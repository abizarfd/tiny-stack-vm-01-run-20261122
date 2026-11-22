// Tiny stack VM: runs each <input>/<id>/program.bin on its input.bin and
// writes <output>/<id>/stdout.bin + exit.txt. 32-bit wrapping stack machine
// per the kit ISA.md (vm.mjs settles ambiguities). Deterministic.
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Opcode tables by opcode byte: immediate length, pops, pushes, known.
const IMM = new Uint8Array(256);
const POPS = new Uint8Array(256);
const PUSH = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
for (const [o, i, p, q] of [ // [opcode, imm, pops, pushes]
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0],
  [4, 0, 1, 2], [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3],
  [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0],
  [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0],
  [81, 0, 1, 0], [82, 0, 0, 1], [83, 0, 1, 0],
]) { IMM[o] = i; POPS[o] = p; PUSH[o] = q; KNOWN[o] = 1; }
// The 0x10-0x22 binary/unary ALU ops are all (0, 2, 1) except NEG/NOT (0, 1, 1).
for (let o = 0x10; o < 0x23; o++) { POPS[o] = 2; PUSH[o] = 1; KNOWN[o] = 1; }
POPS[0x17] = 1; POPS[0x1b] = 1; KNOWN[0x1f] = 0;

// Runs one program to halt / exit / trap. Returns bytes written (valid in
// `out` up to `len`) and the exit code.
function run(prog: Buffer, input: Buffer): { out: Uint8Array; len: number; exit: number } {
  const n = prog.length;
  const S = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, steps = 0;
  const dig = new Uint8Array(11);
  const done = (exit: number) => ({ out, len: ol, exit });

  for (;;) {
    // ISA check order: step limit, pc range, opcode, immediate fit,
    // then step count and stack checks.
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    if (!KNOWN[op]) return done(5);
    const imm = IMM[op];
    if (pc + imm >= n) return done(9);
    steps++;
    const nx = pc + 1 + imm;
    if (sp < POPS[op]) return done(2);
    if (sp - POPS[op] + PUSH[op] > 256) return done(3);
    pc = nx;

    switch (op) {
      case 0x00: return done(0);
      case 0x01: S[sp++] = (prog[nx - 1] << 24) >> 24; break;
      case 0x02: S[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: S[sp] = S[sp - 1]; sp++; break;
      case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; }
      case 0x06: S[sp] = S[sp - 2]; sp++; break;
      case 0x07: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; }
      case 0x17: S[sp - 1] = (-S[sp - 1]) | 0; break;
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = S[sp - 1], a = S[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return done(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14:
            if (b === 0) return done(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15:
            if (b === 0) return done(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return done(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        S[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = S[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return done(7);
        C[cp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const addr = S[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        S[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = S[sp - 1], v = S[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const v = S[sp - 1];
        let u = v < 0 ? -v : v, d = 0;
        do { dig[d++] = 48 + (u % 10); u = (u / 10) | 0; } while (u > 0);
        const total = d + (v < 0 ? 1 : 0);
        if (ol + total > 65536) return done(11);
        sp--;
        if (v < 0) out[ol++] = 45;
        while (d > 0) out[ol++] = dig[--d];
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return done(11);
        out[ol++] = S[--sp] & 255;
        break;
      case 0x52:
        S[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      default:
        return done(S[--sp] & 255);
    }
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const d = join(IN_DIR, id);
  if (!existsSync(join(d, 'program.bin'))) continue;
  const input = existsSync(join(d, 'input.bin')) ? readFileSync(join(d, 'input.bin')) : Buffer.alloc(0);
  const r = run(readFileSync(join(d, 'program.bin')), input);
  const od = join(OUT_DIR, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), r.out.subarray(0, r.len));
  writeFileSync(join(od, 'exit.txt'), r.exit + '\n');
}
