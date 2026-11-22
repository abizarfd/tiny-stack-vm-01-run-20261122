// Tiny stack VM entry point.
//
// For every program id in the input directory this runs
//   <input>/<id>/program.bin  on  <input>/<id>/input.bin
// and writes
//   <output>/<id>/stdout.bin  and  <output>/<id>/exit.txt
// The machine is the 32-bit wrapping stack VM of the kit's ISA.md
// (program/generator/subject/ISA.md); the reference VM vm.mjs beside it
// settles any ambiguity. Everything here is deterministic: no clock,
// no environment reads beyond the two directory overrides below.
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const STEP_LIMIT = 1_000_000;
const OUTPUT_MAX = 65_536;
const STACK_MAX = 256;
const CALLS_MAX = 64;

// Per-opcode tables, indexed by opcode byte: immediate length, values
// popped, values pushed, and whether the byte is a known opcode at all.
const IMM = new Uint8Array(256);
const POPS = new Uint8Array(256);
const PUSHES = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
function def(op: number, imm: number, pops: number, pushes: number): void {
  IMM[op] = imm; POPS[op] = pops; PUSHES[op] = pushes; KNOWN[op] = 1;
}
def(0x00, 0, 0, 0); // HALT
def(0x01, 1, 0, 1); // PUSH8
def(0x02, 4, 0, 1); // PUSH32
def(0x03, 0, 1, 0); // POP
def(0x04, 0, 1, 2); // DUP
def(0x05, 0, 2, 2); // SWAP
def(0x06, 0, 2, 3); // OVER
def(0x07, 0, 3, 3); // ROT
def(0x10, 0, 2, 1); // ADD
def(0x11, 0, 2, 1); // SUB
def(0x12, 0, 2, 1); // MUL
def(0x13, 0, 2, 1); // DIV
def(0x14, 0, 2, 1); // MOD
def(0x15, 0, 2, 1); // DIVU
def(0x16, 0, 2, 1); // MODU
def(0x17, 0, 1, 1); // NEG
def(0x18, 0, 2, 1); // AND
def(0x19, 0, 2, 1); // OR
def(0x1a, 0, 2, 1); // XOR
def(0x1b, 0, 1, 1); // NOT
def(0x1c, 0, 2, 1); // SHL
def(0x1d, 0, 2, 1); // SHR
def(0x1e, 0, 2, 1); // SHRU
def(0x20, 0, 2, 1); // EQ
def(0x21, 0, 2, 1); // LT
def(0x22, 0, 2, 1); // LTU
def(0x30, 2, 0, 0); // JMP
def(0x31, 2, 1, 0); // JZ
def(0x32, 2, 1, 0); // JNZ
def(0x33, 2, 0, 0); // CALL
def(0x34, 0, 0, 0); // RET
def(0x40, 0, 1, 1); // LOAD
def(0x41, 0, 2, 0); // STORE
def(0x50, 0, 1, 0); // PRINT
def(0x51, 0, 1, 0); // PUTC
def(0x52, 0, 0, 1); // IN
def(0x53, 0, 1, 0); // EXIT

// Runs one program to its halt / exit / trap. Returns the bytes it wrote
// (a view into a full-size buffer, valid up to `len`) and its exit code.
function runProgram(prog: Buffer, input: Buffer): { out: Uint8Array; len: number; exit: number } {
  const n = prog.length;
  const st = new Int32Array(STACK_MAX);
  let sp = 0;
  const cs = new Int32Array(CALLS_MAX);
  let cp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(OUTPUT_MAX);
  let ol = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const dig = new Uint8Array(11); // scratch for PRINT's decimal digits
  const finish = (exit: number) => ({ out, len: ol, exit });

  for (;;) {
    // Checks in ISA order: step limit, pc range, opcode, immediate fit,
    // then the step counts and the stack checks.
    if (steps === STEP_LIMIT) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    if (!KNOWN[op]) return finish(5);
    const imm = IMM[op];
    if (pc + imm >= n) return finish(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < POPS[op]) return finish(2);
    if (sp - POPS[op] + PUSHES[op] > STACK_MAX) return finish(3);
    pc = next;

    switch (op) {
      case 0x00: return finish(0); // HALT
      case 0x01: // PUSH8, sign-extended
        st[sp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian
        st[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: st[sp] = st[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; } // SWAP
      case 0x06: st[sp] = st[sp - 2]; sp++; break; // OVER
      case 0x07: { // ROT: (a b c -- b c a)
        const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a;
        break;
      }
      case 0x17: st[sp - 1] = (-st[sp - 1]) | 0; break; // NEG, wraps at INT_MIN
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1];
        const a = st[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break; // ADD wraps
          case 0x11: r = (a - b) | 0; break; // SUB wraps
          case 0x12: r = Math.imul(a, b); break; // MUL, low 32 bits of exact product
          case 0x13: // DIV, truncated toward zero; INT_MIN / -1 stays INT_MIN
            if (b === 0) return finish(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14: // MOD, sign follows a; x % -1 is 0
            if (b === 0) return finish(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15: // DIVU, operands read unsigned
            if (b === 0) return finish(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16: // MODU, operands read unsigned
            if (b === 0) return finish(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // SHL, low 5 bits of count
          case 0x1d: r = a >> (b & 31); break; // SHR, arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // SHRU, logical
          case 0x20: r = a === b ? 1 : 0; break; // EQ
          case 0x21: r = a < b ? 1 : 0; break; // LT, signed
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU, unsigned
        }
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset from next
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = st[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit target; 64 held returns is full
        if (cp === CALLS_MAX) return finish(7);
        cs[cp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return finish(8);
        pc = cs[--cp];
        break;
      case 0x40: { // LOAD
        const addr = st[sp - 1];
        if (addr < 0 || addr >= 256) return finish(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE: (v addr --), addr is on top
        const addr = st[sp - 1];
        const v = st[sp - 2];
        if (addr < 0 || addr >= 256) return finish(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline; over-limit writes nothing
        const v = st[sp - 1];
        let u = v < 0 ? -v : v;
        let d = 0;
        do { dig[d++] = 48 + (u % 10); u = (u / 10) | 0; } while (u > 0);
        const total = d + (v < 0 ? 1 : 0);
        if (ol + total > OUTPUT_MAX) return finish(11);
        sp--;
        if (v < 0) out[ol++] = 45;
        while (d > 0) out[ol++] = dig[--d];
        break;
      }
      case 0x51: // PUTC: low byte only
        if (ol + 1 > OUTPUT_MAX) return finish(11);
        out[ol++] = st[--sp] & 255;
        break;
      case 0x52: // IN: -1 forever once the input is used up
        st[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      default: // 0x53 EXIT: low byte of the popped value
        return finish(st[--sp] & 255);
    }
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const dir = join(IN_DIR, id);
  const progPath = join(dir, 'program.bin');
  if (!existsSync(progPath)) continue;
  const prog = readFileSync(progPath);
  const inputPath = join(dir, 'input.bin');
  const input = existsSync(inputPath) ? readFileSync(inputPath) : Buffer.alloc(0);
  const r = runProgram(prog, input);
  const od = join(OUT_DIR, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), r.out.subarray(0, r.len));
  writeFileSync(join(od, 'exit.txt'), String(r.exit) + '\n');
}
