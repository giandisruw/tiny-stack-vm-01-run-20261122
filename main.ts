// Tiny stack VM for make.fun tiny-stack-vm-01 (ISA.md / generator/subject/vm.mjs).
// Faithful re-implementation of the reference VM: 32-bit wrapping values, 256-slot
// data stack, 64-frame call stack, 256 words of memory, 1,000,000 steps, 65,536
// output bytes, traps 2..11 as exit codes, HALT 0, EXIT v&255. Runs every
// instance in /input/<id>/ and writes /output/<id>/stdout.bin + exit.txt.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode table: [byte, immediate bytes, pops, pushes] — mirrors vm.mjs OPS.
const T = [[0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3], [16, 0, 2, 1], [17, 0, 2, 1],
  [18, 0, 2, 1], [19, 0, 2, 1], [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1],
  [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1], [26, 0, 2, 1], [27, 0, 1, 1],
  [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1], [33, 0, 2, 1],
  [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0],
  [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0],
  [82, 0, 0, 1], [83, 0, 1, 0]];
const imm = new Uint8Array(256), pops = new Uint8Array(256),
  push = new Uint8Array(256), known = new Uint8Array(256);
for (const [o, i, p, q] of T) { imm[o] = i; pops[o] = p; push[o] = q; known[o] = 1; }

// Returns [output buffer, output length, exit code].
function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const end = (code) => [out, olen, code];
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    if (!known[op]) return end(5);
    const im = imm[op];
    if (pc + im >= n) return end(9);
    steps++;
    const po = pops[op];
    if (sp < po) return end(2);
    if (sp - po + push[op] > 256) return end(3);
    const nx = pc + 1 + im;
    pc = nx;
    switch (op) {
      case 0: return end(0);
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break; // POP
      case 4: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 6: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 23: D[sp - 1] = -D[sp - 1] | 0; break; // NEG (wraps at INT_MIN)
      case 27: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        switch (op) {
          case 16: r = (a + b) | 0; break; // ADD wraps
          case 17: r = (a - b) | 0; break; // SUB wraps
          case 18: r = Math.imul(a, b); break; // MUL low 32 bits, exact
          case 19: // DIV, truncates toward zero; INT_MIN / -1 is INT_MIN
            if (!b) return end(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 20: // MOD, sign of a; x % -1 is 0
            if (!b) return end(4);
            r = b === -1 ? 0 : (a % b) | 0; break;
          case 21: // DIVU, unsigned quotient read back signed
            if (!b) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 22: // MODU, unsigned remainder read back signed
            if (!b) return end(4);
            r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break; // SHL, only low 5 bits of count
          case 29: r = a >> (b & 31); break; // SHR arithmetic
          case 30: r = (a >>> (b & 31)) | 0; break; // SHRU logical
          case 32: r = a === b ? 1 : 0; break; // EQ
          case 33: r = a < b ? 1 : 0; break; // LT signed
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU (34)
        }
        sp -= 2; D[sp++] = r; break;
      }
      case 48: case 49: case 50: { // JMP / JZ / JNZ, signed rel from next instr
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51: // CALL, unsigned absolute target
        if (csp === 64) return end(7);
        C[csp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52: // RET
        if (!csp) return end(8);
        pc = C[--csp];
        break;
      case 64: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: { // STORE ( v addr -- )
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a >= 256) return end(6);
        sp -= 2; M[a] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII, no newline
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC: one byte, v & 255
        if (olen + 1 > 65536) return end(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN, -1 at end
      default: return end(D[--sp] & 255); // EXIT (83)
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [out, olen, code] = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out.subarray(0, olen));
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
