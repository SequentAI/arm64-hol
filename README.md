# arm64-hol

Executable HOL4 semantics for a subset of the little-endian A64
instruction set at EL0, based on the
[Arm Architecture Reference Manual](https://developer.arm.com/documentation/ddi0487/)
and the [A64 instruction descriptions](https://developer.arm.com/documentation/ddi0602/).
The model uses byte-addressed memory with per-byte permissions and omits
address translation.

`isa/` defines instruction decoding and encoding, the machine state, and
one-instruction execution. It covers the base A64 integer and branch
instructions other than pointer authentication, all general-register
loads, stores and prefetches outside the atomic, exclusive and ordered
classes, SIMD&FP single-register, pair, literal and structure (`LD1`–`LD4`,
`ST1`–`ST4`, single-lane and replicate) loads and stores, AdvSIMD
modified-immediate moves, the AES, SHA-1, SHA-256, SHA-512, SHA-3, SM3 and
SM4 instructions, and selected AdvSIMD, CRC-32, CRC-32C and polynomial
multiply instructions. The model gates optional instruction
families by feature and faults on unsupported encodings. Fetches require
readable, executable, non-writable bytes. Stores require readable,
writable, non-executable bytes. SP-based transfers also require 16-byte
stack alignment.

`step_cv` uses finite sparse maps for executable evaluation. HOL4 proves
that it refines the function-valued `step` and that any successfully decoded
instruction encodes to the original word.

## Build and check

With Poly/ML and holbuild on PATH:

```sh
holbuild buildhol
holbuild -j4 build arm64HolTheory
holbuild check arm64CryptoTheory arm64IsaTheory arm64IsaCvTheory \
  arm64CryptoVectorsTheory arm64NativeCasesTheory arm64NativeTheory \
  arm64L3Theory arm64HolTheory
```

## Conformance

- The AArch64 harness runs instruction probes and records the resulting
  registers, flags, PC, and memory. It checks that a read-only page
  produces `SEGV_ACCERR` on stores and instruction fetches.
- The generator checks the probe disassembly with GNU and LLVM tools.
  `arm64Native` checks the decodes, encodings and hardware observations
  with `cv_eval`. Model-only cases cover permissions, alignment, feature
  gates and unsupported encodings.
- `arm64L3` compares selected integer and CRC cases with HOL4's independent
  L3 `arm8` model. Separate assertions record the pinned L3 decoder's
  zero-input `CLZ` discrepancy observed against native behavior.
- `arm64Crypto` proves equivalence of the modeled AES round operations
  with the corresponding components of HOL4's AES reference implementation.
- `arm64CryptoVectors` computes the GB/T 32907 SM4 and GB/T 32905 SM3
  examples by stepping assembled SM4 and SM3 instructions, which the native
  hosts cannot execute.

To reproduce the hardware observations, run on AArch64 with CRC32, PMULL,
AES, SHA-1, SHA-256, SHA-512 and SHA-3 support. The generator requires GCC, GNU binutils, Python 3, and
rustup's `llvm-tools` component.

```sh
rustup component add llvm-tools
python3 tests/generate_native.py --check
```

## Coverage

`tools/a64_coverage.py` measures the decoder against every A64 encoding
clause of Arm's Armv9.4-A Sail model
([rems-project/sail-arm](https://github.com/rems-project/sail-arm)). It
samples each clause, classifies the samples with the Sail decoder, decodes
them in HOL4, and reports, per instruction area, the clauses the model
covers and any word it accepts that Sail rejects.

```sh
python3 tools/a64_coverage.py --json a64-coverage.json
```

The JSON gives each clause's mask, opcode and decode status, including
partial and missing clauses. `encode_of_decode` guarantees round-trip for
every successful decode. The report attaches checked state-update
observations, instruction fault theorems and L3 comparisons to clauses by
instruction word. Empty evidence lists indicate that the report has no
matching check for that clause. These observations cover individual
states, and `step_cv_refines` relates the executable evaluator to the
HOL model for all states.

CI samples the two extremes of each clause's operand fields and runs the
ADD regression test. The test probes both widths of each ADD form, with the
flag-setting and subtract variants, immediate shifts, register shifts and
extensions. It rebuilds the decoder in a temporary ISA-only checkout
with 32-bit ADD immediate disabled and checks that precisely that row
loses coverage.

```sh
python3 tools/a64_coverage.py --samples 0 --json a64-coverage.json --accept-add
```

Released under the [BSD 3-Clause License](LICENSE).
