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
classes, SIMD&FP single-register, pair and literal loads and stores,
AdvSIMD modified-immediate moves, and selected AdvSIMD, CRC-32, CRC-32C,
polynomial multiply and AES instructions. The model gates optional instruction
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
  arm64NativeCasesTheory arm64NativeTheory arm64L3Theory arm64HolTheory
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

To reproduce the hardware observations, run on AArch64 with CRC32, PMULL
and AES support. The generator requires GCC, GNU binutils, Python 3, and
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
python3 tools/a64_coverage.py --json coverage.json
```

Released under the [BSD 3-Clause License](LICENSE).
