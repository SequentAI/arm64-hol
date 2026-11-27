# Equivalence with Arm's Armv9.4-A specification

This optional package relates `arm64-hol` to Arm's own Armv9.4-A
specification, exported to HOL4 from the Sail translation of Arm's ASL in
[rems-project/sail-arm](https://github.com/rems-project/sail-arm)
(`arm-v9.4-a`, revision `f7e11ae`). It is not built by default: name its
theories to build them, e.g. `holbuild build armv9_p32Theory`.

- `model/` is the generated specification: the A64 instruction set without
  A32, SVE, SME or devices, with flat identity memory (no address
  translation) and each UNKNOWN value a fixed unspecified value (HOL's
  `ARB`), and `ConstrainUnpredictable` making the choices of Arm's
  Armv9.3-A specification. It is split into the theories `armv9_p1` to
  `armv9_p32`; each opens only the earlier parts it uses, so independent
  parts build in parallel.
- `lib/` holds the Lem and Sail support libraries the model needs.
- `gen/generate.sh` regenerates `model/`; its header says how.

## Licences

`model/` is derived from Arm's specification and is under the
BSD-3-Clause-Clear licence in `model/LICENSE`. `lib/lem` and `lib/sail` are
under the Lem and Sail licences in their directories. The rest of this
package is under the repository's licence.
