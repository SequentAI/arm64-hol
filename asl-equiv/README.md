# Equivalence with Arm's Armv9.4-A specification

This optional package relates `arm64-hol` to Arm's own Armv9.4-A
specification, exported to HOL4 from the Sail translation of Arm's ASL in
[rems-project/sail-arm](https://github.com/rems-project/sail-arm)
(`arm-v9.4-a`, revision `f7e11ae`). Neither the default build nor CI
builds it: the model takes about 7 hours to build from scratch. Build and
check it by naming its theories:

```bash
holbuild build aslSimTheory aslNonVacuityTheory aslDecodeNonVacuityTheory armv9_p32Theory
holbuild check armv9_typesTheory armv9_p{1..32}Theory arm64AslTheory aslLemmasTheory \
  aslSimTheory aslNonVacuityTheory aslDecodeNonVacuityTheory
```

- `model/` is the generated specification: the A64 instruction set without
  A32, SVE, SME or devices, with flat identity memory (no address
  translation) and each UNKNOWN value a fixed unspecified value (HOL's
  `ARB`), and `ConstrainUnpredictable` making the choices of Arm's
  Armv9.3-A specification. It is split into the theories `armv9_p1` to
  `armv9_p32`; each opens only the earlier parts it uses, so independent
  parts build in parallel.
- `lib/` holds the Lem and Sail support libraries the model needs.
- `gen/generate.sh` regenerates `model/`; its header says how.
- `proofs/` relates the two. `arm64Asl` defines the state relation, the
  system configuration `arm64-hol` assumes, the specification's step, and
  `asl_complete`, the statement that the specification simulates every
  instruction `arm64-hol` decodes. `aslSim` proves the simulation so far:
  NOP, ADD/SUB (immediate), FMOV (general to vector), and 64-bit LDR and
  STR (immediate, unsigned offset) at any address. `aslNonVacuity` and
  `aslDecodeNonVacuity` show that the hypotheses hold for some states.

`lib/` is Lem's and Sail's HOL4 output as they ship it. Lem leaves 34 of
its recursive functions without termination proofs, so their equations
(`_def`) and induction theorems (`_ind`) carry the termination conditions
as hypotheses, and `holbuild check` reports them. About 24 of them recurse
on a list or a number (`foreachM`, `repeat`, …) and could be proved to
terminate; the others are loops that need not terminate (`whileM`,
`untilM`, …). No theorem in `model/` or `proofs/` depends on them; a proof
that evaluates one discharges its conditions where it uses it.

## Licences

`model/` is derived from Arm's specification and is under the
BSD-3-Clause-Clear licence in `model/LICENSE`. `lib/lem` and `lib/sail` are
under the Lem and Sail licences in their directories. The rest of this
package is under the repository's licence.
