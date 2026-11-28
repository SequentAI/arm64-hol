#!/usr/bin/env bash
# Regenerate asl-equiv/model from sail-arm's arm-v9.4-a specification.
#
# Needs Sail 0.17.1 and Lem 2022-12-10 on PATH (an opam switch), and a
# checkout of rems-project/sail-arm at f7e11ae, the revision its Isabelle
# snapshot of Armv9.4-A was made from. Newer Sail fails on this model.
#
# usage: generate.sh <sail-arm checkout> <work directory>
#
# Steps:
#  1. sail -lem on the A64 sources only (no A32, SVE, SME or devices), with
#     flat identity memory (sail/flat_memory.*) and UNKNOWN as HOL's ARB
#     (sail/undefined_override.lem).
#  2. Split Sail's one Lem module into parts Lem can process: Lem keeps
#     about 1.2 GB per 20k lines, and the module has 650k.
#  3. lem -hol each part against declaration-only stand-ins of the others,
#     twice: the first pass finds the names Lem gives each constant in HOL,
#     the second uses them in the stand-ins.
#  4. Adapt the output to the pinned HOL and give ConstrainUnpredictable
#     Arm's choices (fix-hol.sh), open in each part only the parts it uses
#     (split/trim_opens.py), and copy it to model/.
set -euo pipefail
spec=$(realpath "$1"); work=$(realpath -m "$2"); here=$(dirname "$(realpath "$0")")
share=$(dirname "$(dirname "$(command -v sail)")")/share/sail
model=$here/../model
libs=(-lib "$here/lem-lib" -lib "$share/lib/hol" -lib "$share/src/gen_lib")

# 1. Sail to Lem
rm -rf "$work"; mkdir -p "$work"; cp -r "$spec/arm-v9.4-a/src" "$work/src"
cd "$work"
patch -p1 < "$here/sail/flat_memory.patch"
mkdir -p lem isabelle
cp src/lem-patches/prelude.lem lem/
# The patch declares no HOL type for this size.
sed -i '/declare isabelle target_rep type ty86528/a declare hol target_rep type ty86528 = `86528`' lem/prelude.lem
splices=()
for s in src/lem-patches/*.sail "$here/sail/flat_memory.sail"; do splices+=(-splice "$s"); done
srcs=(prelude decode_start builtins v8_base sysregs_autogen sysregs instrs64 interrupts
      reset fetch interface no_devices impdefs mem decode_end map_clauses event_clauses stubs)
sail -memo_z3 -grouped_regstate -lem -lem_output_dir lem -isa_output_dir isabelle -o armv9 \
  -lem_lib Prelude -lem_lib Undefined_override -lem_mwords -mono_rewrites -auto_mono -undefined_gen \
  "${splices[@]}" $(for s in "${srcs[@]}"; do echo "src/$s.sail"; done)
sed -i '/open import Sail2_monadic_combinators/a open import Prelude' lem/armv9_types.lem
cp "$here/sail/undefined_override.lem" lem/

# 2. Split
python3 "$here/split/move_vals.py" lem/armv9.lem moved.lem
python3 "$here/split/cuts.py" moved.lem 20000 > cuts.txt
mkdir -p parts; cp lem/{prelude,undefined_override,armv9_types}.lem parts/
python3 "$here/split/split_lem.py" moved.lem parts cuts.txt
n=$(ls parts/armv9_p*.lem | wc -l)

# 3. Lem to HOL, one part at a time
gen_part() {  # <part number> <stand-in directory> <output directory>
  local d=$work/run/p$1
  rm -rf "$d"; mkdir -p "$d" "$3"
  cp parts/{prelude,undefined_override,armv9_types}.lem "parts/armv9_p$1.lem" "$d"/
  (cd "$d" && lem -hol -outdir "$3" -auxiliary_level none -lib "$d" -lib "$2" "${libs[@]}" "armv9_p$1.lem")
}
python3 "$here/split/stubs.py" parts stubs1
for k in $(seq 1 "$n"); do gen_part "$k" "$work/stubs1" "$work/hol1"; done
python3 "$here/split/hol_names.py" parts hol1 names.json
python3 "$here/split/stubs.py" parts stubs2 names.json
for k in $(seq 1 "$n"); do gen_part "$k" "$work/stubs2" "$work/hol"; done
python3 "$here/split/hol_names.py" parts hol names2.json
cmp names.json names2.json
(cd parts && lem -hol -outdir "$work/hol" -auxiliary_level none "${libs[@]}" \
   prelude.lem undefined_override.lem armv9_types.lem)

# The HOL stand-in for Sail 0.17's concurrency-interface monad (lem-lib/)
(cd "$here/lem-lib" && lem -hol -outdir "$work/hol-lib" -auxiliary_level none \
   -lib . -lib "$share/lib/hol" -lib "$share/src/gen_lib" *.lem)

# 4. Adapt and install, replacing the previous export
rm -f "$model"/*Script.sml
cp hol/*Script.sml "$model/"
cp hol-lib/*Script.sml "$here/../lib/sail/"
bash "$here/fix-hol.sh" "$model"/*Script.sml "$here"/../lib/sail/sail2_{concurrency_interface,monadic_combinators,undefined_concurrency_interface}Script.sml
python3 "$here/split/trim_opens.py" "$model"
sed -i '/^val _ = new_theory "armv9_/a val _ = HOLFlags.set_trace "TheoryPP.include_html_docs" 0;' "$model"/armv9_*Script.sml
