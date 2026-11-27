#!/usr/bin/env bash
# Adapt Lem's HOL4 output to the HOL4 revision this project pins, and give
# the specification's stubbed ConstrainUnpredictable Arm's choices.
set -euo pipefail
# sail-arm's arm-v9.4-a stubs ConstrainUnpredictable as UNKNOWN (stubs.sail);
# constrain_unpredictable.hol is the choice table of arm-v9.3-a's
# v8_base.sail, the Arm pseudocode's, with UNKNOWN for every other case.
export CU_DEF=$(dirname "$(realpath "$0")")/constrain_unpredictable.hol
for f in "$@"; do
  perl -i -pe '
    BEGIN { local $/; open my $h, "<", $ENV{CU_DEF} or die; $cu = <$h>; chomp $cu }
    # computeLib.auto_import_definitions is a HOLFlags.bflag, not a ref.
    s/Lib\.with_flag \(computeLib\.auto_import_definitions, false\)/HOLFlags.with_bflags [(computeLib.auto_import_definitions, false)]/g;
    # relationTheory.tc was renamed transitive_closure.
    s/\(tc \(/(transitive_closure (/g; s/\(tc r\)/(transitive_closure r)/g;
    # whileTheory was renamed WhileTheory.
    s/\bwhileTheory\./WhileTheory./g;
    s/^ \(\(ConstrainUnpredictable:Unpredictable ->.* which=  \(UNKNOWN_Constraint \(\) \)\)`;$/$cu/;
  ' "$f"
done
