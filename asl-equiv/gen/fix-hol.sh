#!/usr/bin/env bash
# Adapt Lem's HOL4 output to the HOL4 revision this project pins.
set -euo pipefail
for f in "$@"; do
  perl -i -pe '
    # computeLib.auto_import_definitions is a HOLFlags.bflag, not a ref.
    s/Lib\.with_flag \(computeLib\.auto_import_definitions, false\)/HOLFlags.with_bflags [(computeLib.auto_import_definitions, false)]/g;
    # relationTheory.tc was renamed transitive_closure.
    s/\(tc \(/(transitive_closure (/g; s/\(tc r\)/(transitive_closure r)/g;
    # whileTheory was renamed WhileTheory.
    s/\bwhileTheory\./WhileTheory./g;
  ' "$f"
done
