"""Move each forward `val` in Sail's armv9.lem down to just before its first
use or its `let`, whichever comes first.

Sail declares most functions far ahead of their definitions; a Lem module
must hold both, so the gap would block every module cut in between. Moving a
declaration down past lines that never mention the name changes nothing.
Top-level items are separated by blank lines; a `val` item is one line.
"""
import re, sys
blocks = open(sys.argv[1]).read().split('\n\n')
ident = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
name_of = lambda b: ident.findall(b.strip('\n'))[1]
is_val = lambda b: b.strip('\n').startswith('val ')
pending = {}  # name -> val block, waiting for first use or definition
out, moved = [], 0
for b in blocks:
    if is_val(b) and '\n' not in b.strip('\n'):
        pending[name_of(b)] = b
        continue
    words = set(ident.findall(b))
    for n in [n for n in pending if n in words]:
        out.append(pending.pop(n))
        moved += 1
    out.append(b)
out += pending.values()
open(sys.argv[2], 'w').write('\n\n'.join(out))
print('placed', moved, 'vals;', len(pending), 'never used or defined', file=sys.stderr)
