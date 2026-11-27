"""Write val-only stand-ins for split parts, so Lem can check one part
without loading the definitions of every part before it.

A stand-in keeps each part's opens and `val` lines, turns each annotated
constant `let (X : t) = ...` into `val X : t`, and maps each name to the HOL
constant that the part's own theory defines for it (names map from hol_names.py, else the same name).
"""
import json, re, sys, pathlib
src, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
# optional lem name -> HOL name map from hol_names.py (Lem renames, e.g. drops leading underscores)
hol = json.load(open(sys.argv[3])) if len(sys.argv) > 3 else {}
out.mkdir(exist_ok=True)
const = re.compile(r"let \(([A-Za-z_][A-Za-z0-9_']*) : (.*)\) = ")
for p in sorted(src.glob('armv9_p*.lem')):
    keep = []
    for l in p.read_text().split('\n'):
        if l.startswith('open import'):
            keep.append(l)
        elif l.startswith('val '):
            keep.append(l)
            name = l.split()[1]
            keep.append(f'declare hol target_rep function {name} = `{hol.get(name, name)}`')
        elif l.startswith('let ('):
            m = const.match(l)
            if not m:
                sys.exit(f'{p.name}: unparsed constant {l[:80]}')
            keep.append(f'val {m.group(1)} : {m.group(2)}')
            keep.append(f'declare hol target_rep function {m.group(1)} = `{hol.get(m.group(1), m.group(1))}`')
    (out / p.name).write_text('\n\n'.join(keep) + '\n')
