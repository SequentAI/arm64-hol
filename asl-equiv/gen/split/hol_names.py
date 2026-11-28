"""Map each top-level Lem name of the split parts to the HOL constant Lem
generated for it, by pairing the part's `let`s with its Script's `Define`s in
order. Writes the map as JSON (lem name -> HOL name) to argv[3].
"""
import json, re, sys, pathlib
lemdir, holdir, out = map(pathlib.Path, sys.argv[1:4])
ident = r"[A-Za-z_][A-Za-z0-9_']*"
names, renamed = {}, 0
for p in sorted(lemdir.glob('armv9_p*.lem')):
    lets = [re.match(rf"let \(?({ident})", l).group(1)
            for l in p.read_text().split('\n') if l.startswith('let ')]
    script = (holdir / (p.stem + 'Script.sml')).read_text()
    defs = re.findall(rf"Define `\s*\(*({ident})\s*:", script)
    if len(lets) != len(defs):
        sys.exit(f'{p.name}: {len(lets)} lets but {len(defs)} Defines')
    for a, b in zip(lets, defs):
        names[a] = b
        renamed += a != b
json.dump(names, open(out, 'w'), indent=0)
print(len(names), 'names,', renamed, 'renamed', file=sys.stderr)
