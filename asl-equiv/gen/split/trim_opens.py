"""Open in each HOL part armv9_p<k>Script.sml only the earlier parts whose
constants it names, so that holbuild can build independent parts at once.

The last part keeps every earlier one: it is the model's single root.
usage: trim_opens.py <model directory>
"""
import re, sys, pathlib

model = pathlib.Path(sys.argv[1])
parts = sorted(model.glob('armv9_p*Script.sml'),
               key=lambda p: int(re.search(r'armv9_p(\d+)Script', p.name).group(1)))
n = len(parts)
texts = [p.read_text() for p in parts]
defined = [set(re.findall(r"^\s*\(\(([A-Za-z_][A-Za-z0-9_']*):", t, re.M)) for t in texts]
ident = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
for k in range(n - 1):
    tokens = set(ident.findall(texts[k]))
    used = {j for j in range(k) if defined[j] & tokens}
    def keep(m):
        return m.group(0) if int(m.group(1)) - 1 in used else ''
    head, sep, rest = texts[k].partition('\nval _ = numLib.prefer_num();')
    head = re.sub(r' armv9_p(\d+)Theory', keep, head)
    parts[k].write_text(head + sep + rest)
    print(parts[k].name, 'opens', sorted(j + 1 for j in used))
