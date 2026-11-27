"""Find safe module cut points in Sail's armv9.lem.

Two things tie definitions to a Lem module: a `val` and its `let` must be in
the same module (Sail often declares far ahead), and a `let` with no `val`
anywhere gets its class constraints resolved by later uses in the same
module. A `val` line is a safe cut when no declaration above it is defined
below it, and no `val`-less function above it is referenced below it.
Prints how many safe cuts there are and then, with a minimum spacing, the
cuts to use.
"""
import re, sys
lines = open(sys.argv[1]).read().split('\n')
spacing = int(sys.argv[2])
ident = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
val_at, let_at = {}, {}
for i, l in enumerate(lines):
    if l.startswith('val '):
        val_at.setdefault(ident.findall(l)[1], i)
    elif l.startswith('let ') and not l.startswith('let ('):
        let_at.setdefault(ident.findall(l)[1], i)
spans = [(val_at[n], let_at[n]) for n in val_at if n in let_at and let_at[n] > val_at[n]]
valless = {n: d for n, d in let_at.items() if n not in val_at}
last_ref = dict(valless)
for i, l in enumerate(lines):
    for w in ident.findall(l):
        if w in last_ref and i > last_ref[w]:
            last_ref[w] = i
spans += [(d, last_ref[n]) for n, d in valless.items()]
spans.sort()
safe, reach, j = [], -1, 0
for i, l in enumerate(lines):
    while j < len(spans) and spans[j][0] < i:
        reach = max(reach, spans[j][1]); j += 1
    if l.startswith('val ') and reach < i:
        safe.append(i)
print(len(valless), 'val-less functions;', len(safe), 'safe cuts', file=sys.stderr)
prev = 0
for s in safe:
    if s - prev >= spacing:
        print(s); prev = s
