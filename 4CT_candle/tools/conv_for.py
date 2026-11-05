#!/usr/bin/env python3
"""Rewrite OCaml 'for v = a to b do BODY done' into 'for_loop (a) (b) (fun v -> (BODY))'."""
import re, sys
path = sys.argv[1]
s = open(path).read()
out = []; i = 0; depth = []
tok = re.compile(r'\bfor\s+(\w+)\s*=\s*(.*?)\s+to\s+(.*?)\s+do\b|\bdone\b', re.S)
while True:
    m = tok.search(s, i)
    if not m:
        out.append(s[i:]); break
    out.append(s[i:m.start()])
    if m.group(0).startswith('for'):
        out.append("for_loop (%s) (%s) (fun %s -> (" % (m.group(2), m.group(3), m.group(1)))
        depth.append(1)
    else:
        assert depth, "unbalanced done at %d" % m.start()
        depth.pop(); out.append("))")
    i = m.end()
assert not depth
open(path, "w").write(''.join(out))
