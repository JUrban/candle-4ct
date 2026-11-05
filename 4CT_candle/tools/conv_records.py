#!/usr/bin/env python3
"""Convert OCaml record/array code to Candle syntax (for 4CT/geometry.ml).

Usage: conv_records.py FILE TYPE CONSTR   (rewrites FILE in place)
 - type TYPE = { ...; mutable f : T; ... }  ->  type TYPE = | CONSTR of { ...; f : T ref; ...}
 - x.f <- e (mutable f)   ->  x.CONSTR.f := e
 - x.f                    ->  x.CONSTR.f  or (!(x.CONSTR.f)) for mutable f
 - { f = e; ... }         ->  CONSTR { f = e; ... } (mutable values wrapped in ref)
 - { x with f = e; ...}   ->  CONSTR { x with ... }
 - a.(i) <- e             ->  Array.set a i (e)    [e up to ';' or ')' at depth 0]
 - a.(i)                  ->  (Array.get a i)
 - [||]                   ->  (Array.of_list [])
 - Array.init             ->  Cake.Array.tabulate
"""
import re, sys

path, tyname, con = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(path).read()

# --- type declaration
m = re.search(r'type\s+%s\s*=\s*\{(.*?)\}\s*;;' % tyname, s, re.S)
assert m, "type not found"
body = m.group(1)
fields = []
mutable = set()
newfields = []
for part in body.split(';'):
    p = part.strip()
    if not p:
        continue
    mm = re.match(r'(mutable\s+)?(\w+)\s*:\s*(.*)$', p, re.S)
    assert mm, p
    name, ty = mm.group(2), ' '.join(mm.group(3).split())
    fields.append(name)
    if mm.group(1):
        mutable.add(name)
        newfields.append("%s : (%s) ref" % (name, ty))
    else:
        newfields.append("%s : %s" % (name, ty))
newdecl = "type %s = | %s of {\n    %s }" % (tyname, con, ";\n    ".join(newfields))
s = s[:m.start()] + newdecl + ";;" + s[m.end():]
decl_end = m.start() + len(newdecl) + 2
fieldre = '|'.join(sorted(fields, key=len, reverse=True))


def find_close(s, i, open_c='(', close_c=')'):
    """s[i] == open_c; return index of matching close."""
    d = 0
    j = i
    while j < len(s):
        c = s[j]
        if c == open_c:
            d += 1
        elif c == close_c:
            d -= 1
            if d == 0:
                return j
        j += 1
    raise ValueError("unbalanced")


def rhs_extent(s, i):
    """from i, find end of an expression at depth 0: stop at ';' or unmatched ')' or ';;'."""
    d = 0
    j = i
    while j < len(s):
        c = s[j]
        if c in '([{':
            d += 1
        elif c in ')]}':
            if d == 0:
                return j
            d -= 1
        elif c == ';' and d == 0:
            return j
        elif s.startswith(' in ', j) and d == 0:
            return j
        j += 1
    return j


head, tail = s[:decl_end], s[decl_end:]

# --- record constructions: '{ field =' or '{ x with'
out = []
i = 0
while i < len(tail):
    c = tail[i]
    if c == '{':
        mm = re.match(r'\{\s*(\w+\s+with\s+)?(%s)\s*=' % fieldre, tail[i:])
        if mm:
            j = find_close(tail, i, '{', '}')
            inner = tail[i + 1:j]
            # wrap mutable field values in ref (...)
            # split at depth-0 ';'
            parts = []
            d = 0; last = 0
            for k, ch in enumerate(inner):
                if ch in '([{':
                    d += 1
                elif ch in ')]}':
                    d -= 1
                elif ch == ';' and d == 0:
                    parts.append(inner[last:k]); last = k + 1
            parts.append(inner[last:])
            newparts = []
            for pt in parts:
                pm = re.match(r'(\s*(?:\w+\s+with\s+)?)(\w+)(\s*=\s*)(.*)$', pt, re.S)
                if pm and pm.group(2) in mutable:
                    newparts.append(pm.group(1) + pm.group(2) + pm.group(3) +
                                    "ref (" + pm.group(4).strip() + ")")
                else:
                    newparts.append(pt)
            out.append("%s {" % con + ";".join(newparts) + "}")
            i = j + 1
            continue
    out.append(c)
    i += 1
tail = ''.join(out)

# --- mutable field assignment  x.f <- e
tail = re.sub(r'(\b\w+)\.(%s)\s*<-' % fieldre,
              lambda m: "%s.%s.%s :=" % (m.group(1), con, m.group(2)) if m.group(2) in mutable
              else m.group(0), tail)

# --- array assignment a.(i) <- e   (a may be x.f)
def conv_array_sets(t):
    while True:
        m = re.search(r'([\w.]+)\.\(', t)
        found = False
        pos = 0
        while m:
            st = m.start()
            ob = m.end() - 1
            cb = find_close(t, ob)
            after = t[cb + 1:]
            am = re.match(r'\s*<-\s*', after)
            if am:
                arr = m.group(1)
                idx = t[ob + 1:cb]
                rs = cb + 1 + am.end()
                re_ = rhs_extent(t, rs)
                rhs = t[rs:re_].strip()
                t = t[:st] + "Array.set %s (%s) (%s)" % (arr, idx, rhs) + t[re_:]
                found = True
                break
            m = re.compile(r'([\w.]+)\.\(').search(t, cb)
        if not found:
            return t

tail = conv_array_sets(tail)

# --- field reads x.f  (not already converted x.CON.f)
def fread(m):
    x, f = m.group(1), m.group(2)
    if x == con:
        return m.group(0)
    if f in mutable:
        return "(!(%s.%s.%s))" % (x, con, f)
    return "%s.%s.%s" % (x, con, f)

tail = re.sub(r'(?<![.\w])(\w+)\.(%s)\b(?!\s*:=)' % fieldre, fread, tail)

# --- array reads a.(i)
def conv_array_gets(t):
    pat = re.compile(r'((?:\(!\()?[\w.]+(?:\)\))?)\.\(')
    while True:
        m = pat.search(t)
        if not m:
            return t
        ob = m.end() - 1
        cb = find_close(t, ob)
        t = t[:m.start()] + "(Array.get %s (%s))" % (m.group(1), t[ob + 1:cb]) + t[cb + 1:]

tail = conv_array_gets(tail)
tail = tail.replace("[||]", "(Array.of_list [])")
tail = tail.replace("Array.init", "Cake.Array.tabulate")
open(path, "w").write(head + tail)
print("fields:", len(fields), "mutable:", sorted(mutable))
