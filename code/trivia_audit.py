#!/usr/bin/env python3
"""Flag declarations whose statement may assert nothing (Rule 0 / Rule 18 integrity).

HeightLadder carried four of these undetected: `width_at_rung` was commutativity, `apex_offsets`
was reflexivity. A declaration name is not evidence that content exists, so this looks at
statements.

Three syntactic detectors, all conservative, all producing CANDIDATES for human reading:

  REFL     an equality whose two sides are the same token string          (`X = X`)
  PERM     an equality whose two sides are the same multiset of tokens    (pure rearrangement:
           commutativity/associativity, which `ring` proves and which asserts nothing)
  ECHO     the conclusion is a hypothesis with only `* 1`, `+ 0`, `^ 1` decoration

A flag is not a verdict. `height_eq_twice_area` is a genuine Heron identity also proved by `ring`,
and it is correctly NOT flagged, because its two sides differ as multisets.
"""
import re, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, 'lean', 'Erdos634')

DECL = re.compile(r'^(theorem|lemma)\s+([A-Za-z_][\w\']*)\s*(.*?)(?=^\s*$|\Z)', re.M | re.S)

def toks(s):
    return sorted(t for t in re.findall(r"[A-Za-z_][\w']*|\d+|[+\-*/^()]", s))

def split_stmt(body):
    """return (binders, conclusion) from the text between the name and ':=' """
    head = body.split(':=')[0]
    # conclusion is after the LAST top-level ':' outside parens
    depth, cut = 0, -1
    for i, ch in enumerate(head):
        if ch in '([{': depth += 1
        elif ch in ')]}': depth -= 1
        elif ch == ':' and depth == 0: cut = i
    if cut < 0: return head, ''
    return head[:cut], head[cut+1:]

flags = []
for fn in sorted(os.listdir(LEAN)):
    if not fn.endswith('.lean'): continue
    txt = open(os.path.join(LEAN, fn)).read()
    for m in DECL.finditer(txt):
        name, rest = m.group(2), m.group(3)
        binders, concl = split_stmt(rest)
        c = ' '.join(concl.split())
        if not c or '∀' in c or '∃' in c: continue
        for part in re.split(r'∧', c):
            if part.count('=') != 1 or any(x in part for x in ['≤','<','≠','∣','↔']): continue
            lhs, rhs = part.split('=')
            if not lhs.strip() or not rhs.strip(): continue
            if lhs.split() == rhs.split():
                flags.append((fn, name, 'REFL', part.strip()[:70])); break
            if toks(lhs) == toks(rhs):
                flags.append((fn, name, 'PERM', part.strip()[:70])); break
        else:
            hyps = re.findall(r'\(\s*\w+\s*:\s*([^)]*)\)', binders)
            cc = c.replace('* 1','').replace('+ 0','').replace('^ 1','')
            cc = ' '.join(cc.split())
            for h in hyps:
                if ' '.join(h.split()) == cc and cc != c:
                    flags.append((fn, name, 'ECHO', c[:70])); break

print(f"{len(flags)} candidate content-free declarations\n")
for fn, name, kind, stmt in flags:
    print(f"  {kind:5} {fn[:-5]:24} {name:30} {stmt}")
