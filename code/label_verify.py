#!/usr/bin/env python3
"""Upgrade PROVED -> VERIFIED only where the claim is checkable.

Rule 0's VERIFIED means: formalized in Lean4, `lake build` clean, zero `sorry`, axioms checked.  The
corpus satisfies the global half (147 modules, 0 sorry, 8622 jobs).  What is per-statement is
whether the paper's statement is the one that was formalized.  Two conditions, both mechanical:

  (a) the surrounding text claims formalization OF THIS STATEMENT -- "machine-checked",
      "kernel-checked", "formalised as", "axiom-clean", "axiom-free";
  (b) at least one Lean declaration name it cites actually EXISTS in lean/Erdos634.

A citation of a whole file, or of a component ("the arithmetic components are kernel-checked"),
fails (b) or is caught by hand.  Anything not meeting both stays PROVED, which under-claims.
"""
import re, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, 'lean', 'Erdos634')
ENVS = ('theorem', 'proposition', 'lemma', 'corollary', 'conjecture', 'hypothesis')
PAPERS = ['paper/erdos-634.tex', 'paper/erdos-634-companion.tex', 'paper/erdos-634-obstructions.tex']

decls = set()
for fn in os.listdir(LEAN):
    if fn.endswith('.lean'):
        for m in re.finditer(r'^(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_\']*)',
                             open(os.path.join(LEAN, fn)).read(), re.M):
            decls.add(m.group(1))
print(f"{len(decls)} Lean declarations in the corpus")

CLAIM = re.compile(r'machine-checked|kernel-checked|formalis|formaliz|axiom-clean|axiom-free', re.I)

def cited_names(txt):
    out = set()
    for m in re.finditer(r'\\texttt\{([^}]*)\}', txt):
        raw = m.group(1).replace('\\_', '_').replace('\\', '')
        for part in re.split(r'[,\s/]+', raw):
            part = part.strip('.')
            if part.endswith('.lean'):
                continue
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", part):
                out.add(part.split('.')[-1])
    return out

up = []
for p in PAPERS:
    txt = open(os.path.join(ROOT, p)).read()
    for m in re.finditer(r'\\begin\{(' + '|'.join(ENVS) + r')\}', txt):
        env = m.group(1); end = txt.find(r'\end{' + env + '}', m.end())
        body = txt[m.end():end] if end > 0 else ''
        if '\\lab{PROVED}' not in body:
            continue
        lm = re.search(r'\\label\{([^}]*)\}', body)
        if not lm:
            continue
        # stop the window at the next environment, or this bleeds into the following statement
        nxt = re.search(r'\\begin\{(?:' + '|'.join(ENVS) + r'|remark)\}', txt[end + 10:end + 3000])
        tail = txt[end:end + 10 + nxt.start()] if nxt else txt[end:end + 3000]
        scope = body + tail
        hits = cited_names(scope) & decls
        if CLAIM.search(scope) and hits:
            up.append((p, lm.group(1), sorted(hits)[:3]))

print(f"{len(up)} statements meet BOTH conditions and are upgradable to VERIFIED")
for p, lab, h in up:
    print(f"  {os.path.basename(p)[8:20]:14} {lab:26} {','.join(h)}")
if '--apply' in sys.argv:
    for p in PAPERS:
        full = os.path.join(ROOT, p); txt = open(full).read(); n = 0
        for pp, lab, _ in up:
            if pp != p:
                continue
            a = '\\label{' + lab + '}\\lab{PROVED}'
            if a in txt:
                txt = txt.replace(a, '\\label{' + lab + '}\\lab{VERIFIED}', 1); n += 1
        open(full, 'w').write(txt); print(f"  upgraded {n} in {p}")
