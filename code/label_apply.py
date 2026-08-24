#!/usr/bin/env python3
"""Assign Rule 0 labels by dependency closure, not by guesswork.

Rule 0: the effective strength of a result is the WEAKEST label in its dependency chain.  So the
labels are computed, not chosen:

  1. Seed a weak set with the statements known to be open or conditional (the roots below).
  2. Close it transitively over \\ref edges: a statement whose own statement-or-proof cites a weak
     statement is itself at most CONJECTURE.
  3. Everything outside the closure that carries a proof is PROVED.

VERIFIED is never assigned mechanically.  Citing a Lean file does not mean the cited declaration
proves that statement, so those stay at PROVED, which under-claims.  Under-claiming is the safe
direction: Rule 0 forbids presenting a result as stronger than its weakest dependency, not weaker.
Upgrades to VERIFIED are made by hand, one statement at a time, after checking the Lean matches.
"""
import re, os, sys

ENVS = ('theorem', 'proposition', 'lemma', 'corollary', 'conjecture', 'hypothesis')
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAPERS = ['paper/erdos-634.tex', 'paper/erdos-634-companion.tex', 'paper/erdos-634-obstructions.tex']

# statements known to be open, conditional, or resting on a deferral
WEAK_ROOTS = {
    'hyp:walls', 'conj:advance', 'lem:interior', 'thm:e1family', 'cor:walls16',
    'prop:a2branch', 'thm:fullprime', 'thm:basebeta-full', 'thm:strippbound',
    'thm:depthwindow', 'thm:inflrigid', 'cor:sidenoa-proved', 'rem:sidenoa',
}

def blocks(path):
    """(label, statement-body, following-proof) per environment."""
    txt = open(os.path.join(ROOT, path)).read()
    out = []
    for m in re.finditer(r'\\begin\{(' + '|'.join(ENVS) + r')\}', txt):
        env = m.group(1)
        end = txt.find(r'\end{' + env + '}', m.end())
        body = txt[m.end():end] if end > 0 else ''
        tail = txt[end:end + 4000] if end > 0 else ''
        pm = tail.find(r'\begin{proof}')
        proof = ''
        if 0 <= pm < 400:
            pe = tail.find(r'\end{proof}', pm)
            proof = tail[pm:pe] if pe > 0 else tail[pm:pm + 3000]
        lm = re.search(r'\\label\{([^}]*)\}', body)
        out.append((lm.group(1) if lm else None, body, proof, env, path, m.end()))
    return out

allb = []
for p in PAPERS:
    if os.path.exists(os.path.join(ROOT, p)):
        allb += blocks(p)

refs = {}
for lab, body, proof, env, path, pos in allb:
    if lab:
        refs[lab] = set(re.findall(r'\\ref\{([^}]*)\}', body + proof))

weak = set(WEAK_ROOTS)
for _ in range(40):                      # transitive closure
    grew = False
    for lab, r in refs.items():
        if lab not in weak and (r & weak):
            weak.add(lab); grew = True
    if not grew:
        break

def has_inline_argument(body):
    """Many statements here carry their proof inside the statement body, usually ending in a
    machine-check citation.  Treat a Lean citation or an explicit derivation cue as a proof."""
    return bool(re.search(r'\\texttt\{[^}]*\.lean[^}]*\}|machine-checked|kernel-checked|'
                          r'axiom-free|axiom-clean|by \\texttt|\\emph\{Proof', body, re.I))

def classify(lab, body, proof):
    if lab in weak:
        return 'CONJECTURE'
    if proof or has_inline_argument(body):
        return 'PROVED'
    return None

n_weak = sum(1 for lab, body, proof, *_ in allb if classify(lab, body, proof) == 'CONJECTURE')
n_proof = sum(1 for lab, body, proof, *_ in allb if classify(lab, body, proof) == 'PROVED')
n_bare = sum(1 for lab, body, proof, *_ in allb if classify(lab, body, proof) is None)
print(f"{len(allb)} statements")
print(f"  CONJECTURE (in the weak closure) : {n_weak}")
print(f"  PROVED     (has a proof, clean)  : {n_proof}")
print(f"  needs a hand label (no proof)    : {n_bare}")
if '--list-bare' in sys.argv:
    for lab, body, proof, env, path, pos in allb:
        if classify(lab, body, proof) is None:
            print(f"    {os.path.basename(path)}  {env}  {lab}")


if '--apply' in sys.argv:
    import collections
    edits = collections.defaultdict(list)
    for lab, body, proof, env, path, pos in allb:
        if not lab:
            continue
        if '\\lab{' in body:            # already labelled by hand; leave it
            continue
        k = classify(lab, body, proof)
        if k is None:
            continue
        edits[path].append((lab, k))
    for path, items in edits.items():
        full = os.path.join(ROOT, path)
        txt = open(full).read()
        n = 0
        for lab, k in items:
            anchor = '\\label{' + lab + '}'
            if anchor in txt:
                i = txt.index(anchor) + len(anchor)
                if txt[i:i + 5] != '\\lab{':
                    txt = txt[:i] + '\\lab{' + k + '}' + txt[i:]
                    n += 1
        open(full, 'w').write(txt)
        print(f"  applied {n} labels to {path}")
