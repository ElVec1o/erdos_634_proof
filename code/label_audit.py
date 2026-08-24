#!/usr/bin/env python3
"""Rule 0 / Rule 18 label audit of the shipping LaTeX.

Every numbered mathematical statement in a file that ships must carry exactly one Rule 0 label:
VERIFIED, PROVED, HEURISTIC, CONJECTURE, FALSE.  This enumerates the theorem-like environments,
reports which carry a label, and classifies the rest by the evidence actually present:

  lean      the statement or its proof cites a Lean declaration or file  -> candidate VERIFIED
  proof     a \\begin{proof} follows and no Lean is cited                 -> candidate PROVED
  bare      neither                                                      -> must be labelled by hand

A candidate is not a label.  Rule 0 requires the label to be earned, and the effective strength of a
statement is the weakest label in its dependency chain, which this script cannot see.
"""
import re, sys, os

ENVS = ('theorem', 'proposition', 'lemma', 'corollary', 'conjecture', 'hypothesis')
LABELS = ('VERIFIED', 'PROVED', 'HEURISTIC', 'CONJECTURE', 'FALSE')
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SHIPPING = ['paper/erdos-634.tex', 'paper/erdos-634-companion.tex', 'paper/erdos-634-obstructions.tex']

def audit(path):
    txt = open(os.path.join(ROOT, path)).read()
    out = []
    for m in re.finditer(r'\\begin\{(' + '|'.join(ENVS) + r')\}', txt):
        env = m.group(1)
        end = txt.find(r'\end{' + env + '}', m.end())
        body = txt[m.end():end if end > 0 else m.end() + 1200]
        # the statement plus whatever proof directly follows it
        tail = txt[end:end + 2500] if end > 0 else ''
        lab = re.search(r'\\label\{([^}]*)\}', body)
        name = lab.group(1) if lab else '(unlabelled)'
        has_rule0 = any(L in body for L in LABELS)
        cites_lean = bool(re.search(r'\\texttt\{[^}]*(lean|\.lean|_)[^}]*\}', body + tail[:900], re.I))
        has_proof = r'\begin{proof}' in tail[:400]
        if has_rule0:
            kind = 'LABELLED'
        elif cites_lean:
            kind = 'lean'
        elif has_proof:
            kind = 'proof'
        else:
            kind = 'bare'
        out.append((env, name, kind))
    return out

total = {}
for path in SHIPPING:
    if not os.path.exists(os.path.join(ROOT, path)):
        continue
    rows = audit(path)
    counts = {}
    for _, _, k in rows:
        counts[k] = counts.get(k, 0) + 1
    print(f"{path}: {len(rows)} statements  " +
          "  ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    for k, v in counts.items():
        total[k] = total.get(k, 0) + v
    if '-v' in sys.argv:
        for env, name, k in rows:
            if k == 'bare':
                print(f"    bare: {env} {name}")

n = sum(total.values())
unlabelled = n - total.get('LABELLED', 0)
print()
print(f"TOTAL {n} statements; {total.get('LABELLED',0)} carry a Rule 0 label; "
      f"ORPHAN STATEMENTS = {unlabelled}")
print(f"  of the orphans: lean-citing={total.get('lean',0)}  proof-only={total.get('proof',0)}  "
      f"bare={total.get('bare',0)}")
sys.exit(1 if unlabelled else 0)
