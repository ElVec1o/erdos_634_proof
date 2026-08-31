#!/usr/bin/env python3
"""Dependency closure of a paper statement, and its effective label (Rule 0).

Builds the reference graph from \\ref{...} / \\eqref{...} occurring inside each labelled
environment across the three papers, then reports for a target label:

  * the transitive closure of statements it cites,
  * the weakest Rule 0 label in that closure -- the result's effective strength,
  * whether a named hypothesis (default hyp:walls) is reachable.

Used to certify that Paper A's unconditional core has no dependency on Hypothesis (walls).
"""
import glob, re, sys, collections

ENV = re.compile(r'\\begin\{(theorem|proposition|lemma|corollary|remark|conjecture|hypothesis)\}')
END = re.compile(r'\\end\{(theorem|proposition|lemma|corollary|remark|conjecture|hypothesis)\}')
LAB = re.compile(r'\\label\{([A-Za-z]+:[A-Za-z0-9]+)\}')
TAG = re.compile(r'\\lab\{([A-Z]+)')
REF = re.compile(r'\\(?:ref|eqref)\{(?:[A-Z]+-)?([A-Za-z]+:[A-Za-z0-9]+)\}')
# A conditional dependency is also expressed by citing the companion's hypothesis rather than
# \ref-ing a label; without this the checker reports 'no walls dependency' for a statement whose
# own text says 'Assume the complete-corner-wall hypothesis'.
CITEHYP = re.compile(r'\\cite\[[^]]*Hyp[^]]*\]|complete-corner-wall hypothesis|Hypothesis \(walls\)')

def build():
    """Attribute a statement's references to BOTH its own body and the proof block that
    follows it -- dependencies live in proofs, and reading only the statement reports an
    empty closure, which would be false confidence."""
    label_of, refs, order = {}, collections.defaultdict(set), []
    for path in sorted(glob.glob('paper/*.tex')):
        text = open(path).read().split('\n')
        cur, buf, in_proof, last = None, [], False, None
        for line in text:
            if ENV.search(line):
                if cur is not None and buf:
                    for r in REF.findall('\n'.join(buf)):
                        if r != cur: refs[cur].add(r)
                cur, buf, in_proof = None, [line], False
                m = LAB.search(line)
                if m: cur = m.group(1)
                t = TAG.search(line)
                if cur and t: label_of[cur] = t.group(1)
                if cur: order.append(cur); last = cur
                continue
            if cur is not None:
                buf.append(line)
                if END.search(line):
                    body = '\n'.join(buf)
                    for r in REF.findall(body):
                        if r != cur: refs[cur].add(r)
                    if CITEHYP.search(body): refs[cur].add('hyp:walls')
                    cur, buf = None, []
                continue
            # a proof block following the most recent labelled statement
            if line.strip().startswith('\\begin{proof}'):
                in_proof, buf = True, [line]; continue
            if in_proof:
                buf.append(line)
                if line.strip().startswith('\\end{proof}'):
                    if last is not None:
                        body = '\n'.join(buf)
                        for r in REF.findall(body):
                            if r != last: refs[last].add(r)
                        if CITEHYP.search(body): refs[last].add('hyp:walls')
                    in_proof, buf = False, []
    return label_of, refs, order

def closure(refs, start):
    seen, stack = set(), [start]
    while stack:
        x = stack.pop()
        for y in refs.get(x, ()):
            if y not in seen:
                seen.add(y); stack.append(y)
    return seen

RANK = {'VERIFIED': 0, 'PROVED': 1, 'HEURISTIC': 2, 'CONJECTURE': 3, 'OPEN': 4, 'FALSE': 5}

# Statements that appear more than once (an introduction summary plus the body copy) have their
# proof attached to only one occurrence; a closure of size 0 therefore means "no proof block here",
# not "no dependencies". Reported explicitly rather than silently.

def main():
    targets = sys.argv[1:] or ['thm:main', 'thm:iso', 'cor:mod12', 'thm:mod12']
    label_of, refs, _ = build()
    hyp = 'hyp:walls'
    for t in targets:
        cl = closure(refs, t)
        known = {c: label_of[c] for c in cl if c in label_of}
        worst = max(known.values(), key=lambda l: RANK.get(l, 9), default='(none cited)')
        reach = hyp in cl
        print(f"{t}:")
        print(f"   own label      : {label_of.get(t, '(unlabelled)')}")
        print(f"   closure size   : {len(cl)}  ({len(known)} labelled)")
        print(f"   weakest in it  : {worst}")
        if not cl:
            print(f"   NOTE           : no proof block cites anything here; this is an unproved")
            print(f"                    statement or a summary copy whose proof lives elsewhere.")
            print(f"                    Absence of a walls dependency is NOT certified by this run.")
        print(f"   reaches {hyp}: {'YES -- CONDITIONAL' if reach else 'no' if cl else 'undetermined'}")
        bad = sorted(c for c, l in known.items() if RANK.get(l, 9) >= 3)
        if bad: print(f"   >= CONJECTURE  : {', '.join(bad)}")
        print()

if __name__ == '__main__':
    main()
