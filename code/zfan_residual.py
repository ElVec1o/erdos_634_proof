#!/usr/bin/env python3
"""The exact residual set of the rogue-slot problem, member by member.

Layers, in order of strength of provenance:

  T  theorem layer (uniform in f, axiom-clean Lean):
     K0-K3 (RogueContainment/RogueChord) confine the slots to
     floor(f/e)+2 <= M <= k-2, i.e. r = k-M >= 2;
     top2 (RogueMirror + the L1-L4 room kills, exact-verified):
     r = 2 dies for e >= 3;
     top3 (RogueMirror flush core + the a+2c closure, exact-verified
     f <= 12): r = 3 dies for e >= 4.
  E  engine layer (per-member, per-scale, fixed engine only —
     pre-fix verdicts are not trusted): open-KILLED rows kill every
     scale of the slot; rN-KILLED rows kill k = M+N.

The residual printed per member is the set of (M, k) pairs killed by
neither layer.  Every pair listed is an OPEN configuration; an empty
list means the member's whole rogue tower {W(k) : k <= f} is closed.

Usage: zfan_residual.py <recert-table> [fmax]
"""
from math import gcd
import re
import sys


def members(fmax):
    for f in range(3, fmax + 1):
        for e in range(2, f):
            if gcd(e, f) == 1:
                yield e, f


def parse_recert(path):
    """-> {(e,f,M): {'open': v, 2: v, 3: v, ...}} for the free section."""
    out = {}
    section = None
    for line in open(path):
        m = re.match(r"== chord=(\w+) ==", line)
        if m:
            section = m.group(1)
            continue
        if section != "free":
            continue
        m = re.match(r"\((\d+),(\d+)\) M=(\d+): (.*)", line)
        if not m:
            continue
        e, f, M = int(m.group(1)), int(m.group(2)), int(m.group(3))
        cells = {}
        for cell in m.group(4).split():
            if ":" not in cell:
                continue
            key, v = cell.split(":", 1)
            cells["open" if key == "open" else int(key[1:])] = v
        out[(e, f, M)] = cells
    return out


def main():
    recert = parse_recert(sys.argv[1]) if len(sys.argv) > 1 else {}
    fmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    grand_open = 0
    closed_members = []
    for e, f in members(fmax):
        Mlo, Mhi = f // e + 2, f - 2
        if Mlo > Mhi:
            closed_members.append((e, f))
            continue
        residual = []
        for M in range(Mlo, Mhi + 1):
            for r in range(2, f - M + 1):
                if r == 2 and e >= 3:
                    continue                      # top2 (theorem)
                if r == 3 and e >= 4:
                    continue                      # top3 (flush core + exact)
                cells = recert.get((e, f, M), {})
                if cells.get("open") == "KILLED":
                    continue                      # engine, all k
                if cells.get(r) == "KILLED":
                    continue                      # engine, this k
                residual.append((M, M + r))
        if residual:
            grand_open += len(residual)
            print(f"({e},{f}): residual (M,k) pairs [{len(residual)}]: "
                  + " ".join(f"({M},{k})" + ("*" if k == f else "")
                             for M, k in residual))
        else:
            closed_members.append((e, f))
    print(f"\nclosed members (empty residual): {closed_members}")
    print(f"total open (M,k) pairs, f <= {fmax}: {grand_open}")
    print("(* = wall scale k = f.  The b^f base reading these cells sat")
    print(" under is PROVED -- RogueMirror.wall_base_reading (2026-08-15);")
    print(" the arithmetic sharpness RogueMirror.base_side_wall_family")
    print(" stands, the geometry kills the family.  The * marks are kept")
    print(" as scale markers only; no conditionality attaches.)")


if __name__ == "__main__":
    main()
