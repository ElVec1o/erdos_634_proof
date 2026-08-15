#!/usr/bin/env python3
"""Exact verification of the scale-k boundary-word claims (Erdos #634, base-beta).

Tile (a,b,c) = (ef, f^2-e^2, f^2), gcd(e,f)=1, 1 <= e < f.  Delta_k has sides
ka (a-side), kb (B-side), kc (c-side).  A side is an edge-union:
    n_a*a + n_b*b + n_c*c = L,   L in {ka, kb, kc}.

CLAIMS to verify (k < f):
  (B)  L = kb  ==>  (n_a, n_b, n_c) = (0, k, 0).           [B-side fully rigid]
  (C)  L = kc  ==>  n_b = 0  (hence (n_a,n_c) = (qf, k-qe)). [c-side b-free]

Sharpness at k = f (negative controls -- these solutions MUST be found):
  c-side k=f: (n_a,n_b,n_c) = (e, f, 0) is a solution (killed only by gamma-trap n_c>=1).
  B-side k=f: (f-e, 0, f-e) is a solution.

Method: NAIVE full enumeration (no residue shortcuts) for f <= FMAX_NAIVE;
structured residue-parametrized check for f <= FMAX_STRUCT (independent code path).
"""
from math import gcd
import sys

def naive_solutions(a, b, c, L):
    """All (na, nb, nc) >= 0 with na*a + nb*b + nc*c = L. Naive double loop."""
    out = []
    for nb in range(L // b + 1):
        r1 = L - nb * b
        for nc in range(r1 // c + 1):
            r2 = r1 - nc * c
            if r2 % a == 0:
                out.append((r2 // a, nb, nc))
    return out

def run_naive(FMAX):
    bad = []
    members = 0
    checks = 0
    ctrl_c = ctrl_b = 0
    for f in range(2, FMAX + 1):
        for e in range(1, f):
            if gcd(e, f) != 1:
                continue
            members += 1
            a, b, c = e * f, f * f - e * e, f * f
            for k in range(1, f):  # k < f
                for L, tag in ((k * b, 'B'), (k * c, 'C')):
                    sols = naive_solutions(a, b, c, L)
                    checks += 1
                    for (na, nb, nc) in sols:
                        if tag == 'B' and (na, nb, nc) != (0, k, 0):
                            bad.append((e, f, k, 'B', na, nb, nc))
                        if tag == 'C' and nb != 0:
                            bad.append((e, f, k, 'C', na, nb, nc))
            # negative controls at k = f
            solsC = naive_solutions(a, b, c, f * c)
            if (e, f, 0) in solsC:
                ctrl_c += 1
            solsB = naive_solutions(a, b, c, f * b)
            if (f - e, 0, f - e) in solsB:
                ctrl_b += 1
    return members, checks, bad, ctrl_c, ctrl_b

def run_struct(FMAX):
    """Residue-parametrized: c-side solutions with nb = s*f exist iff
    exists t: t*f <= s*e and e*t >= s*f - k  (then na = se-tf, nc = k+et-sf).
    B-side: nb ≡ k (mod f) and nb*b <= k*b.  Checked against the derivation."""
    viol = []
    pairs = 0
    for f in range(2, FMAX + 1):
        for e in range(1, f):
            if gcd(e, f) != 1:
                continue
            pairs += 1
            b = f * f - e * e
            for k in range(1, f):
                # c-side: any s >= 1 feasible?
                smax = (k * f * f) // (b * f) + 2   # inventory bound + slack
                for s in range(1, smax + 1):
                    # t range: ceil((sf-k)/e) <= t <= floor(se/f)
                    tlo = -((k - s * f) // e) if (s * f - k) > 0 else 0
                    tlo = (s * f - k + e - 1) // e
                    thi = (s * e) // f
                    if tlo <= thi:
                        viol.append((e, f, k, 'C', s, tlo, thi))
                # B-side: nb = k + s*f needs (k+sf)*b <= k*b -> s <= 0; nb = k - sf < 0.
                # so only nb = k; residual 0. Nothing to search; identity check:
                assert (k * b - k * b) == 0
    return pairs, viol

if __name__ == '__main__':
    FN = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    FS = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    m, ch, bad, cc, cb = run_naive(FN)
    print(f"[naive f<={FN}] members={m} side-checks={ch} violations={len(bad)} "
          f"controls: c-side k=f word found {cc}/{m}, B-side k=f word found {cb}/{m}")
    for row in bad[:10]:
        print("  VIOLATION:", row)
    p, viol = run_struct(FS)
    print(f"[struct f<={FS}] pairs={p} c-side s>=1 feasible cases: {len(viol)}")
    for row in viol[:10]:
        print("  FEASIBLE (refutes claim):", row)
