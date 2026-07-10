#!/usr/bin/env python3
"""
verify_frontier.py  --  the branch sweep for the frontier values (Section 8 of the paper).

For each N in {14, 15, 21, 22, 30, 33, 35, 38, 39, 42, 46}, every branch of the Laczkovich classification is checked by an exact
finite computation. Branches whose published characterizations are equations are decided here;
the four surviving instances (all equilateral or isosceles targets with a uniquely determined
tile) are the ones settled by the exhaustive search engine (code/engine/).

Notation: 120-triple = (a,b,c), gcd(a,b)=1, c^2 = a^2+ab+b^2 (tile with a 2pi/3 angle).
3a2b-tile = integer (a,b,c) with b = c - a^2/c (tile with 3*alpha + 2*beta = pi).
M below always denotes a coloring/invariant count, so M == N (mod 2) since M = B - W, N = B + W.
"""
from math import isqrt, gcd
from fractions import Fraction
from itertools import count

def issq(n):
    return n >= 0 and isqrt(n) ** 2 == n

def is120(a, b):
    if gcd(a, b) != 1:
        return None
    s = a * a + a * b + b * b
    c = isqrt(s)
    return c if c * c == s else None

RESULTS = []
def report(N, branch, verdict, detail=""):
    RESULTS.append((N, branch, verdict, detail))
    print(f"  N={N:2d}  {branch:34s} {verdict:10s} {detail}")

print("=" * 96)
print("Branch sweep for N = 14, 15, 21, 22, 30, 33, 35, 38, 39, 42, 46  (with the parity law M == N mod 2)")
print("=" * 96)

for N in (14, 15, 21, 22, 30, 33, 35, 38, 39, 42, 46):
    # ---- commensurable angles: N must be square, sum of two squares, or 2,3,6 x square ----
    forms = (issq(N) or any(issq(N - e * e) for e in range(1, isqrt(N) + 1))
             or (N % 2 == 0 and issq(N // 2)) or (N % 3 == 0 and issq(N // 3))
             or (N % 6 == 0 and issq(N // 6)))
    report(N, "commensurable [B-seven Thm 3]", "dead" if not forms else "ALIVE")

    # ---- tile similar to ABC: N = n^2 ----
    report(N, "tile-similar [SWW]", "dead" if not issq(N) else "ALIVE")

    # ---- right-angle tile (isosceles target): N = square, even sum of 2 squares, 6n^2 ----
    ok = issq(N) or (N % 6 == 0 and issq(N // 6)) or (N % 2 == 0 and any(
        issq(N - e * e) for e in range(1, isqrt(N) + 1)))
    report(N, "right-angle tile [B-iso]", "dead" if not ok else "ALIVE")

    # ---- gamma = 2 alpha tile: N not squarefree ----
    sqfree = all((N % (p * p)) for p in range(2, isqrt(N) + 1))
    report(N, "gamma=2alpha [B-iso 11.7]", "dead" if sqfree else "ALIVE")

    # ---- 2pi/3 tile, non-equilateral targets: the admissible spectra ----
    hits = []
    for a in range(1, 400):
        for b in range(1, 400):
            c = is120(a, b)
            if not c:
                continue
            for (form, name) in (((a + 2 * b), "isoA"), ((2 * a + b), "isoB"),
                                 ((a + b), "F1")):
                if N % form == 0:
                    # spectrum: N = d*w^2*form with d = squarefree kernel of the leg
                    leg = b if name in ("isoA", "F1") else a
                    d = 1
                    m = leg
                    for p in range(2, isqrt(leg) + 1):
                        while m % (p * p) == 0:
                            m //= p * p
                    d = m  # squarefree kernel of leg (crude but exact for small leg)
                    rest = N // form
                    if rest % d == 0 and issq(rest // d):
                        w = isqrt(rest // d)
                        leg2 = leg // d
                        e = isqrt(leg2)
                        if name in ("isoA", "isoB"):
                            # invariant count M = w(c-a-b)/e; parity law M == N (mod 2)
                            Mnum = w * (c - a - b)
                            if Mnum % e or ((Mnum // e) - N) % 2:
                                continue
                            if N < 36:
                                continue        # Beeson rules out N < 36 for iso 2pi/3 [B-iso]
                        if name == "F1":
                            # Phi-invariant on the F1 target (sides k(a+b), ka, kc):
                            # Phi_alpha = k(2a+b-c) must be divisible by c+a-b, and
                            # Phi_beta  = k(2a+b+c) by c+b-a  (one failure kills)
                            w = isqrt(rest // d)
                            e2leg = isqrt(b * b // (d * d)) if False else None
                            # scale k from N = k^2 (a+b)/b: k^2 = N b/(a+b)
                            k2 = N * b // form
                            k = isqrt(k2)
                            if k * k == k2:
                                MA, ra = divmod(k * (2 * a + b - c), c + a - b)
                                MB, rb = divmod(k * (2 * a + b + c), c + b - a)
                                okA = ra == 0 and (MA - N) % 2 == 0
                                okB = rb == 0 and (MB - N) % 2 == 0
                                if okA and okB:
                                    hits.append((N, name, a, b, c))
                            # non-square k^2 cannot occur here (spectrum passed)
                        else:
                            hits.append((N, name, a, b, c))
    # F2/F3/F4 minimum N0 = 88 > 15, checked in verify_shapes.py
    report(N, "2pi/3 sporadic shapes [spectrum]", "dead" if not hits else "ALIVE", str(hits))

    # ---- pi/3 tile, equilateral target: Beeson-Eq Thm 3: (9N - M^2)(N - M^2) = square ----
    sols = [M for M in range(1, isqrt(N) + 1) if M * M < N and (N - M) % 2 == 0
            and issq((9 * N - M * M) * (N - M * M))]
    report(N, "pi/3-equilateral [B-eq Thm 3]", "dead" if not sols else "ALIVE", f"M={sols}")

    # ---- 3a+2b=pi, shape (2b,b,a+b): N = 2K^2 - M^2 with K | M^2  [B-III Thm 7, iff] ----
    sols = [(M, K) for M in range(1, isqrt(N) + 1) if M * M < N
            for K in range(1, isqrt((N + M * M) // 2) + 1)
            if 2 * K * K == N + M * M and M * M % K == 0]
    report(N, "3a2b (2b,b,a+b) [B-III Thm 7]", "dead" if not sols else "ALIVE", str(sols))

    # ---- 3a+2b=pi, shape with second tiling equation [B-III Thm 11, iff] ----
    # N/M^2 = (2-s^2)(3-s^2) / ((1-s)^2 (2+s)^2), rational s in (0,1).
    def rational_roots(coeffs):
        """all rational roots of an integer-coefficient polynomial, exact"""
        while coeffs and coeffs[-1] == 0:
            coeffs = coeffs[:-1]
        if not coeffs:
            return []
        lead, const = coeffs[0], coeffs[-1]
        if const == 0:
            return [Fraction(0)] + rational_roots(coeffs[:-1])
        roots = []
        for p in range(1, abs(const) + 1):
            if const % p:
                continue
            for q in range(1, abs(lead) + 1):
                if lead % q:
                    continue
                for sgn in (1, -1):
                    s = Fraction(sgn * p, q)
                    if sum(cf * s ** (len(coeffs) - 1 - i) for i, cf in enumerate(coeffs)) == 0:
                        if s not in roots:
                            roots.append(s)
        return roots
    alive = []
    for M in range(1, isqrt(N) + 1):
        if (N - M) % 2:
            continue
        v = Fraction(N, M * M)
        # (v-1)s^4 + 2v s^3 - (3v-5)s^2 - 4v s + (4v-6) = 0, cleared to integers
        den = v.denominator
        cf = [ (v - 1) * den, 2 * v * den, -(3 * v - 5) * den, -4 * v * den, (4 * v - 6) * den ]
        cf = [int(x) for x in cf]
        for s in rational_roots(cf):
            if 0 < s < 1:
                alive.append((M, s))
    report(N, "3a2b 2nd-equation [B-III Thm 11]", "dead" if not alive else "ALIVE", str(alive))

    # ---- 3a+2b=pi, isosceles base beta [B-III Thm 14]: N/M^2 = (3-s^2)/(1+s)^2 ----
    alive = []
    for M in range(1, isqrt(2 * N) + 1):
        if (N - M) % 2 or 3 * M * M <= N or M * M >= 2 * N:
            continue
        # N (1+s)^2 = M^2 (3 - s^2):  (N+M^2) s^2 + 2N s + (N - 3M^2) = 0
        A, B, C = N + M * M, 2 * N, N - 3 * M * M
        disc = B * B - 4 * A * C
        if issq(disc):
            s = Fraction(-B + isqrt(disc), 2 * A)
            if 0 < s < 1:
                if M % s.denominator == 0:      # Thm 14: g divides M
                    alive.append((M, s))
    report(N, "3a2b iso-beta [B-III Thm 14]", "dead" if not alive else "ALIVE", str(alive))

    # ---- 3a+2b=pi, isosceles base alpha [B-III Thm 19]: ----
    # N/M^2 = (1+s)(2-s^2)/((1-s)(2+s)^2):  (v-1)s^3+(3v-1)s^2+2s+(2-4v)=0 after clearing
    alive = []
    for M in range(1, isqrt(2 * N) + 1):
        if (N - M) % 2:
            continue
        v = Fraction(N, M * M)
        den = v.denominator
        cf = [int((v - 1) * den), int((3 * v - 1) * den), int(2 * den), int((2 - 4 * v) * den)]
        for s in rational_roots(cf):
            if 0 < s < 1:
                if M % s.denominator == 0:      # Thm 19: g = gcd(a,c) = f divides M
                    alive.append((M, s))
    report(N, "3a2b iso-alpha [B-III Thm 19]", "dead" if not alive else "ALIVE", str(alive))

    # ---- 3a+2b=pi, isosceles base alpha+beta [B-III Thm 17 + congruence (28)] ----
    # N/M^2 = (1+s)/(1-s) => s = (N-M^2)/(N+M^2); tile (ef, f^2-e^2, f^2) for s = e/f;
    # X^2 = N b c; congruence: M = -m (mod g), g = gcd(a,c), m = #b-edges on the base,
    # base Y = p a + m b + q c with p,q >= 0.
    survivors = []
    for M in range(1, isqrt(N) + 1):
        if (N - M) % 2 or M * M >= N:
            continue
        s = Fraction(N - M * M, N + M * M)
        e, f = s.numerator, s.denominator
        a0, b0, c0 = e * f, f * f - e * e, f * f
        g0 = gcd(gcd(a0, b0), c0)
        a0, b0, c0 = a0 // g0, b0 // g0, c0 // g0
        # X^2 = N b c must be a perfect square (X = length of the equal sides)
        if not issq(N * b0 * c0):
            continue
        X = isqrt(N * b0 * c0)
        lam = Fraction(X, c0)
        Y = lam * a0
        if Y.denominator != 1:
            continue
        Y = int(Y)
        g = gcd(a0, c0)
        okm = [m for m in range(0, Y // b0 + 1) if (M + m) % g == 0
               and any(Y - m * b0 - qq * c0 >= 0 and (Y - m * b0 - qq * c0) % a0 == 0
                       for qq in range(0, (Y - m * b0) // c0 + 1))]
        if okm:
            survivors.append((M, (a0, b0, c0), (X, X, Y), f"m in {okm}"))
    report(N, "3a2b iso-(a+b) [Thm 17 + cong 28]",
           "dead" if not survivors else "ENGINE", str(survivors))

    # ---- 2pi/3 tile, equilateral target: st = 3N criterion ----
    # X=c+a-b, Y=c+b-a: XY = 3ab, X | 3S, Y | 3S, S^2 = N a b  =>  s t = 3N with
    # s = 3S/X, t = 3S/Y, and (t-s)^2 + 16N must be a perfect square.
    inst = []
    for s in range(1, 3 * N + 1):
        if (3 * N) % s:
            continue
        t = 3 * N // s
        if s > t:
            continue
        if (s - N) % 2 or (t - N) % 2:
            continue
        q2 = (t - s) ** 2 + 16 * N
        if issq(q2):
            q = isqrt(q2)
            # a = S(q + (t-s))/(4N), b = S(q - (t-s))/(4N), c = S(s+t)/(2 s t) * 3 ... derive:
            # a+b = S q/(2N), a-b = S(t-s)/(2N), c = (X+Y)/2 = 3S(s+t)/(2 s t) = S(s+t)/(2N)
            # primitive scale: S/(4N) * (q + t - s, q - t + s, 2(s+t)) made integral & primitive
            va, vb, vc = q + (t - s), q - (t - s), 2 * (s + t)
            g0 = gcd(gcd(va, vb), vc)
            va, vb, vc = va // g0, vb // g0, vc // g0
            if is120(va, vb) == vc or is120(vb, va) == vc:
                S = 4 * N // g0  # S/(4N) * g0 = 1 for the primitive tile
                inst.append(((va, vb, vc), f"S={S}", f"(s,t)=({s},{t})"))
    report(N, "2pi/3-equilateral [st=3N crit]",
           "dead" if not inst else "ENGINE", str(inst))

print()
print("Surviving finite instances (settled by the exhaustive engine):")
for (N, br, v, d) in RESULTS:
    if v == "ENGINE":
        print(f"  N={N}: {br}: {d}")
