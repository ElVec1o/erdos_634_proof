#!/usr/bin/env python3
"""Verify the invariant-product table (paper, Prop. `prop:product` and Table `tab:product`).

For a 2pi/3 tile (a,b,c) with c^2 = a^2+ab+b^2 and a target of one of the eleven admissible
shapes, the two signed-direction invariants

    M_alpha = Phi_{f_alpha}(dABC) / (c+a-b),    M_beta = Phi_{f_beta}(dABC) / (c+b-a)

are integers (paper Cor. `cor:int`).  This script checks, in exact symbolic arithmetic, that their
product is the stated fixed rational multiple of the tile count N on every shape, and then checks
the resulting identities numerically against three configurations taken from the paper itself.

A target corner angle is  M*alpha + K*(pi/3).  Traversing the boundary counterclockwise,
    dir(e_{i+1}) = dir(e_i) + pi - theta_{i+1},
so writing dir = j*(pi/3) + k*alpha we get j_{i+1} = j_i + 3 - K_{i+1} and k_{i+1} = k_i - M_{i+1};
then f_alpha = (-1)^j and f_beta = (-1)^(j+k).  The side |V_i V_{i+1}| is opposite V_{i+2}.

Overall sign note: the direction grid is only fixed up to a global rotation by a grid element, which
multiplies f_alpha by (-1)^n and f_beta by (-1)^(n+m).  So M_alpha and M_beta are each defined up to
sign and only |M_alpha * M_beta| is gauge-invariant; the table records one consistent gauge.

Needs sympy.  Prints PASS lines and a RESULT block; every check is an assert.
"""
import sympy as sp
from fractions import Fraction as F

a, b, c = sp.symbols('a b c', positive=True)
S3 = sp.sqrt(3)
REL = c ** 2 - (a ** 2 + a * b + b ** 2)

E_al = (2 * b + a) / (2 * c) + sp.I * a * S3 / (2 * c)      # e^{i alpha}
E_60 = sp.Rational(1, 2) + sp.I * S3 / 2                     # e^{i pi/3}

# the eleven shapes, as corner types (M_i, K_i) in counterclockwise order
SHAPES = {
    'equilateral':   ([(0, 1), (0, 1), (0, 1)], 3),
    'tile-similar':  ([(1, 0), (-1, 1), (0, 2)], 1),
    'iso base-alpha': ([(1, 0), (1, 0), (-2, 3)], -a / (a + 2 * b)),
    'iso base-beta': ([(-1, 1), (-1, 1), (2, 1)], -b / (2 * a + b)),
    'F1':            ([(1, 0), (0, 1), (-1, 2)], 1),
    'F2':            ([(2, 0), (-2, 2), (0, 1)], 3 * a * b / ((a + 2 * b) * (2 * a + b))),
    'F3':            ([(1, 0), (2, 0), (-3, 3)], -a / (a + 2 * b)),
    'F4':            ([(1, 0), (-2, 2), (1, 1)], -b / (2 * a + b)),
    "F1'":           ([(-1, 1), (0, 1), (1, 1)], 1),
    "F3'":           ([(-1, 1), (-2, 2), (3, 0)], -b / (2 * a + b)),
    "F4'":           ([(-1, 1), (2, 0), (-1, 2)], -a / (a + 2 * b)),
}


def sin_of(M, K):
    return sp.im(sp.expand(sp.simplify(E_al ** M * E_60 ** K)))


def reduce_mod_rel(e):
    num, den = sp.fraction(sp.together(sp.simplify(e)))
    num = sp.rem(sp.Poly(sp.expand(num), c), sp.Poly(REL, c)).as_expr()
    den = sp.rem(sp.Poly(sp.expand(den), c), sp.Poly(REL, c)).as_expr()
    return sp.simplify(num / den)


def ratio_for(corners):
    sigma = [sp.simplify(sin_of(*corners[(i + 2) % 3])) for i in range(3)]
    j, k = [0, 0, 0], [0, 0, 0]
    for i in range(2):
        j[i + 1] = j[i] + 3 - corners[i + 1][1]
        k[i + 1] = k[i] - corners[i + 1][0]
    # closure: after the third turn the direction must have advanced by exactly 2*pi
    assert (j[2] + 3 - corners[0][1], k[2] - corners[0][0]) == (6, 0), 'boundary does not close'
    Phi_a = sum(sigma[i] * (-1) ** j[i] for i in range(3))
    Phi_b = sum(sigma[i] * (-1) ** (j[i] + k[i]) for i in range(3))
    N = sp.simplify(sp.Rational(1, 2) * sigma[0] * sigma[2] * sin_of(*corners[0]) / (a * b * S3 / 4))
    MaMb = sp.simplify(Phi_a * Phi_b / ((c + a - b) * (c + b - a)))
    return reduce_mod_rel(MaMb / N)


print('--- symbolic: M_alpha * M_beta / N on each of the eleven shapes ---')
for name, (corners, expected) in SHAPES.items():
    got = ratio_for(corners)
    ok = sp.simplify(sp.factor(got) - sp.factor(expected)) == 0
    assert ok, f'{name}: expected {expected}, got {got}'
    print(f'  PASS  {name:14s}  M_a*M_b/N = {sp.factor(got)}')

print('\n--- the three shapes on which the product is exactly N ---')
unit = [n for n, (_, e) in SHAPES.items() if sp.simplify(e - 1) == 0]
assert set(unit) == {'tile-similar', 'F1', "F1'"}, unit
print(f'  PASS  M_alpha * M_beta = N exactly on: {", ".join(unit)}')

# ---------------------------------------------------------------- numerical cross-checks -----
def Ma_F1(A, B, C, k): return F(k * (2 * A + B - C), C + A - B)
def Mb_F1(A, B, C, k): return F(k * (2 * A + B + C), C + B - A)
def N_F1(A, B, C, k):  return F(k * k * (A + B), B)
def Ma_isoA(A, B, C, k): return F(k * (2 * B + A - 2 * C), C + A - B)
def Mb_isoA(A, B, C, k): return F(k * (2 * B + A + 2 * C), C + B - A)
def N_isoA(A, B, C, k):  return F(k * k * (A + 2 * B), B)

print('\n--- numerical cross-checks against configurations named in the paper ---')
# F1 target of the tile (8,7,13) at k=7: the paper states N=105, M_alpha=5, M_beta=21
A, B, C, k = 8, 7, 13, 7
assert C * C == A * A + A * B + B * B
Ma, Mb, N = Ma_F1(A, B, C, k), Mb_F1(A, B, C, k), N_F1(A, B, C, k)
assert (Ma, Mb, N) == (5, 21, 105) and Ma * Mb == N
print(f'  PASS  F1 on (8,7,13), k=7:  N={N}, M_a={Ma}, M_b={Mb}, M_a*M_b={Ma*Mb} = N')

# F1 target of the tile (3,5,7) at k=5
A, B, C, k = 3, 5, 7, 5
Ma, Mb, N = Ma_F1(A, B, C, k), Mb_F1(A, B, C, k), N_F1(A, B, C, k)
assert Ma * Mb == N
print(f'  PASS  F1 on (3,5,7), k=5:   N={N}, M_a={Ma}, M_b={Mb}, M_a*M_b={Ma*Mb} = N')

# Herdt's genuine 2673-tiling: iso base-alpha, tile (5,3,7), k=27; paper states M_alpha=-9
A, B, C, k = 5, 3, 7, 27
Ma, Mb, N = Ma_isoA(A, B, C, k), Mb_isoA(A, B, C, k), N_isoA(A, B, C, k)
assert Ma == -9 and N == 2673
assert Ma * Mb == -F(N * A, A + 2 * B)
print(f'  PASS  iso base-alpha on (5,3,7), k=27 (Herdt, a GENUINE tiling):')
print(f'          N={N}, M_a={Ma}, M_b={Mb}, M_a*M_b={Ma*Mb} = -N*a/(a+2b)')

# ------------------------------------------------------------------- prime consequences -----
print('\n--- consequences for a prime tile count ---')
# F1: M_a*M_b = N prime forces |M_a|=1, |M_b|=N, hence (c+a)/(c-a)=N, hence a/c=(N-1)/(N+1);
# the tile is then rational iff N^2+14N+1 is a perfect square.
bad = [n for n in range(7, 200001) if sp.integer_nthroot(n * n + 14 * n + 1, 2)[1]]
assert bad == [], bad
print('  PASS  N^2+14N+1 is a perfect square for no N in [7, 200000]')
print('        (proved for all N>6 in lean/InvariantProduct.lean: disc_not_square)')
sols = [n for n in range(0, 200001) if sp.integer_nthroot(n * n + 14 * n + 1, 2)[1]]
assert sols == [0, 1, 6], sols
print(f'  PASS  the only nonnegative solutions at all are N in {sols}')

print("""
RESULT
  The product M_alpha * M_beta is a fixed rational multiple of N on every one of the eleven
  admissible target shapes, and equals N exactly on the tile-similar and F1 (and F1') targets,
  and 3N on the equilateral target.  Consequences, both citation-free:
    - tile-similar target: N = M_alpha^2, a perfect square, hence never prime;
    - F1 target: a prime N forces |M_alpha| = 1 and a/c = (N-1)/(N+1), which makes the tile
      irrational (N^2+14N+1 is not a square for N > 6).
  Verified symbolically on all eleven shapes and numerically against three configurations from
  the paper, one of which (Herdt's 2673-tiling) is a genuine tiling.""")
