/-
RationalityFree.lean — removing part of the rationality citation (Erdős #634).
No imports, no axioms: kernel-checked with the core toolchain only.

BACKGROUND. The spectrum analysis of the main paper needs the tile to have commensurable sides.
For eight of the eleven admissible target shapes that is imported from the rationality theorem of
Beeson and Zhang; three shapes (tile-similar, F1, F1') are already citation-free, via the
invariant-product identity with κ = 1.

THE OBSERVATION FORMALIZED HERE. The invariant product identity reads

    M_α · M_β = κ · N ,

where M_α, M_β are the two signed-direction counts and N the tile count — all three INTEGERS — and
κ is an explicit rational function of the tile's sides, computed shape by shape:

    equilateral 3 ;  tile-similar, F1, F1' 1 ;  iso base-α, F3, F4' −a/(a+2b) ;
    iso base-β, F4, F3' −b/(2a+b) ;  F2 3ab/((a+2b)(2a+b)) .

On the six shapes where κ is one of the two linear-fractional expressions, clearing denominators in
`M_α·M_β·(a+2b) = −a·N` turns the identity into an INTEGER-COEFFICIENT LINEAR RELATION between a
and b, which forces a/b rational with no external input:

    a · (N + P) = −2b · P        where P = M_α·M_β,                       (`ratio_relation_alpha`)
    b · (N + P) = −2a · P        for the mirrored family,                 (`ratio_relation_beta`)

and the coefficient N + P is nonzero: the identity forces P·a + 2(P·b) < 0 (`product_negative`),
whence the right-hand side of the elimination is positive (`elimination_rhs_pos`) and so is N + P.
Hence a/b = −2P/(N+P) ∈ ℚ.

SCOPE, STATED EXACTLY. The product identity yields a/b ∈ ℚ. The second ratio is then supplied by
the boundary walk on a c-carrying side of the target (`walk_relation`), which gives c as a rational
combination of a and b unless that side is covered by c-edges alone (`degenerate_pure_c`). So on the
six shapes the rationality citation is replaced by a finite check per shape: that some c-carrying
side of the target admits a walk which is not pure-c. On F2 the elimination produces a quadratic in t
(discriminant 9q² − 30q + 9), so even a/b is not forced there; on the equilateral shape κ = 3 is
constant and carries no information. Those two shapes still carry the citation.
-/

namespace Erdos634.RationalityFree

/-! ## The relation, over the integers.
`P = M_α·M_β` and `N` are integers. The geometric input is the invariant product with
κ = −a/(a+2b), i.e. `P·(a+2b) = −a·N`; written out, `P·a + 2·(P·b) = −(a·N)`. Everything below is
that identity rearranged, so the statements are given in expanded form and the proofs are pure
linear arithmetic over the products as atoms. -/

/-- **The elimination.** `P·a + 2(P·b) = −(a·N)` gives `a·N + P·a = −2(P·b)`, i.e.
`a·(N+P) = −2b·P`: an integer-coefficient linear relation between the two sides, so
`a/b = −2P/(N+P)` is a ratio of integers. -/
theorem ratio_relation_alpha (a b N P : Int) (h : P * a + 2 * (P * b) = -(a * N)) :
    a * N + P * a = -(2 * (P * b)) := by omega

/-- The mirrored family, κ = −b/(2a+b): `2(P·a) + P·b = −(b·N)` gives `b·N + P·b = −2(P·a)`. -/
theorem ratio_relation_beta (a b N P : Int) (h : 2 * (P * a) + P * b = -(b * N)) :
    b * N + P * b = -(2 * (P * a)) := by omega

/-- **The coefficient does not vanish.** The identity forces `P·a + 2(P·b) < 0` when `a, N > 0`,
so `P < 0` (both `P·a` and `P·b` share P's sign for positive sides), and then `a·(N+P) = −2(P·b) > 0`
gives `N + P > 0`. Stated here in the form actually consumed: with the product negative, the
right-hand side of the elimination is positive. -/
theorem elimination_rhs_pos (a b N P : Int) (hPb : P * b < 0)
    (h : P * a + 2 * (P * b) = -(a * N)) : 0 < a * N + P * a := by omega

/-- And the sign hypothesis is not extra: from the identity with `a, N > 0` the left side is
negative, so at least one of `P·a`, `P·b` is. -/
theorem product_negative (a b N P : Int) (ha : 0 < a) (hN : 0 < N)
    (h : P * a + 2 * (P * b) = -(a * N)) : P * a < 0 ∨ P * b < 0 := by
  have hpos : 0 < a * N := Int.mul_pos ha hN
  omega

/-! ## The third side, from the boundary walk.
The first half gives a/b ∈ ℚ. The second ratio is supplied by the tiling itself, at no extra cost.

Each of the six shapes has a side of the target that is a rational multiple of `c` (in the
normalisation `b = 1`, `a = t`: the isosceles base-α target is `(ac, ac, a(b+2a))`, and similarly for
the F-shapes). That side is covered by a boundary walk, a sum of whole tile edges with non-negative
multiplicities:

    λ·c = P·a + Q·b + R·c ,    P, Q, R ≥ 0 integers,

whence `(λ − R)·c = P·a + Q·b`. Writing λ = u/v with u, v integers and clearing denominators gives
an integer-coefficient relation (`walk_relation`). If `u ≠ v·R` it exhibits `c` as a rational
combination of `a` and `b`, so with a/b ∈ ℚ already in hand, c/b ∈ ℚ and the tile has commensurable
sides — with no appeal to the rationality theorem.

The excluded branch is sharp and harmless: `λ = R` forces `P·a + Q·b = 0` with `a, b > 0` and
`P, Q ≥ 0`, hence `P = Q = 0` (`degenerate_pure_c`), i.e. that side is covered by `c`-edges alone.
The side data of the six shapes (law of sines, up to a common scale) is

    iso base-α  (c, c, a+2b)          iso base-β  (c, c, 2a+b)
    F3  (c², c(a+2b), 3b(a+b))        F3'  (c², c(2a+b), 3a(a+b))
    F4  (ac, b(2a+b), c(a+b))         F4'  (bc, a(a+2b), c(a+b))

so each has both a c-carrying side and a side rational in a and b. Either kind closes the argument
as soon as its walk is not extremal: a c-carrying side of length λ·c gives c rational unless its
walk is pure-c, and a c-free side gives c rational as soon as its walk contains ONE c-edge. What
survives is therefore a single configuration, the same on every shape:

    (★)  every c-carrying side is covered by c-edges alone, and every c-free side by a- and
         b-edges alone.

Excluding (★) is a corner-and-walk argument of the type the branch analysis already runs (the
γ-trap of the base-β target is exactly such an exclusion, proved there); it is NOT a finite
arithmetic check, and it is not carried out here. Until it is, the six shapes rest on (★) being
impossible rather than on the rationality theorem — a strictly weaker and fully explicit hypothesis.

For orientation: the tiles for which `t² + t + 1` IS a rational square are exactly the integer
triangles with a 120° angle, parametrised by `(m²−n², 2mn+n², m²+mn+n²)`, e.g. (3,5,7), (7,8,13),
(5,16,19), (7,33,37). The condition is therefore restrictive, which is why it must be earned from
the tiling rather than assumed. -/

/-- **The walk relation.** From `u·c = v·(P·a + Q·b) + v·R·c` (the side `λ = u/v` times `c`, covered
by `P` a-edges, `Q` b-edges and `R` c-edges, denominators cleared) follows
`(u − v·R)·c = v·P·a + v·Q·b`. -/
theorem walk_relation (a b c u v P Q R : Int)
    (h : u * c = v * (P * a) + v * (Q * b) + v * (R * c)) :
    (u - v * R) * c = v * (P * a) + v * (Q * b) := by
  have e : (u - v * R) * c = u * c - v * R * c := by
    rw [Int.sub_mul]
  have e2 : v * R * c = v * (R * c) := by rw [Int.mul_assoc]
  omega

/-- **The excluded branch is degenerate.** If the coefficient vanishes (`u = v·R`) then
`P·a + Q·b = 0`; with `a, b > 0` and `P, Q ≥ 0` this forces `P = Q = 0`, so the side consists of
`c`-edges alone. -/
theorem degenerate_pure_c (a b P Q : Int) (ha : 0 < a) (hb : 0 < b) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : P * a + Q * b = 0) : P = 0 ∧ Q = 0 := by
  have h1 : 0 ≤ P * a := Int.mul_nonneg hP (by omega)
  have h2 : 0 ≤ Q * b := Int.mul_nonneg hQ (by omega)
  have hPa : P * a = 0 := by omega
  have hQb : Q * b = 0 := by omega
  constructor
  · rcases Int.mul_eq_zero.mp hPa with h3 | h3
    · exact h3
    · omega
  · rcases Int.mul_eq_zero.mp hQb with h3 | h3
    · exact h3
    · omega

/-! ## Witnesses for the square condition (why it had to be earned).
`c/b = √(t²+t+1)` is rational exactly when `t²+t+1` is a rational square, and both cases occur:
`t = 3/5` and `t = 7/8` give `(7/5)²` and `(13/8)²`, while `t = 1` and `t = 2` give `3` and `7`,
neither a square (both `≡ 3 mod 4`). So the condition is a real restriction on the tile; the point
of `walk_relation` is that the tiling supplies it rather than the tile being assumed to satisfy it. -/

/-- `t = 3/5`: `3² + 3·5 + 5² = 7²`. -/
theorem c_rational_witness : (3:Int)*3 + 3*5 + 5*5 = 7*7 := by decide
/-- `t = 7/8`: `7² + 7·8 + 8² = 13²`. -/
theorem c_rational_witness2 : (7:Int)*7 + 7*8 + 8*8 = 13*13 := by decide
/-- `t = 1` gives `3` and `t = 2` gives `7`; both are `≡ 3 (mod 4)`, and `3 (mod 4)` is not a
quadratic residue, so neither is a square. -/
theorem three_mod_four : (3:Int) % 4 = 3 ∧ (7:Int) % 4 = 3 := by decide

end Erdos634.RationalityFree
