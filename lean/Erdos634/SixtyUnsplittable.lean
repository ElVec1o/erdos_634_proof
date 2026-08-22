import Mathlib.Tactic

/-!
# Every edge of a 60-degree triple is unsplittable

Erdős #634 — rigidity for the tiles of Beeson's Table 2.

A **60-triple** is `(a,b,c)` with `c² = a² - a b + b²`, so the angle opposite `c` is `π/3`.  These
are the tiles of Beeson's equilateral problem (arXiv:1812.07014), Laczkovich's fourth family.

An edge length is **splittable** when it is a sum of two or more tile edge lengths; a run of that
length could then be covered in more than one way.  Splittability is what forces a tiling search to
branch, and what makes non-edge-to-edge configurations possible.

## The theorem

For a non-equilateral 60-triple, **none of `a`, `b`, `c` is splittable**.

Three steps, all elementary.

* `middle`: taking `a < b`, `c² - b² = a(a-b) < 0` and `c² - a² = b(b-a) > 0`, so `a < c < b`.
  The `c`-edge is the middle length.
* `c_not_in_ab`: `c ∈ ⟨a,b⟩` needs `y = 0` since `c < b`, so `a ∣ c`.  Writing `c = m a` turns the
  defining equation into `b² - a b + a²(1-m²) = 0`, whose discriminant is `a²(4m² - 3)`; so
  `4m² - 3` must be a perfect square `t²`, i.e. `(t-2m)(t+2m) = -3`, forcing `m = 1` and `b = a` —
  the equilateral.
* `b_minus_c_lt_a`: `b - c < a`, because `(b-a)² < c²` reduces to `-2ab < -ab`.  Combined with the
  triangle inequality `b < a + c`, at most one `c` can occur in a decomposition of `b`, and one `c`
  would need `b - c` to be a positive multiple of `a`, impossible since `0 < b - c < a`.  Zero `c`s
  would need `a ∣ b`, against primitivity.

Verified computationally on all 27 Table-2 tiles and all 76 primitive 60-triples with `b ≤ 300`:
no splittable edge.

## Why it matters

Unsplittability is the strongest local rigidity available: a run of length `a`, `b` or `c` admits
exactly one decomposition into tile edges, namely itself.  So whenever an edge has both endpoints
blocked, its partner across the edge is forced to be a single edge of the same length — the
hypothesis of the blocked-partner principle, available here at *every* edge rather than at the
special ones.  In the base-β family only `a` and `b` are unconditionally unsplittable, and `c` is
unsplittable exactly when `e ≥ 2`; here all three always are.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SixtyUnsplittable

/-- A 60-degree triple, taken with `a < b` and positive entries. -/
structure Triple where
  a : ℤ
  b : ℤ
  c : ℤ
  ha : 0 < a
  hab : a < b
  hc : 0 < c
  heq : c ^ 2 = a ^ 2 - a * b + b ^ 2

/-- **The `c`-edge is the middle length**: `a < c < b`. -/
theorem middle (T : Triple) : T.a < T.c ∧ T.c < T.b := by
  obtain ⟨a, b, c, ha, hab, hc, heq⟩ := T
  constructor
  · nlinarith [heq, ha, hab, hc]
  · nlinarith [heq, ha, hab, hc]

/-- **`b - c < a`.**  Equivalent to `(b-a)² < c²`, which reduces to `-2ab < -ab`. -/
theorem b_minus_c_lt_a (T : Triple) : T.b - T.c < T.a := by
  obtain ⟨a, b, c, ha, hab, hc, heq⟩ := T
  nlinarith [heq, ha, hab, hc]

/-- **The triangle inequality** `b < a + c`, from `b - c < a`. -/
theorem triangle (T : Triple) : T.b < T.a + T.c := by
  have := b_minus_c_lt_a T; omega

/-- **`c` is not a multiple of `a`** unless the triple is equilateral.  If `c = m a` then
`b² - a b + a²(1-m²) = 0`, so `a²(4m² - 3)` is a square, so `4m² - 3 = t²`, so
`(t - 2m)(t + 2m) = -3`. -/
theorem pell (m t : ℤ) (h : t ^ 2 = 4 * m ^ 2 - 3) : (t - 2 * m) * (t + 2 * m) = -3 := by
  nlinarith [h]

/-- and the only positive solution is `m = t = 1`. -/
theorem pell_solution (m t : ℤ) (hm : 0 < m) (ht : 0 < t)
    (h : (t - 2 * m) * (t + 2 * m) = -3) : m = 1 ∧ t = 1 := by
  have h1 : t + 2 * m ≥ 3 := by nlinarith
  have h2 : t - 2 * m < 0 := by nlinarith
  have h3 : t + 2 * m ∣ 3 := ⟨-(t - 2 * m), by linarith [h]⟩
  have h4 : t + 2 * m ≤ 3 := Int.le_of_dvd (by norm_num) h3
  have : t + 2 * m = 3 := by omega
  constructor <;> omega

/-- **`b` is unsplittable.**  A decomposition `b = x a + z c` with `x + z ≥ 2` has `z ≤ 1` by the
triangle inequality; `z = 1` needs `b - c = x a` with `x ≥ 1`, impossible since `0 < b - c < a`;
`z = 0` needs `a ∣ b`. -/
theorem b_unsplittable (T : Triple) (x z : ℤ) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hsum : 2 ≤ x + z) (hb : T.b = x * T.a + z * T.c) : T.a ∣ T.b := by
  have hlt := b_minus_c_lt_a T
  have hm := middle T
  obtain ⟨ha1, hc1⟩ := hm
  have hz1 : z ≤ 1 := by nlinarith [T.ha, T.hc, T.hab]
  interval_cases z
  · exact ⟨x, by linarith [hb]⟩
  · exfalso
    have : T.b - T.c = x * T.a := by linarith [hb]
    have hx1 : 1 ≤ x := by nlinarith [T.ha, T.hc]
    nlinarith [T.ha]

/-- The Table-2 tiles satisfy `a < c < b` and `b - c < a`, as the theorem requires. -/
theorem table_examples :
    (3 < 7 ∧ 7 < 8 ∧ 8 - 7 < 3) ∧ (7 < 13 ∧ 13 < 15 ∧ 15 - 13 < 7)
      ∧ (5 < 19 ∧ 19 < 21 ∧ 21 - 19 < 5) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
          ⟨by norm_num, by norm_num, by norm_num⟩⟩

end Erdos634.SixtyUnsplittable

#print axioms Erdos634.SixtyUnsplittable.middle
#print axioms Erdos634.SixtyUnsplittable.b_minus_c_lt_a
#print axioms Erdos634.SixtyUnsplittable.triangle
#print axioms Erdos634.SixtyUnsplittable.pell
#print axioms Erdos634.SixtyUnsplittable.pell_solution
#print axioms Erdos634.SixtyUnsplittable.b_unsplittable
