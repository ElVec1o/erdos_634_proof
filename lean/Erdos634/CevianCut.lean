import Mathlib.Tactic

/-!
# Lemma C: the cevian `AD` has length exactly `K·b`, and `ABD` is the tile scaled by `f`

Erdős #634, base-β family. Tile `(a,b,c) = (ef, f²−e², f²)`, `gcd(e,f)=1`; target isosceles with
legs `f³` and base `e(3f²−e²)`, base angles `β`, apex `3α`.

Put the base on the `x`-axis, `B = (0,0)`, and let `A` be the apex, `D = (e f², 0)`. Then

* `|AD| = f(f²−e²) = K·b` **exactly**, where `K = f` is the constant of the essential-segment
  length bound (`jb = ua+vc ⟹ f ∣ j`); and
* `BD : AD : AB = ef² : f(f²−e²) : f³ = f·(a : b : c)`, so **`ABD` is the tile scaled by `f`**.

This is the single geometric fact the forced-double-cut argument rests on, and it is pure integer
algebra once the coordinates are written down: with `4h² = 4·leg² − base²` for the apex height,

  `4|AD|² = (base − 2ef²)² + 4·leg² − base²`,

and the identity below evaluates that to `4f²(f²−e²)²`.

Stated over `ℤ` so that no square roots or division appear; the geometric reading is recorded in the
statement names. Axiom-clean; no `sorry`.
-/

namespace Erdos634.CevianCut

variable (e f : ℤ)

/-- The target's base length, `e(3f² − e²)`. -/
def baseLen : ℤ := e * (3 * f ^ 2 - e ^ 2)

/-- The target's leg length, `f³`. -/
def legLen : ℤ := f ^ 3

/-- The tile's three sides. -/
def sideA : ℤ := e * f
def sideB : ℤ := f ^ 2 - e ^ 2
def sideC : ℤ := f ^ 2

/-- **The foot `D` sits at `x = e f²`, and `base − 2·e f² = e(f² − e²)`.** -/
theorem base_sub_twice_foot : baseLen e f - 2 * (e * f ^ 2) = e * sideB e f := by
  simp only [baseLen, sideB]; ring

/-- **Lemma C, in integer form.**  `4|AD|² = (base − 2ef²)² + 4·leg² − base²` evaluates to
`4f²(f²−e²)²`, i.e. `|AD| = f(f²−e²) = f · b`. -/
theorem four_AD_sq :
    (baseLen e f - 2 * (e * f ^ 2)) ^ 2 + 4 * (legLen f) ^ 2 - (baseLen e f) ^ 2
      = 4 * (f * sideB e f) ^ 2 := by
  simp only [baseLen, legLen, sideB]; ring

/-- **`|AD|² = (f·b)²`**, the same statement with the factor 4 cleared. -/
theorem AD_sq_eq : ((baseLen e f - 2 * (e * f ^ 2)) ^ 2 + 4 * (legLen f) ^ 2
    - (baseLen e f) ^ 2) / 4 = (f * sideB e f) ^ 2 := by
  rw [four_AD_sq]; omega

/-- **`ABD` is the tile scaled by `f`** — the three side ratios, exactly. -/
theorem cut_triangle_is_scaled_tile :
    e * f ^ 2 = f * sideA e f ∧
    f * sideB e f = f * sideB e f ∧
    legLen f = f * sideC f := by
  refine ⟨by simp only [sideA]; ring, rfl, by simp only [legLen, sideC]; ring⟩

/-- **Arithmetic bookkeeping of the forced double cut at `e = 1`.**  Each of the two outer
triangles is the tile scaled by `f` (`cut_triangle_is_scaled_tile`), hence carries `f²` tiles by
area; the middle triangle then carries `N - 2f² = f² - 1` tiles.  This records only the count
identity — that the middle piece admits no such tiling is *not* proved here. -/
theorem decomposition_count : f ^ 2 + (f ^ 2 - 1) + f ^ 2 = 3 * f ^ 2 - 1 := by ring

end Erdos634.CevianCut
