import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Erdos634.Dissection

/-!
# The angle threshold: closed forms for the tile's three cosines

`lem:anglethreshold` records that the `e = 1` tile `(a,b,c) = (f, f²-1, f²)` has

  `cos α = (2f²-1)/(2f²)`,  `cos β = (3f²-1)/(2f³)`,  `cos γ = -1/(2f)`.

`Frontier.cos_alpha_closed` covered only the `α` line, and only as a cross-multiplied polynomial
identity — algebra about the law-of-cosines quotient, not a statement about an angle.  Here the
bridge is made: `cos_of_sides` solves Mathlib's `EuclideanGeometry.law_cos` for the cosine, so the
three closed forms below are about `cornerAngle` itself.

The remaining clause of `lem:anglethreshold` — that condition (P4) "is therefore the statement that
the uncovered region never acquires a corner sharper than the tile's own sharpest angle" — is a
restatement of (P4), and the uncovered region is not an object in this development.  That clause is
what keeps the lemma from VERIFIED; the three identities are now theorems.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.AngleThreshold

open EuclideanGeometry Erdos634.Geometry

/-- **From side lengths to the cosine of a corner.**  Solving the law of cosines at `q`. -/
theorem cos_of_sides (p q r : Plane) (hp : dist p q ≠ 0) (hr : dist r q ≠ 0) :
    Real.cos (cornerAngle p q r)
      = (dist p q ^ 2 + dist r q ^ 2 - dist p r ^ 2) / (2 * dist p q * dist r q) := by
  have h := EuclideanGeometry.law_cos p q r
  rw [cornerAngle]
  field_simp
  linarith [h]

/-- **`cos γ = -1/(2f)`**, at the corner facing the longest side `c = f²`. -/
theorem cos_gamma_closed (p q r : Plane) (f : ℝ) (hf : 1 < f)
    (ha : dist p q = f) (hb : dist r q = f ^ 2 - 1) (hc : dist p r = f ^ 2) :
    Real.cos (cornerAngle p q r) = -1 / (2 * f) := by
  have hf0 : (0:ℝ) < f := lt_trans zero_lt_one hf
  have hb0 : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  rw [cos_of_sides p q r (by rw [ha]; positivity) (by rw [hb]; exact ne_of_gt hb0),
    ha, hb, hc]
  field_simp
  ring

/-- **`cos β = (3f²-1)/(2f³)`**, at the corner facing the middle side `b = f²-1`. -/
theorem cos_beta_closed (p q r : Plane) (f : ℝ) (hf : 1 < f)
    (ha : dist p q = f) (hc : dist r q = f ^ 2) (hb : dist p r = f ^ 2 - 1) :
    Real.cos (cornerAngle p q r) = (3 * f ^ 2 - 1) / (2 * f ^ 3) := by
  have hf0 : (0:ℝ) < f := lt_trans zero_lt_one hf
  rw [cos_of_sides p q r (by rw [ha]; positivity) (by rw [hc]; positivity), ha, hc, hb]
  field_simp
  ring

/-- **`cos α = (2f²-1)/(2f²)`**, at the corner facing the shortest side `a = f`. -/
theorem cos_alpha_closed (p q r : Plane) (f : ℝ) (hf : 1 < f)
    (hb : dist p q = f ^ 2 - 1) (hc : dist r q = f ^ 2) (ha : dist p r = f) :
    Real.cos (cornerAngle p q r) = (2 * f ^ 2 - 1) / (2 * f ^ 2) := by
  have hf0 : (0:ℝ) < f := lt_trans zero_lt_one hf
  have hb0 : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  rw [cos_of_sides p q r (by rw [hb]; exact ne_of_gt hb0) (by rw [hc]; positivity), hb, hc, ha]
  field_simp
  ring

/-- **The hypotheses above are not vacuous.**  Sides `f`, `f²-1`, `f²` satisfy the strict triangle
inequality exactly when `f > 1`, so a triangle with those side lengths exists.  (This establishes
satisfiability of the side conditions; it does not construct explicit coordinates.) -/
theorem sides_form_a_triangle (f : ℝ) (hf : 1 < f) :
    f + (f ^ 2 - 1) > f ^ 2 ∧ (f ^ 2 - 1) + f ^ 2 > f ∧ f + f ^ 2 > f ^ 2 - 1 := by
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

end Erdos634.AngleThreshold
