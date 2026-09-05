import Erdos634.CevianRealization
import Erdos634.AngleThreshold

/-!
# The target's shape theorem, general in `(e,f)`

Erdős #634.  `CevianRealization.base_beta_cevian_dist` needs, as hypotheses, that an actual target
triangle has legs `k·f³` and base `k·e(3f²−e²)` for some real `k > 0`.  Nothing in the corpus derived
these side lengths for a real target — `CornerAnglePermTarget.htarget_of_isosceles` gives the
target's *angle* shape (base corners `β`, apex `3α`) but stops there.  This file supplies the
missing step, **general in `(e,f)`** (not only `e = 1`):

1.  `cos_beta_of_sides`: the tile's own law of cosines, generalizing `AngleThreshold.cos_beta_closed`
    from `e = 1` to every `(e,f)` — `cos β = e(3f²−e²)/(2f³)` when a triangle has sides
    `a = ef`, `b = f²−e²`, `c = f²` placed with `β` opposite `b`.
2.  `isosceles_of_equal_base_angles`: a general triangle fact — if a triangle presents the *same*
    angle at two of its vertices, the sides opposite those vertices are equal.  (Via Mathlib's law of
    sines twice; needs only that the third angle's sine is nonzero.)
3.  `target_shape`: composing — a target whose two base corners both present the tile's angle `β`
    (with the tile's own sides `ef, f²−e², f²` witnessed on its model) has `dist A B = dist A C`
    and, setting `k := dist A B / f³`, satisfies `dist A B = k·f³` and `dist B C = k·e(3f²−e²)`
    exactly — the hypotheses `CevianRealization.base_beta_cevian_dist` asks for.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TargetShape

open Erdos634.Geometry Erdos634.AngleThreshold Erdos634.CevianRealization

/-! ## 1. The tile's `cos β`, general in `(e,f)` -/

/-- **`cos β = e(3f²−e²)/(2f³)`**, general in `(e,f)` (generalizes `cos_beta_closed`'s `e = 1`
case). Law of cosines at the corner facing side `b = f² − e²`. -/
theorem cos_beta_of_sides (p q r : Plane) (e f : ℝ) (he : 0 < e) (hef : e < f)
    (ha : dist p q = e * f) (hc : dist r q = f ^ 2) (hb : dist p r = f ^ 2 - e ^ 2) :
    Real.cos (cornerAngle p q r) = e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3) := by
  have hf0 : (0:ℝ) < f := lt_trans he hef
  rw [Erdos634.AngleThreshold.cos_of_sides p q r
    (by rw [ha]; positivity) (by rw [hc]; positivity), ha, hc, hb]
  field_simp
  ring

/-! ## 2. Equal base angles force equal opposite sides -/

/-- **A triangle with equal angles at two vertices is isosceles.**  If `∠ABC = ∠ACB` and the
apex angle `∠BAC` has nonzero sine, then `dist A B = dist A C`. -/
theorem isosceles_of_equal_base_angles (A B C : Plane)
    (hsin : Real.sin (cornerAngle B A C) ≠ 0)
    (heq : cornerAngle A B C = cornerAngle A C B) :
    dist A B = dist A C := by
  have h1 : Real.sin (cornerAngle B A C) * dist A C = Real.sin (cornerAngle C B A) * dist C B := by
    simpa [cornerAngle] using EuclideanGeometry.law_sin B A C
  have h2 : Real.sin (cornerAngle C A B) * dist A B = Real.sin (cornerAngle B C A) * dist B C := by
    simpa [cornerAngle] using EuclideanGeometry.law_sin C A B
  have hcomm1 : cornerAngle C B A = cornerAngle A B C := by
    simp only [cornerAngle]; exact EuclideanGeometry.angle_comm _ _ _
  have hcomm2 : cornerAngle B C A = cornerAngle A C B := by
    simp only [cornerAngle]; exact EuclideanGeometry.angle_comm _ _ _
  have hcomm3 : cornerAngle C A B = cornerAngle B A C := by
    simp only [cornerAngle]; exact EuclideanGeometry.angle_comm _ _ _
  rw [hcomm1, heq, dist_comm C B] at h1
  rw [hcomm3, hcomm2] at h2
  -- `h1 : sin(∠BAC) * dist A C = sin(∠ACB) * dist B C`
  -- `h2 : sin(∠BAC) * dist A B = sin(∠ACB) * dist B C`
  have : Real.sin (cornerAngle B A C) * dist A C = Real.sin (cornerAngle B A C) * dist A B := by
    rw [h1, h2]
  exact (mul_left_cancel₀ hsin this).symm

/-! ## 3. The target's shape, composed -/

/-- **The target's shape theorem, general in `(e,f)`.**  A target with base corners both presenting
the tile's angle `β` (witnessed via the model's own sides `ef, f²−e², f²`) has `dist A B = dist A C`,
and with `k := dist A B / f³ > 0` satisfies exactly `CevianRealization.base_beta_cevian_dist`'s
hypotheses: `dist A B = k·f³`, `dist A C = k·f³`, `dist B C = k·e(3f²−e²)`. -/
theorem target_shape (A B C : Plane) (e f : ℝ) (he : 0 < e) (hef : e < f)
    -- the tile's `β`, witnessed by its own three sides at some triangle `p q r`
    (β : ℝ) (p q r : Plane)
    (hpq : dist p q = e * f) (hrq : dist r q = f ^ 2) (hpr : dist p r = f ^ 2 - e ^ 2)
    (hβ : cornerAngle p q r = β)
    -- the target presents `β` at both base corners
    (hB : cornerAngle A B C = β) (hC : cornerAngle A C B = β)
    (hsin : Real.sin (cornerAngle B A C) ≠ 0) (hAB0 : 0 < dist A B)
    (hBC0 : dist B C ≠ 0) :
    ∃ k : ℝ, 0 < k ∧
      dist A B = k * f ^ 3 ∧ dist A C = k * f ^ 3 ∧ dist B C = k * e * (3 * f ^ 2 - e ^ 2) := by
  have hf0 : (0:ℝ) < f := lt_trans he hef
  have hiso : dist A B = dist A C := isosceles_of_equal_base_angles A B C hsin (hB.trans hC.symm)
  have hcosβ : Real.cos β = e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3) := by
    rw [← hβ]; exact cos_beta_of_sides p q r e f he hef hpq hrq hpr
  have hcosβ' : Real.cos (cornerAngle A B C) = e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3) := by
    rw [hB]; exact hcosβ
  have hABne : dist A B ≠ 0 := hAB0.ne'
  have hCBne : dist C B ≠ 0 := by rwa [dist_comm] at hBC0
  have hiso_cos := isoceles_cos A B C hABne hCBne hiso
  rw [hcosβ'] at hiso_cos
  -- `hiso_cos : e(3f²−e²)/(2f³) = dist C B / (2 dist A B)`
  refine ⟨dist A B / f ^ 3, div_pos hAB0 (by positivity), ?_, ?_, ?_⟩
  · field_simp
  · rw [← hiso]; field_simp
  · have hCB : dist C B = e * (3 * f ^ 2 - e ^ 2) / f ^ 3 * dist A B := by
      have hne1 : (2:ℝ) * f ^ 3 ≠ 0 := by positivity
      have hne2 : (2:ℝ) * dist A B ≠ 0 := by positivity
      field_simp at hiso_cos
      field_simp
      linarith [hiso_cos]
    rw [dist_comm C B] at hCB
    rw [hCB]; ring

end Erdos634.TargetShape
