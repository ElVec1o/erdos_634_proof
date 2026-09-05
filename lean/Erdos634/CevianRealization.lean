import Erdos634.LineParam
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Wiring `CevianCut`'s Lemma C to an actual isosceles triangle

Erdős #634.  `CevianCut.lean` proves Lemma C — `|AD|² = f²(f²−e²)²` — as pure integer algebra on
the abstract coordinates `B = (0,0)`, `D = (ef², 0)`, base `e(3f²−e²)`, legs `f³`.  The end-to-end
check flagged that nothing connects this to an *actual* target triangle of a `CongruentDissection`:
the abstract picture fixes a unit scale, while a real target's legs and base are just some positive
reals in the ratio `f³ : e(3f²−e²)`.

This file reproves Lemma C **directly for any isosceles triangle**, with the scale left free as a
parameter `k`, and with `D` constructed as an actual point via `AffineMap.lineMap` — so it composes
with real `Tri`/`CongruentDissection` data instead of bare coordinates.  The proof does not even
need the tile's angle values: it uses only the law of cosines and the isosceles hypothesis
`dist A B = dist A C`, so `AB = AC` forces `cos(∠ABC) = BC / (2·AB)`, which is *always* true of an
isosceles triangle and needs no case-specific trigonometric identity.

**Consequence for the base-β family.**  Taking `AB = AC = k·f³` (legs) and `BC = k·e(3f²−e²)`
(base), and `D = lineMap B C t` with `t = f²/(3f²−e²)` (so `BD = k·e·f²`, matching `CevianCut`'s
`D = (ef², 0)`), `isoceles_cevian_dist` gives `dist A D = k·f·(f²−e²)` exactly — Lemma C, realized.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CevianRealization

open Erdos634.Geometry EuclideanGeometry

/-- **An isosceles triangle's base angle has cosine `BC/(2·AB)`.**  From the law of cosines applied
to `dist A C = dist A B`. -/
theorem isoceles_cos (A B C : Plane) (hAB : dist A B ≠ 0) (hCB : dist C B ≠ 0)
    (hiso : dist A B = dist A C) :
    Real.cos (cornerAngle A B C) = dist C B / (2 * dist A B) := by
  have hlaw := EuclideanGeometry.law_cos A B C
  rw [cornerAngle]
  rw [← hiso] at hlaw
  have h2 : dist C B * dist C B = 2 * dist A B * dist C B * Real.cos (EuclideanGeometry.angle A B C) := by
    nlinarith [hlaw]
  rw [eq_div_iff (by positivity : (2:ℝ) * dist A B ≠ 0)]
  have hcb0 : dist C B ≠ 0 := hCB
  field_simp at h2
  linarith [h2]

/-- **The corner angle is unchanged along the ray past `D`.**  If `D = lineMap B C t` for `t > 0`,
then `∠ A B D = ∠ A B C`. -/
theorem angle_lineMap_eq (A B C : Plane) {t : ℝ} (ht : 0 < t) :
    cornerAngle A B (AffineMap.lineMap B C t) = cornerAngle A B C := by
  simp only [cornerAngle, EuclideanGeometry.angle]
  have hD : (AffineMap.lineMap B C t) -ᵥ B = t • (C -ᵥ B) := by
    rw [AffineMap.lineMap_apply]; simp
  rw [hD]
  exact InnerProductGeometry.angle_smul_right_of_pos _ _ ht

/-- **`dist B (lineMap B C t) = t * dist B C` for `t ≥ 0`.** -/
theorem dist_lineMap_base (B C : Plane) {t : ℝ} (ht : 0 ≤ t) :
    dist B (AffineMap.lineMap B C t) = t * dist B C := by
  have h := dist_lineMap_lineMap B C (0 : ℝ) t
  simp only [AffineMap.lineMap_apply_zero] at h
  rw [h, abs_of_nonneg ht]

/-- **Lemma C, realized.**  For an isosceles triangle with `dist A B = dist A C ≠ 0` and `D` on ray
`BC` at parameter `t > 0`, `dist A D ² = dist A B ² + (t · dist B C)² − (t · dist B C) · dist B C`.
This is the general isosceles-cevian identity; the base-β instantiation below specializes it. -/
theorem isoceles_cevian_sq (A B C : Plane) {t : ℝ} (ht : 0 < t)
    (hAB : dist A B ≠ 0) (hCB : dist B C ≠ 0) (hiso : dist A B = dist A C) :
    dist A (AffineMap.lineMap B C t) ^ 2
      = dist A B ^ 2 + (t * dist B C) ^ 2 - (t * dist B C) * dist B C := by
  set D := AffineMap.lineMap B C t with hDdef
  have hlaw := EuclideanGeometry.law_cos A B D
  have hangle : EuclideanGeometry.angle A B D = EuclideanGeometry.angle A B C :=
    angle_lineMap_eq A B C ht
  have hDB : dist D B = t * dist B C := by
    rw [dist_comm D B, hDdef, dist_lineMap_base B C ht.le]
  have hCB' : dist C B ≠ 0 := by rwa [dist_comm] at hCB
  have hcos : Real.cos (EuclideanGeometry.angle A B C) = dist C B / (2 * dist A B) :=
    isoceles_cos A B C hAB hCB' hiso
  rw [hangle] at hlaw
  rw [hDB] at hlaw
  rw [dist_comm C B] at hcos
  have hlaw' : dist A D * dist A D = dist A B * dist A B + (t * dist B C) * (t * dist B C)
      - 2 * dist A B * (t * dist B C) * Real.cos (EuclideanGeometry.angle A B C) := by
    linarith [hlaw]
  rw [hcos] at hlaw'
  have habeq : dist A D * dist A D = dist A B * dist A B + (t * dist B C) * (t * dist B C)
      - (t * dist B C) * dist B C := by
    rw [hlaw']; field_simp
  nlinarith [habeq]

/-- **Lemma C, for the base-β family.**  With legs `k·f³`, base `k·e(3f²−e²)`, and `D` at parameter
`t = f²/(3f²−e²)` (giving `BD = k·e·f²`), `dist A D = k·f·(f²−e²)` exactly. -/
theorem base_beta_cevian_dist (A B C : Plane) {e f k : ℝ}
    (he : 0 < e) (hf3 : e < f) (hf2 : e ^ 2 < 3 * f ^ 2) (hk : 0 < k)
    (hAB : dist A B = k * f ^ 3) (hAC : dist A C = k * f ^ 3)
    (hBC : dist B C = k * e * (3 * f ^ 2 - e ^ 2)) :
    dist A (AffineMap.lineMap B C (f ^ 2 / (3 * f ^ 2 - e ^ 2))) = k * f * (f ^ 2 - e ^ 2) := by
  have hf0 : (0:ℝ) < f := lt_trans he hf3
  have hden : (0:ℝ) < 3 * f ^ 2 - e ^ 2 := by linarith
  have ht : 0 < f ^ 2 / (3 * f ^ 2 - e ^ 2) := div_pos (by positivity) hden
  have hAB0 : dist A B ≠ 0 := by rw [hAB]; positivity
  have hCB0 : dist B C ≠ 0 := by rw [hBC]; positivity
  have hiso : dist A B = dist A C := by rw [hAB, hAC]
  have hsq := isoceles_cevian_sq A B C ht hAB0 hCB0 hiso
  rw [hAB, hBC] at hsq
  have ht_bc : f ^ 2 / (3 * f ^ 2 - e ^ 2) * (k * e * (3 * f ^ 2 - e ^ 2)) = k * e * f ^ 2 := by
    have hrw : f ^ 2 / (3 * f ^ 2 - e ^ 2) * (k * e * (3 * f ^ 2 - e ^ 2))
        = f ^ 2 * (k * e) * ((3 * f ^ 2 - e ^ 2) / (3 * f ^ 2 - e ^ 2)) := by
      ring
    rw [hrw, div_self hden.ne', mul_one]
    ring
  rw [ht_bc] at hsq
  have hrhs : (k * f ^ 3) ^ 2 + (k * e * f ^ 2) ^ 2 - (k * e * f ^ 2) * (k * e * (3 * f ^ 2 - e ^ 2))
      = (k * f * (f ^ 2 - e ^ 2)) ^ 2 := by ring
  rw [hrhs] at hsq
  have hpos : 0 ≤ dist A (AffineMap.lineMap B C (f ^ 2 / (3 * f ^ 2 - e ^ 2))) := dist_nonneg
  have hrpos : 0 ≤ k * f * (f ^ 2 - e ^ 2) := by
    have : (0:ℝ) < f ^ 2 - e ^ 2 := by nlinarith
    positivity
  nlinarith [sq_nonneg (dist A (AffineMap.lineMap B C (f ^ 2 / (3 * f ^ 2 - e ^ 2)))
    - k * f * (f ^ 2 - e ^ 2)), hsq]

end Erdos634.CevianRealization
