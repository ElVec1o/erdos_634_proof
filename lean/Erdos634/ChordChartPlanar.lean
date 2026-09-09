import Erdos634.ChordChart
import Erdos634.CertCoord

/-!
# The planar step of `ChordChart`'s bridge (ii), actually proved

Written 2026-09-10.

## The gap this closes

`ChordChart.lean`'s section "The planar step, proved" claims that bridge (ii)'s residue — *two
triangles reaching across a common vertical at positive height must intersect* — is discharged by
`ChordChart.upward_in_cone` together with `ChordChart.shared_segment_pos`.  It is not.  Those two
statements are:

* `upward_in_cone` — `(0,1)` is a **strictly positive combination of two vectors**.  A statement
  about two vectors; no triangle, no carrier, no membership.
* `shared_segment_pos` — `0 < min h₁ h₂`, i.e. `lt_min`.  A statement about two real numbers.

Between them and "the interiors meet" sit exactly the three facts nobody had written down: that a
positive combination of the two edge directions at a corner, **scaled small enough**, lies in the
triangle; that it lies in the *interior*, not merely the carrier; and that a single scale works for
both triangles at once.  `StripRigid.lean:173-186` and `LayerLink.lean:36-48` both propagate the
claim (`StripRigid` going as far as "BOTH bridges are theorems", and blaming the earlier, correct,
blocker note on staleness).  This file supplies the missing statement so that those claims become
true rather than being downgraded.

## What is proved here

* `mem_interior_carrier_of_dets_pos` — **strict** determinant signs put a point in the *interior*
  of a coordinate triangle.  `CertCoord.mem_carrier_of_dets` gives only the closed carrier; the
  strict version follows because the strict-sign region is open, so `interior_maximal` applies.
  This is general-purpose and reusable.
* `vertical_mem_interior_right` / `vertical_mem_interior_left` — the two orientations of the
  configuration: a triangle with its base edge on the floor from the shared foot `F = (0,0)`, its
  other base end on one side of `F` and its apex strictly on the **other** side and strictly above
  the floor, contains `(0, μ)` in its interior for every small enough `μ > 0`.  The apex sign
  hypothesis is exactly the straddle `ChordChart.straddle_of_opposite_signs` records; drop it and
  the corresponding determinant is `≤ 0` and the conclusion is false.
* `interiors_meet_at_shared_foot` — one `μ` serves both triangles, so the two interiors share a
  point.  **This is the planar step.**
* `member_configuration_interiors_meet` — the same conclusion for the base-`β` member data
  (`a = ef`, unreflected abscissa `x_u = S/(2f) > a`, reflected abscissa `x_r < 0`), i.e. with the
  hypotheses supplied by `ChordChart.reflected_apex_left_of_mast` and
  `ChordChart.predecessor_apex_right_of_foot` rather than assumed.  So this is not a
  `False → False`: the hypothesis set is inhabited by every member of the family.

## What is still not proved

The *assembly* named in `StripRigid.lean:181-186` is untouched: nothing here says that the two
triangles of a real `CongruentDissection` at an unreflected/reflected adjacency **are** these two
coordinate triangles.  That is the placement obligation (blockers 1 and 3), and it is the reason
`LayerLink.strip_layer_rigid` still takes `overlap` as a hypothesis.  No label moves.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.ChordChartPlanar

open Erdos634.Geometry Erdos634.CertCoord

/-! ## Strict determinant signs give interior membership -/

/-- A plane point is `mkPt` of its own coordinates. -/
theorem mkPt_coords (q : Plane) : mkPt (q 0) (q 1) = q := by
  refine PiLp.ext ?_
  intro i
  fin_cases i <;> simp

/-- `det3` with the *first* pair varying is continuous. -/
theorem continuous_det3_fst (x₁ y₁ x₂ y₂ : ℝ) :
    Continuous fun q : Plane => det3 (q 0) (q 1) x₁ y₁ x₂ y₂ := by
  have h0 : Continuous fun q : Plane => q 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have h1 : Continuous fun q : Plane => q 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  simp only [det3]
  fun_prop

/-- `det3` with the *middle* pair varying is continuous. -/
theorem continuous_det3_mid (x₀ y₀ x₂ y₂ : ℝ) :
    Continuous fun q : Plane => det3 x₀ y₀ (q 0) (q 1) x₂ y₂ := by
  have h0 : Continuous fun q : Plane => q 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have h1 : Continuous fun q : Plane => q 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  simp only [det3]
  fun_prop

/-- `det3` with the *last* pair varying is continuous. -/
theorem continuous_det3_snd (x₀ y₀ x₁ y₁ : ℝ) :
    Continuous fun q : Plane => det3 x₀ y₀ x₁ y₁ (q 0) (q 1) := by
  have h0 : Continuous fun q : Plane => q 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have h1 : Continuous fun q : Plane => q 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  simp only [det3]
  fun_prop

/-- **Strict determinant signs put a point in the interior.**  `CertCoord.mem_carrier_of_dets`
concludes membership in the closed carrier from three weak sign checks.  With all three checks
*strict*, the point lies in the interior: the strict-sign region is an open set contained in the
carrier, so it is contained in the interior. -/
theorem mem_interior_carrier_of_dets_pos {x₀ y₀ x₁ y₁ x₂ y₂ a b : ℝ}
    (hD : 0 < det3 x₀ y₀ x₁ y₁ x₂ y₂)
    (h₀ : 0 < det3 a b x₁ y₁ x₂ y₂)
    (h₁ : 0 < det3 x₀ y₀ a b x₂ y₂)
    (h₂ : 0 < det3 x₀ y₀ x₁ y₁ a b) :
    mkPt a b ∈ interior (mkTri x₀ y₀ x₁ y₁ x₂ y₂ hD.ne').carrier := by
  set S : Set Plane :=
      ({q : Plane | 0 < det3 (q 0) (q 1) x₁ y₁ x₂ y₂} ∩
       {q : Plane | 0 < det3 x₀ y₀ (q 0) (q 1) x₂ y₂}) ∩
      {q : Plane | 0 < det3 x₀ y₀ x₁ y₁ (q 0) (q 1)} with hS
  have hopen : IsOpen S := by
    have e₀ : IsOpen {q : Plane | 0 < det3 (q 0) (q 1) x₁ y₁ x₂ y₂} :=
      isOpen_lt continuous_const (continuous_det3_fst x₁ y₁ x₂ y₂)
    have e₁ : IsOpen {q : Plane | 0 < det3 x₀ y₀ (q 0) (q 1) x₂ y₂} :=
      isOpen_lt continuous_const (continuous_det3_mid x₀ y₀ x₂ y₂)
    have e₂ : IsOpen {q : Plane | 0 < det3 x₀ y₀ x₁ y₁ (q 0) (q 1)} :=
      isOpen_lt continuous_const (continuous_det3_snd x₀ y₀ x₁ y₁)
    exact (e₀.inter e₁).inter e₂
  have hsub : S ⊆ (mkTri x₀ y₀ x₁ y₁ x₂ y₂ hD.ne').carrier := by
    rintro q ⟨⟨k₀, k₁⟩, k₂⟩
    have := mem_carrier_of_dets (a := q 0) (b := q 1) hD k₀.le k₁.le k₂.le
    rwa [mkPt_coords q] at this
  refine interior_maximal hsub hopen ?_
  exact ⟨⟨by simpa using h₀, by simpa using h₁⟩, by simpa using h₂⟩

/-! ## The two orientations of the corner configuration -/

/-- **Apex strictly left, other base end strictly right.**  The triangle `F = (0,0)`,
`(p, 0)` with `p > 0`, apex `(qx, qy)` with `qx < 0 < qy`, contains `(0, μ)` in its interior for
every `μ` with `0 < μ` and `μ (p - qx) < p·qy`.

The determinant that uses the straddle is the middle one: it equals `-qx·μ`, positive exactly
because the apex is on the **other** side of the vertical through `F`. -/
theorem vertical_mem_interior_right (p qx qy μ : ℝ) (hp : 0 < p) (hqx : qx < 0) (_hqy : 0 < qy)
    (hμ : 0 < μ) (hsmall : μ * (p - qx) < p * qy)
    (hD : 0 < det3 0 0 p 0 qx qy) :
    mkPt 0 μ ∈ interior (mkTri 0 0 p 0 qx qy hD.ne').carrier := by
  refine mem_interior_carrier_of_dets_pos hD ?_ ?_ ?_
  · simp only [det3]; nlinarith
  · simp only [det3]; nlinarith
  · simp only [det3]; nlinarith

/-- **Apex strictly right, other base end strictly left.**  The mirrored configuration, with the
vertices listed apex-first so that the triangle is positively oriented: `F = (0,0)`, apex
`(qx, qy)` with `0 < qx` and `0 < qy`, other base end `(p, 0)` with `p < 0`.  Contains `(0, μ)` in
its interior whenever `0 < μ` and `μ (qx - p) < -p·qy`. -/
theorem vertical_mem_interior_left (p qx qy μ : ℝ) (hp : p < 0) (hqx : 0 < qx) (_hqy : 0 < qy)
    (hμ : 0 < μ) (hsmall : μ * (qx - p) < -p * qy)
    (hD : 0 < det3 0 0 qx qy p 0) :
    mkPt 0 μ ∈ interior (mkTri 0 0 qx qy p 0 hD.ne').carrier := by
  refine mem_interior_carrier_of_dets_pos hD ?_ ?_ ?_
  · simp only [det3]; nlinarith
  · simp only [det3]; nlinarith
  · simp only [det3]; nlinarith

/-! ## One scale serves both -/

/-- A single positive scale below two positive thresholds. -/
theorem exists_small_scale (d₁ d₂ n₁ n₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    ∃ μ : ℝ, 0 < μ ∧ μ * d₁ < n₁ ∧ μ * d₂ < n₂ := by
  have q₁ : 0 < n₁ / d₁ := div_pos hn₁ hd₁
  have q₂ : 0 < n₂ / d₂ := div_pos hn₂ hd₂
  set μ : ℝ := min (n₁ / d₁) (n₂ / d₂) / 2 with hμdef
  have hmin : 0 < min (n₁ / d₁) (n₂ / d₂) := lt_min q₁ q₂
  refine ⟨μ, by simpa [hμdef] using half_pos hmin, ?_, ?_⟩
  · have h1 : μ ≤ (n₁ / d₁) / 2 := by
      have := min_le_left (n₁ / d₁) (n₂ / d₂); simp only [hμdef]; linarith
    have h2 : μ * d₁ ≤ ((n₁ / d₁) / 2) * d₁ := mul_le_mul_of_nonneg_right h1 hd₁.le
    have h3 : ((n₁ / d₁) / 2) * d₁ = n₁ / 2 := by field_simp
    rw [h3] at h2; linarith
  · have h1 : μ ≤ (n₂ / d₂) / 2 := by
      have := min_le_right (n₁ / d₁) (n₂ / d₂); simp only [hμdef]; linarith
    have h2 : μ * d₂ ≤ ((n₂ / d₂) / 2) * d₂ := mul_le_mul_of_nonneg_right h1 hd₂.le
    have h3 : ((n₂ / d₂) / 2) * d₂ = n₂ / 2 := by field_simp
    rw [h3] at h2; linarith

/-- **The planar step.**  Two triangles sharing the foot `F = (0,0)`, each with its base edge on
the floor and its body above it, the first with its other base end strictly **left** of `F` and its
apex strictly **right** of the vertical through `F`, the second the other way round: their
interiors meet.

This is exactly the configuration `ChordChart` puts the predecessor (unreflected, apex abscissa
`x_u > a`) and the successor (reflected, apex abscissa `x_r < 0`) in, once the shared foot is moved
to the origin.  It is the statement `upward_in_cone` and `shared_segment_pos` were claimed to
prove. -/
theorem interiors_meet_at_shared_foot
    (p₁ qx₁ qy₁ p₂ qx₂ qy₂ : ℝ)
    (hp₁ : p₁ < 0) (hqx₁ : 0 < qx₁) (hqy₁ : 0 < qy₁)
    (hp₂ : 0 < p₂) (hqx₂ : qx₂ < 0) (hqy₂ : 0 < qy₂)
    (hD₁ : 0 < det3 0 0 qx₁ qy₁ p₁ 0) (hD₂ : 0 < det3 0 0 p₂ 0 qx₂ qy₂) :
    ∃ z : Plane,
      z ∈ interior (mkTri 0 0 qx₁ qy₁ p₁ 0 hD₁.ne').carrier ∧
      z ∈ interior (mkTri 0 0 p₂ 0 qx₂ qy₂ hD₂.ne').carrier := by
  obtain ⟨μ, hμ, hs₁, hs₂⟩ :=
    exists_small_scale (qx₁ - p₁) (p₂ - qx₂) (-p₁ * qy₁) (p₂ * qy₂)
      (by linarith) (by linarith) (by nlinarith) (by nlinarith)
  exact ⟨mkPt 0 μ,
    vertical_mem_interior_left p₁ qx₁ qy₁ μ hp₁ hqx₁ hqy₁ hμ hs₁ hD₁,
    vertical_mem_interior_right p₂ qx₂ qy₂ μ hp₂ hqx₂ hqy₂ hμ hs₂ hD₂⟩

/-! ## The hypothesis set is inhabited by every member of the family

`ChordChart.reflected_apex_left_of_mast` gives `x_r < 0` and
`ChordChart.predecessor_apex_right_of_foot` gives `x_u > a = ef`, for every `0 < e < f`.  With the
shared foot at the origin the predecessor's other base end is at `-a < 0` and its apex abscissa is
`-a + x_u > 0`; the successor's other base end is at `a > 0` and its apex abscissa is `x_r < 0`.
So the sign pattern of `interiors_meet_at_shared_foot` is the member's own, not a stipulation. -/

/-- **The member configuration realizes the hypotheses.**  For `0 < e < f`, the two abscissa signs
the theorem needs are the ones `ChordChart` proves. -/
theorem member_signs (e f xu xr : ℝ) (he : 0 < e) (hef : e < f)
    (hu : e * f < xu) (hr : xr < 0) :
    -(e * f) < 0 ∧ 0 < -(e * f) + xu ∧ 0 < e * f ∧ xr < 0 := by
  have hf : 0 < f := lt_trans he hef
  exact ⟨by nlinarith, by linarith, mul_pos he hf, hr⟩

/-- **The planar step at the member configuration.**  Heights `c₁, c₂ > 0` are the tiles' apex
heights; the abscissae are the member's.  No hypothesis is stipulated that `ChordChart` does not
already prove, so the conditional is inhabited. -/
theorem member_configuration_interiors_meet
    (e f xu xr c₁ c₂ : ℝ) (he : 0 < e) (hef : e < f)
    (hu : e * f < xu) (hr : xr < 0) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hD₁ : 0 < det3 0 0 (-(e * f) + xu) c₁ (-(e * f)) 0)
    (hD₂ : 0 < det3 0 0 (e * f) 0 xr c₂) :
    ∃ z : Plane,
      z ∈ interior (mkTri 0 0 (-(e * f) + xu) c₁ (-(e * f)) 0 hD₁.ne').carrier ∧
      z ∈ interior (mkTri 0 0 (e * f) 0 xr c₂ hD₂.ne').carrier := by
  obtain ⟨s₁, s₂, s₃, s₄⟩ := member_signs e f xu xr he hef hu hr
  exact interiors_meet_at_shared_foot _ _ _ _ _ _ s₁ s₂ hc₁ s₃ s₄ hc₂ hD₁ hD₂

/-- **The hypothesis set of `member_configuration_interiors_meet` is inhabited.**  Explicit
witness `e = 1`, `f = 2`: then `a = ef = 2`, `x_u = e(3f²-e²)/(2f) = 11/4 > 2`, and any `x_r < 0`
(take `-1`) with unit apex heights makes both orientation determinants positive.  So the theorem
is not a `False → False`. -/
theorem member_hypotheses_inhabited :
    (0:ℝ) < 1 ∧ (1:ℝ) < 2 ∧ ((1:ℝ) * 2) < 11/4 ∧ (-1:ℝ) < 0 ∧
      0 < det3 0 0 (-((1:ℝ) * 2) + 11/4) 1 (-((1:ℝ) * 2)) 0 ∧
      0 < det3 0 0 ((1:ℝ) * 2) 0 (-1) 1 := by
  norm_num [det3]

end Erdos634.ChordChartPlanar
