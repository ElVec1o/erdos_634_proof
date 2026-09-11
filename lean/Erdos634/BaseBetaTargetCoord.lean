import Erdos634.ChordChartPlanar
import Erdos634.AngleThreshold
import Erdos634.CornerAnglePermTarget
import Erdos634.BaseBetaQuadCoord

/-!
# A coordinate model of the base-`β` **target**, and the escape point `V` in it

Written 2026-09-11.  Three separate pieces of work of that day —
`RouteOneApproach.lean` (§"What is honestly still open", item 1), `RouteOneWallOnly.lean` (its
closing scope note) and, earlier, the `hV` obligation of `RouteOne.route_one_given_attachment` —
each independently reported that the corpus has **no coordinate `Dissection`-level model of the
base-`β` target**: `BaseBetaWalks` and its relatives work at the word level, and the coordinate
machinery that does exist (`ChordChart`, `BaseBetaQuadCoord`, `CertCoord`) places *tiles*, or
places specific small members (`Tiling44`, `Tiling99`, `CevianTiling63`).  This file supplies the
missing object for the whole family and settles the obligation those three files named.

## The model

For real parameters `0 < e < f` write

    N = 3f² − e²,   L = eN = e(3f² − e²),   D = 4f² − e²,   H = (f² − e²)·√D / 2 .

`baseBetaTarget e f` is the triangle with vertices

    P₀ = (0,0),   P₁ = (L,0),   P₂ = (L/2, H) .

It is isosceles about the vertical `x = L/2`, and its data are **exact**:

* `baseBetaTarget_dist_base`  — `|P₀P₁| = L = eN`;
* `baseBetaTarget_dist_leg₀`, `_leg₁` — `|P₀P₂| = |P₁P₂| = f³`.

The leg length is `f³` on the nose, and the only identity used is
`e²(3f²−e²)² + (f²−e²)²(4f²−e²) = 4f⁶`, which is exactly `BaseBetaQuad.xiQ_norm_one`'s
numerator identity — i.e. the assertion that `ξ = e^{iβ}` has norm one.  So the model is not a
new convention: it *is* `BaseBetaQuadCoord`'s `ξ`, scaled by `f³`, and

    P₂ − P₀ = f³ · (cos β, sin β),   cos β = eN/(2f³),   sin β = (f²−e²)√D/(2f³)

is `xiQ e f` read as a point of the plane (`baseBetaTarget_leg_is_xi`).

## The angles

`cos_cornerAngle_base₀`, `cos_cornerAngle_base₁` give `cos = eN/(2f³)` at both base corners and
`cos_cornerAngle_apex` gives `1 − e²N²/(2f⁶)` at the apex, all by `AngleThreshold.cos_of_sides`
from the three exact distances.  With

    β := arccos (eN/(2f³)),        α := (π − 2β)/3

(so `3α + 2β = π` holds definitionally, `modelAngle_rel`) the three corner angles are
`β, β, 3α` — `baseBetaTarget_corner_base₀/₁`, `baseBetaTarget_corner_apex` — which is *verbatim*
the `htarget` shape hypothesis of `CornerAnglePermTarget.htarget_of_isosceles`, discharged here
rather than assumed (`baseBetaTarget_htarget`).

That `α` is the family's own `α` and not merely a name is `cos_modelAlpha`:

    cos α = (2f² − e²)/(2f²),

the real part of `BaseBetaQuad.zetaQ e f`.  It is proved from the triple-angle identity plus
injectivity of `cos` on `[0,π]`, so no `arccos` gymnastics leak into the statement.

## The escape point

`rem:route1uniform` (`erdos-634-companion.tex:1604`) defines Route 1's escape point as
`V = c·u + (c,0)` with `c = f²` the tile's long side and `u = (cos β, sin β)` the direction of the
target's left side from the base corner.  In this model that is

    escapeV e f = (L/(2f) + f², H/f) ,

`escapeV_eq_c_smul_u` recording that this really is `c·u + (c,0)`.

**The obligation that was open is discharged**: `escapeV_mem_interior` proves

    escapeV e f ∈ interior (baseBetaTarget e f).carrier

for every member `1 ≤ e < f` with `2 ≤ f`, via
`ChordChartPlanar.mem_interior_carrier_of_dets_pos`.  The three
determinants collapse:

* the base side is `L · H/f > 0`;
* the left side is `f² · H > 0` — this is the exact form of "`(c,0)` pushes `V` strictly right of
  the ray `ℝ₊·u`", the `−c sin β` cross product, with `L` cancelling identically;
* the right side is `2f·H·(L(f−1) − f³) > 0`, i.e. **`e(3f²−e²)(f−1) > f³`**
  (`right_side_margin_pos`), which holds for every member with `1 ≤ e < f` and `2 ≤ f`.

The third is the only inequality with content.  At `e = 1` it is `2f³ − 3f² − f + 1 > 0`, and the
hypothesis `2 ≤ f` is **necessary and not cosmetic**: over the reals the inequality is *false* on
`1 < f < 1.87…` (e.g. `f = 3/2`, `e = 1`).  It is integrality of `f` that supplies it — every
base-`β` member has `f ≥ 2` — so the theorem is stated with `2 ≤ f` explicit rather than smuggled.

`escapeV_mem_interior_of_target` is the consumer-facing form: for a `Dissection D` whose target is
this model, the `hV` hypothesis of `RouteOneApproach.EscapeData.ofInterior`,
`RouteOneWallOnly.flank_from_wall_only` and `RouteOne.route_one_given_attachment` holds.

## The negative that came out with it

The same computation settles the *companion* hypothesis, and settles it the other way.
`rem:route1uniform`'s `A = c·u` is the upper end of the side's first `c`-edge — a point of the
target's **left side**.  `sideA_not_mem_interior` proves `A ∉ interior carrier`, so the hypothesis
`hAint : A ∈ interior D.target.carrier`, carried by both
`RouteOneWallOnly.flank_from_wall_only` and `RouteOne.route_one_flank_from_configuration`, is
**false** at the configuration those theorems are meant to serve.  `escapeV_eq_A_shift` records
that the `A` in question is exactly the one shifted to `V` by `(c,0)`.

So the composition "discharge `hV`, then apply `flank_from_wall_only`" does **not** go through as
those theorems were stated: `hV` is free and `hAint` is refuted.  That is a sharper statement than
"still blocked" — it names which hypothesis has to change.

**Superseded 2026-09-11 (same day), `RouteOneBoundaryA.lean`.**  It is the *hypothesis* that was
wrong, not the configuration: interiority of `A` was never used, only that the **open** segment
`V`–`A` is interior, which holds for any `A` in a convex set given `V` interior
(`Convex.openSegment_interior_self_subset_interior`).  `hAint` has been weakened in place to
`hAcar : A ∈ D.target.carrier` in `route_one_flank_from_configuration`,
`route_one_flank_of_vertices`, `flank_from_wall_only` and `flank_from_wall_only_of_vertices`;
`RouteOneBoundaryA.sideA_mem_carrier` discharges it at this `A`, and
`RouteOneBoundaryA.flank_at_route1uniform` states the composition.  The residue is `hwall`, normal
position, and the `α`-tile placement — not a false hypothesis.

## What is **not** claimed

This is not progress on any of the three `/goal` outcomes.  It closes a *formalization* gap that
three files named, nothing more.  Specifically:

1. **No dissection is produced.**  The model is a `Tri`.  Route 1's hypothesis is about
   `D.target` for a hypothetical `Dissection D`; `escapeV_mem_interior_of_target` needs
   `D.target = baseBetaTarget e f` as a hypothesis.  Reducing a general base-`β` `Dissection` to
   this normal position is a *placement* obligation (an isometry moving `D.target` onto the model)
   which is **not** discharged here, and `Tri.Congruent` being congruence under an arbitrary
   isometry means it is a real step, not a relabelling.
2. `hwall` — the actual open content of Route 1 (`rem:routeoneopen`, OPEN) — is untouched, and
   nothing here bears on it.  `RouteOneWallOnly.flank_from_wall_only` had two hypotheses that were
   not witnessed at `Dissection` level, `hV` and `hwall`; this file removes the first from that
   list *given* normal position, and says nothing about the second.
3. **`hAint` is refuted, not discharged** (§9).  *(Dated 2026-09-11; superseded the same day by
   `RouteOneBoundaryA.lean`, which weakens the hypothesis to `A ∈ D.target.carrier` — never used
   in interior form — and discharges it here.  The composition now exists:
   `RouteOneBoundaryA.flank_at_route1uniform`.)*
4. No Rule 0 label moves.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.BaseBetaTargetCoord

open Erdos634.Geometry Erdos634.CertCoord

/-! ## 1. The parameters -/

/-- `N = 3f² − e²`, the tile count of the base-`β` member `(e,f)`. -/
def Nq (e f : ℝ) : ℝ := 3 * f ^ 2 - e ^ 2

/-- The target's base length `L = eN`. -/
def baseLen (e f : ℝ) : ℝ := e * Nq e f

/-- The discriminant `D = 4f² − e²` of `BaseBetaQuadCoord`. -/
def Dr (e f : ℝ) : ℝ := 4 * f ^ 2 - e ^ 2

/-- The target's height `H = (f² − e²)√D / 2`. -/
noncomputable def height (e f : ℝ) : ℝ := (f ^ 2 - e ^ 2) * Real.sqrt (Dr e f) / 2

theorem Dr_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < Dr e f := by
  have hf : 0 < f := lt_trans he hef
  have : e ^ 2 < f ^ 2 := by nlinarith
  unfold Dr; nlinarith

theorem sqrtD_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < Real.sqrt (Dr e f) :=
  Real.sqrt_pos.mpr (Dr_pos he hef)

theorem sq_sqrtD {e f : ℝ} (he : 0 < e) (hef : e < f) :
    Real.sqrt (Dr e f) ^ 2 = Dr e f :=
  Real.sq_sqrt (le_of_lt (Dr_pos he hef))

theorem baseLen_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < baseLen e f := by
  have hf : 0 < f := lt_trans he hef
  have : e ^ 2 < f ^ 2 := by nlinarith
  unfold baseLen Nq; nlinarith

theorem height_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < height e f := by
  have hf : 0 < f := lt_trans he hef
  have h2 : e ^ 2 < f ^ 2 := by nlinarith
  have := sqrtD_pos he hef
  unfold height; positivity

/-- **The base-`β` `√`-identity.**  `e²N² + (f²−e²)²D = 4f⁶` — the numerator identity of
`BaseBetaQuad.xiQ_norm_one`, i.e. `|ξ| = 1`.  This is what makes the legs come out at exactly
`f³`. -/
theorem xi_norm_identity (e f : ℝ) :
    e ^ 2 * Nq e f ^ 2 + (f ^ 2 - e ^ 2) ^ 2 * Dr e f = 4 * f ^ 6 := by
  unfold Nq Dr; ring

/-! ## 2. The triangle -/

theorem target_det_pos {e f : ℝ} (he : 0 < e) (hef : e < f) :
    0 < det3 0 0 (baseLen e f) 0 (baseLen e f / 2) (height e f) := by
  have hL := baseLen_pos he hef
  have hH := height_pos he hef
  have : det3 0 0 (baseLen e f) 0 (baseLen e f / 2) (height e f) = baseLen e f * height e f := by
    unfold det3; ring
  rw [this]; positivity

/-- **The base-`β` target in normal position**: base from `(0,0)` to `(L,0)`, apex at
`(L/2, H)`. -/
noncomputable def baseBetaTarget (e f : ℝ) (he : 0 < e) (hef : e < f) : Tri :=
  mkTri 0 0 (baseLen e f) 0 (baseLen e f / 2) (height e f) (target_det_pos he hef).ne'

@[simp] theorem baseBetaTarget_pts₀ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (baseBetaTarget e f he hef).pts 0 = mkPt 0 0 := rfl

@[simp] theorem baseBetaTarget_pts₁ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (baseBetaTarget e f he hef).pts 1 = mkPt (baseLen e f) 0 := rfl

@[simp] theorem baseBetaTarget_pts₂ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (baseBetaTarget e f he hef).pts 2 = mkPt (baseLen e f / 2) (height e f) := rfl

/-! ## 3. The three side lengths, exactly -/

theorem dist_base {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist (mkPt (0:ℝ) 0) (mkPt (baseLen e f) 0) = baseLen e f := by
  have hL := baseLen_pos he hef
  have hsq : dist (mkPt (0:ℝ) 0) (mkPt (baseLen e f) 0) ^ 2 = baseLen e f ^ 2 := by
    rw [dist_sq_mkPt]; ring
  have hnn : 0 ≤ dist (mkPt (0:ℝ) 0) (mkPt (baseLen e f) 0) := dist_nonneg
  nlinarith [hsq, hnn, hL]

theorem dist_leg₀ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist (mkPt (0:ℝ) 0) (mkPt (baseLen e f / 2) (height e f)) = f ^ 3 := by
  have hf : 0 < f := lt_trans he hef
  have hD := sq_sqrtD he hef
  have hsq : dist (mkPt (0:ℝ) 0) (mkPt (baseLen e f / 2) (height e f)) ^ 2 = (f ^ 3) ^ 2 := by
    rw [dist_sq_mkPt]
    have : (0 - baseLen e f / 2) ^ 2 + (0 - height e f) ^ 2
        = (baseLen e f ^ 2 + (f ^ 2 - e ^ 2) ^ 2 * Real.sqrt (Dr e f) ^ 2) / 4 := by
      unfold height; ring
    rw [this, hD]
    have hid := xi_norm_identity e f
    unfold baseLen
    field_simp
    nlinarith [hid]
  have hnn : 0 ≤ dist (mkPt (0:ℝ) 0) (mkPt (baseLen e f / 2) (height e f)) := dist_nonneg
  nlinarith [hsq, hnn, pow_pos hf 3]

theorem dist_leg₁ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist (mkPt (baseLen e f) 0) (mkPt (baseLen e f / 2) (height e f)) = f ^ 3 := by
  have hf : 0 < f := lt_trans he hef
  have hD := sq_sqrtD he hef
  have hsq : dist (mkPt (baseLen e f) 0) (mkPt (baseLen e f / 2) (height e f)) ^ 2
      = (f ^ 3) ^ 2 := by
    rw [dist_sq_mkPt]
    have : (baseLen e f - baseLen e f / 2) ^ 2 + (0 - height e f) ^ 2
        = (baseLen e f ^ 2 + (f ^ 2 - e ^ 2) ^ 2 * Real.sqrt (Dr e f) ^ 2) / 4 := by
      unfold height; ring
    rw [this, hD]
    have hid := xi_norm_identity e f
    unfold baseLen
    field_simp
    nlinarith [hid]
  have hnn : 0 ≤ dist (mkPt (baseLen e f) 0) (mkPt (baseLen e f / 2) (height e f)) := dist_nonneg
  nlinarith [hsq, hnn, pow_pos hf 3]

/-- **`|P₀P₁| = eN`.** -/
theorem baseBetaTarget_dist_base {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist ((baseBetaTarget e f he hef).pts 0) ((baseBetaTarget e f he hef).pts 1)
      = e * (3 * f ^ 2 - e ^ 2) := dist_base he hef

/-- **`|P₀P₂| = f³`.** -/
theorem baseBetaTarget_dist_leg₀ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist ((baseBetaTarget e f he hef).pts 0) ((baseBetaTarget e f he hef).pts 2) = f ^ 3 :=
  dist_leg₀ he hef

/-- **`|P₁P₂| = f³`.** -/
theorem baseBetaTarget_dist_leg₁ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    dist ((baseBetaTarget e f he hef).pts 1) ((baseBetaTarget e f he hef).pts 2) = f ^ 3 :=
  dist_leg₁ he hef

/-! ## 4. The leg direction is `BaseBetaQuadCoord`'s `ξ = e^{iβ}` -/

/-- **The model is `xiQ`, scaled.**  `P₂ − P₀ = f³·(Re ξ, Im ξ)` with
`ξ = (e(3f²−e²) + (f²−e²)√−D)/(2f³)` — i.e. the real and imaginary parts of
`BaseBetaQuad.xiQ e f`, the `√−D` coordinate multiplied by `√D`.  So this file's conventions and
`BaseBetaQuadCoord`'s are the same conventions. -/
theorem baseBetaTarget_leg_is_xi {e f : ℝ} (he : 0 < e) (hef : e < f) :
    baseLen e f / 2 = f ^ 3 * (e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3)) ∧
    height e f = f ^ 3 * ((f ^ 2 - e ^ 2) / (2 * f ^ 3) * Real.sqrt (Dr e f)) := by
  have hf : 0 < f := lt_trans he hef
  have hf3 : (f : ℝ) ^ 3 ≠ 0 := by positivity
  constructor
  · unfold baseLen Nq; field_simp
  · unfold height; field_simp

/-! ## 5. The corner angles -/

/-- `β = arccos (eN / 2f³)`. -/
noncomputable def modelBeta (e f : ℝ) : ℝ := Real.arccos (baseLen e f / (2 * f ^ 3))

/-- `α = (π − 2β)/3`, so that `3α + 2β = π` holds definitionally. -/
noncomputable def modelAlpha (e f : ℝ) : ℝ := (Real.pi - 2 * modelBeta e f) / 3

theorem modelAngle_rel (e f : ℝ) : 3 * modelAlpha e f + 2 * modelBeta e f = Real.pi := by
  unfold modelAlpha; ring

/-- `eN < 2f³` for every member: `2f³ − eN = (f−e)²(e+2f) > 0`. -/
theorem baseLen_lt {e f : ℝ} (he : 0 < e) (hef : e < f) : baseLen e f < 2 * f ^ 3 := by
  have hf : 0 < f := lt_trans he hef
  have hfac : 2 * f ^ 3 - baseLen e f = (f - e) ^ 2 * (e + 2 * f) := by
    unfold baseLen Nq; ring
  nlinarith [sq_nonneg (f - e), hfac, mul_pos (sub_pos.mpr hef) (sub_pos.mpr hef)]

theorem cosBeta_mem {e f : ℝ} (he : 0 < e) (hef : e < f) :
    0 < baseLen e f / (2 * f ^ 3) ∧ baseLen e f / (2 * f ^ 3) < 1 := by
  have hf : 0 < f := lt_trans he hef
  have h2 : (0:ℝ) < 2 * f ^ 3 := by positivity
  refine ⟨div_pos (baseLen_pos he hef) h2, ?_⟩
  rw [div_lt_one h2]; exact baseLen_lt he hef

theorem cos_modelBeta {e f : ℝ} (he : 0 < e) (hef : e < f) :
    Real.cos (modelBeta e f) = baseLen e f / (2 * f ^ 3) := by
  obtain ⟨h1, h2⟩ := cosBeta_mem he hef
  exact Real.cos_arccos (by linarith) (le_of_lt h2)

theorem modelBeta_mem {e f : ℝ} (he : 0 < e) (hef : e < f) :
    0 < modelBeta e f ∧ modelBeta e f < Real.pi / 2 := by
  obtain ⟨h1, h2⟩ := cosBeta_mem he hef
  constructor
  · exact Real.arccos_pos.mpr h2
  · have := Real.arccos_lt_pi_div_two (x := baseLen e f / (2 * f ^ 3))
    exact this.mpr h1

/-- **The base corner at `P₀` has cosine `eN/(2f³)`** — `AngleThreshold.cos_of_sides` on the exact
side lengths, the `f³` legs cancelling. -/
theorem cos_cornerAngle_base₀ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    Real.cos (cornerAngle ((baseBetaTarget e f he hef).pts 1) ((baseBetaTarget e f he hef).pts 0)
      ((baseBetaTarget e f he hef).pts 2)) = baseLen e f / (2 * f ^ 3) := by
  have hf : 0 < f := lt_trans he hef
  set T := baseBetaTarget e f he hef with hT
  have d10 : dist (T.pts 1) (T.pts 0) = baseLen e f := by
    rw [dist_comm]; exact baseBetaTarget_dist_base he hef
  have d20 : dist (T.pts 2) (T.pts 0) = f ^ 3 := by
    rw [dist_comm]; exact baseBetaTarget_dist_leg₀ he hef
  have d12 : dist (T.pts 1) (T.pts 2) = f ^ 3 := baseBetaTarget_dist_leg₁ he hef
  rw [Erdos634.AngleThreshold.cos_of_sides _ _ _ (by rw [d10]; exact (baseLen_pos he hef).ne')
    (by rw [d20]; positivity), d10, d20, d12]
  have hL := (baseLen_pos he hef).ne'
  field_simp
  ring

/-- **The base corner at `P₁`**, the mirror. -/
theorem cos_cornerAngle_base₁ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    Real.cos (cornerAngle ((baseBetaTarget e f he hef).pts 2) ((baseBetaTarget e f he hef).pts 1)
      ((baseBetaTarget e f he hef).pts 0)) = baseLen e f / (2 * f ^ 3) := by
  have hf : 0 < f := lt_trans he hef
  set T := baseBetaTarget e f he hef with hT
  have d21 : dist (T.pts 2) (T.pts 1) = f ^ 3 := by
    rw [dist_comm]; exact baseBetaTarget_dist_leg₁ he hef
  have d01 : dist (T.pts 0) (T.pts 1) = baseLen e f := baseBetaTarget_dist_base he hef
  have d20 : dist (T.pts 2) (T.pts 0) = f ^ 3 := by
    rw [dist_comm]; exact baseBetaTarget_dist_leg₀ he hef
  rw [Erdos634.AngleThreshold.cos_of_sides _ _ _ (by rw [d21]; positivity)
    (by rw [d01]; exact (baseLen_pos he hef).ne'), d21, d01, d20]
  have hL := (baseLen_pos he hef).ne'
  field_simp
  ring

theorem cornerAngle_base₀ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    cornerAngle ((baseBetaTarget e f he hef).pts 1) ((baseBetaTarget e f he hef).pts 0)
      ((baseBetaTarget e f he hef).pts 2) = modelBeta e f := by
  have hc := cos_cornerAngle_base₀ he hef
  have hb := cos_modelBeta he hef
  have h1 : cornerAngle ((baseBetaTarget e f he hef).pts 1) ((baseBetaTarget e f he hef).pts 0)
      ((baseBetaTarget e f he hef).pts 2) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have h2 : modelBeta e f ∈ Set.Icc 0 Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  exact Real.injOn_cos h1 h2 (by rw [hc, hb])

theorem cornerAngle_base₁ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    cornerAngle ((baseBetaTarget e f he hef).pts 2) ((baseBetaTarget e f he hef).pts 1)
      ((baseBetaTarget e f he hef).pts 0) = modelBeta e f := by
  have hc := cos_cornerAngle_base₁ he hef
  have hb := cos_modelBeta he hef
  have h1 : cornerAngle ((baseBetaTarget e f he hef).pts 2) ((baseBetaTarget e f he hef).pts 1)
      ((baseBetaTarget e f he hef).pts 0) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have h2 : modelBeta e f ∈ Set.Icc 0 Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  exact Real.injOn_cos h1 h2 (by rw [hc, hb])

/-- **The apex carries `3α`.**  From the two base corners and the angle sum. -/
theorem cornerAngle_apex {e f : ℝ} (he : 0 < e) (hef : e < f) :
    cornerAngle ((baseBetaTarget e f he hef).pts 0) ((baseBetaTarget e f he hef).pts 2)
      ((baseBetaTarget e f he hef).pts 1) = 3 * modelAlpha e f := by
  have hsum := Erdos634.Geometry.cornerAngle_sum (baseBetaTarget e f he hef)
  rw [cornerAngle_base₀ he hef, cornerAngle_base₁ he hef] at hsum
  have := modelAngle_rel e f
  linarith

/-- **The shape hypothesis `htarget`, discharged.**  Every corner of the model carries `3α` or
`β` — the hypothesis `lem:census` and the whole route-1 chain assume, now proved for an explicit
triangle rather than assumed.  (`CornerAnglePermTarget.htarget_of_isosceles` derives the same from
the two base corners; here the base corners themselves are computed.) -/
theorem baseBetaTarget_htarget {e f : ℝ} (he : 0 < e) (hef : e < f) :
    ∀ k : Fin 3,
      cornerAngle ((baseBetaTarget e f he hef).pts (k + 1)) ((baseBetaTarget e f he hef).pts k)
        ((baseBetaTarget e f he hef).pts (k + 2)) = 3 * modelAlpha e f ∨
      cornerAngle ((baseBetaTarget e f he hef).pts (k + 1)) ((baseBetaTarget e f he hef).pts k)
        ((baseBetaTarget e f he hef).pts (k + 2)) = modelBeta e f := by
  refine Erdos634.Geometry.htarget_of_isosceles _ (modelAngle_rel e f) 2 ?_ ?_
  · have h : ((2 : Fin 3) + 1) = 0 := by decide
    rw [h]
    simpa [show ((0:Fin 3) + 1) = 1 from rfl, show ((0:Fin 3) + 2) = 2 from rfl] using
      cornerAngle_base₀ he hef
  · have h : ((2 : Fin 3) + 2) = 1 := by decide
    rw [h]
    simpa [show ((1:Fin 3) + 1) = 2 from rfl, show ((1:Fin 3) + 2) = 0 from rfl] using
      cornerAngle_base₁ he hef

/-! ## 6. `α` is the family's `α`: `cos α = (2f² − e²)/(2f²)` -/

/-- **The triple-angle identity of the model.**  `cos 3α = 4C³ − 3C` with
`C = (2f²−e²)/(2f²)`, and independently `cos 3α = cos(π − 2β) = 1 − 2cos²β`; the two agree as a
polynomial identity in `(e,f)` — this is exactly the algebraic content of
`BaseBetaQuad.xiQ_sq_zetaQ_cube` (`ξ²ζ³ = −1`). -/
theorem triple_angle_identity {e f : ℝ} (hf : 0 < f) :
    4 * ((2 * f ^ 2 - e ^ 2) / (2 * f ^ 2)) ^ 3 - 3 * ((2 * f ^ 2 - e ^ 2) / (2 * f ^ 2))
      = 1 - 2 * (baseLen e f / (2 * f ^ 3)) ^ 2 := by
  have h2 : (f : ℝ) ≠ 0 := ne_of_gt hf
  unfold baseLen Nq
  field_simp
  ring

/-- **`cos α = (2f² − e²)/(2f²)`** — the real part of `BaseBetaQuad.zetaQ e f`.  So `modelAlpha`
is the base-`β` family's `α`, not a fresh name: `cos α = 1 − 2 sin²(α/2)` with
`sin(α/2) = e/(2f)`. -/
theorem cos_modelAlpha {e f : ℝ} (he : 0 < e) (hef : e < f) :
    Real.cos (modelAlpha e f) = (2 * f ^ 2 - e ^ 2) / (2 * f ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he hef
  set C : ℝ := (2 * f ^ 2 - e ^ 2) / (2 * f ^ 2) with hC
  -- `cos (3α) = 1 - 2 cos²β`
  have h3a : 3 * modelAlpha e f = Real.pi - 2 * modelBeta e f := by
    unfold modelAlpha; ring
  have hcos3 : Real.cos (3 * modelAlpha e f) = 1 - 2 * (baseLen e f / (2 * f ^ 3)) ^ 2 := by
    rw [h3a, Real.cos_pi_sub, Real.cos_two_mul, cos_modelBeta he hef]
    ring
  -- and `cos (3α) = 4 cos³α - 3 cos α`
  have hexp : Real.cos (3 * modelAlpha e f)
      = 4 * Real.cos (modelAlpha e f) ^ 3 - 3 * Real.cos (modelAlpha e f) := by
    have := Real.cos_three_mul (modelAlpha e f); linarith [this]
  have hCid := triple_angle_identity (e := e) hf
  have hkey : 4 * Real.cos (modelAlpha e f) ^ 3 - 3 * Real.cos (modelAlpha e f)
      = 4 * C ^ 3 - 3 * C := by rw [← hexp, hcos3, hC, hCid]
  -- `cos` is injective on `[0, π]`, and `3α, 3·arccos C ∈ [0, π]`
  have hCbound : 0 < C ∧ C < 1 := by
    have h1 : (0:ℝ) < 2 * f ^ 2 := by positivity
    constructor
    · apply div_pos _ h1; nlinarith
    · rw [div_lt_one h1]; nlinarith [mul_pos he he]
  have harccos : Real.cos (Real.arccos C) = C :=
    Real.cos_arccos (by linarith [hCbound.1]) (le_of_lt hCbound.2)
  -- both `modelAlpha` and `arccos C` lie in `[0, π/3]`, so `3·` of each lies in `[0, π]`
  have halpha_mem : modelAlpha e f ∈ Set.Icc 0 Real.pi := by
    constructor
    · unfold modelAlpha; have := Real.pi_pos; nlinarith
    · unfold modelAlpha; have := Real.pi_pos; linarith
  have harc_mem : Real.arccos C ∈ Set.Icc 0 Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  -- compare via `cos 3·`, using that `3α, 3 arccos C ∈ [0, π]`
  have h3alpha : 3 * modelAlpha e f ∈ Set.Icc 0 Real.pi := by
    rw [h3a]
    refine ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have h3arc : 3 * Real.arccos C ∈ Set.Icc 0 Real.pi := by
    constructor
    · have := Real.arccos_nonneg C; linarith
    · -- `arccos C ≤ π/3` because `C ≥ 1/2`
      have hhalf : (1:ℝ) / 2 ≤ C := by
        rw [hC, le_div_iff₀ (by positivity : (0:ℝ) < 2 * f ^ 2)]
        nlinarith
      have hmono : Real.arccos C ≤ Real.arccos (1/2 : ℝ) :=
        Real.arccos_le_arccos hhalf
      have : Real.arccos (1/2 : ℝ) = Real.pi / 3 := by
        rw [show (1/2 : ℝ) = Real.cos (Real.pi / 3) by rw [Real.cos_pi_div_three]]
        exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
      rw [this] at hmono; linarith
  have hcos3arc : Real.cos (3 * Real.arccos C) = 4 * C ^ 3 - 3 * C := by
    rw [Real.cos_three_mul, harccos]
  have heq3 : 3 * modelAlpha e f = 3 * Real.arccos C :=
    Real.injOn_cos h3alpha h3arc (by rw [hexp, hkey, hcos3arc])
  have : modelAlpha e f = Real.arccos C := by linarith
  rw [this, harccos]

/-! ## 7. The escape point `V = c·u + (c,0)` of `rem:route1uniform` -/

/-- The escape point of `rem:route1uniform`: `V = c·u + (c,0)` with `c = f²` and
`u = (cos β, sin β)` the direction of the target's left side. -/
noncomputable def escapeV (e f : ℝ) : ℝ × ℝ :=
  (baseLen e f / (2 * f) + f ^ 2, height e f / f)

/-- **`escapeV` really is `c·u + (c,0)`.**  With `c = f²`, `u = (cos β, sin β)` and the model's
`cos β = eN/(2f³)`, `sin β = (f²−e²)√D/(2f³)`, the two coordinates are
`f²·cos β + f²` and `f²·sin β`. -/
theorem escapeV_eq_c_smul_u {e f : ℝ} (he : 0 < e) (hef : e < f) :
    (escapeV e f).1 = f ^ 2 * (baseLen e f / (2 * f ^ 3)) + f ^ 2 ∧
    (escapeV e f).2 = f ^ 2 * ((f ^ 2 - e ^ 2) / (2 * f ^ 3) * Real.sqrt (Dr e f)) := by
  have hf : 0 < f := lt_trans he hef
  have hf0 : (f : ℝ) ≠ 0 := ne_of_gt hf
  constructor
  · unfold escapeV; field_simp
  · unfold escapeV height; field_simp

/-! ## 8. The three determinants, and the one inequality with content -/

/-- **The right-hand side's margin.**  `e(3f²−e²)(f−1) − f³ > 0` for every member with
`1 ≤ e < f` and `2 ≤ f`.  This is the only inequality in the interiority check with content; at
`e = 1` it is `2f³ − 3f² − f + 1 > 0`, which needs `f ≥ 2` (it fails at `f = 3/2`).  The proof
first replaces `e` by its minimum `1`, using that `e ↦ e(3f²−e²)` increases on `[0,f]`. -/
theorem right_side_margin_pos {e f : ℝ} (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f) :
    0 < baseLen e f * (f - 1) - f ^ 3 := by
  have hf1 : (1:ℝ) < f := lt_of_le_of_lt he hef
  have hf : (0:ℝ) < f := by linarith
  -- `g(e) = e(3f² − e²)` is increasing on `[0, f]`, so `g(e) ≥ g(1) = 3f² − 1`
  have hmono : 3 * f ^ 2 - 1 ≤ baseLen e f := by
    unfold baseLen Nq
    nlinarith [mul_pos (sub_pos.mpr hef) (sub_pos.mpr hef), sq_nonneg (e - 1), sq_nonneg (e + 1),
      mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr he)]
  have hbase : 0 < (3 * f ^ 2 - 1) * (f - 1) - f ^ 3 := by
    nlinarith [sq_nonneg (f - 2), mul_nonneg (mul_nonneg (sub_nonneg.mpr hf2) (sub_nonneg.mpr hf2))
      (sub_nonneg.mpr hf2), sub_nonneg.mpr hf2]
  nlinarith [hmono, sub_pos.mpr hf1]

theorem det_left {e f : ℝ} (he : 0 < e) (hef : e < f) :
    det3 0 0 (escapeV e f).1 (escapeV e f).2 (baseLen e f / 2) (height e f)
      = f ^ 2 * height e f := by
  have hf : 0 < f := lt_trans he hef
  have hf0 : (f : ℝ) ≠ 0 := ne_of_gt hf
  unfold det3 escapeV
  field_simp
  ring

theorem det_bottom (e f : ℝ) :
    det3 0 0 (baseLen e f) 0 (escapeV e f).1 (escapeV e f).2
      = baseLen e f * height e f / f := by
  unfold det3 escapeV
  ring

theorem det_right {e f : ℝ} (he : 0 < e) (hef : e < f) :
    2 * f ^ 2 * det3 (escapeV e f).1 (escapeV e f).2 (baseLen e f) 0
        (baseLen e f / 2) (height e f)
      = 2 * f * height e f * (baseLen e f * (f - 1) - f ^ 3) := by
  have hf : 0 < f := lt_trans he hef
  have hf0 : (f : ℝ) ≠ 0 := ne_of_gt hf
  unfold det3 escapeV
  field_simp
  ring

/-- **The escape point is interior to the target.**  `V = c·u + (c,0)` lies in
`interior (baseBetaTarget e f).carrier` for every member `1 ≤ e < f`.

This is the check `RouteOneApproach.lean` recorded as *"a finite check: two strict linear
inequalities in the target's coordinates … not formalised here because the coordinate model of the
base-`β` target is not connected to `Dissection` in this corpus"*. -/
theorem escapeV_mem_interior {e f : ℝ} (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f) :
    mkPt (escapeV e f).1 (escapeV e f).2 ∈ interior (baseBetaTarget e f (by linarith) hef).carrier
    := by
  have he0 : (0:ℝ) < e := by linarith
  have hf : (0:ℝ) < f := lt_trans he0 hef
  have hH := height_pos he0 hef
  have hL := baseLen_pos he0 hef
  refine Erdos634.ChordChartPlanar.mem_interior_carrier_of_dets_pos
    (target_det_pos he0 hef) ?_ ?_ ?_
  · -- the right side
    have hm := right_side_margin_pos he hef hf2
    have hd := det_right he0 hef
    nlinarith [hd, hm, hH, hf, mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hf) hH,
      mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hf) hH]
  · rw [det_left he0 hef]; positivity
  · rw [det_bottom e f]; positivity

/-- **Consumer form.**  For a dissection whose target is the model in normal position, the
hypothesis `hV : V ∈ interior D.target.carrier` of `RouteOne.route_one_given_attachment`,
`RouteOneApproach.EscapeData.ofInterior` and `RouteOneWallOnly.flank_from_wall_only` holds at
`rem:route1uniform`'s escape point.

The hypothesis `htgt` is the *normal-position* obligation, and it is not discharged here: see the
module docstring, item 1. -/
theorem escapeV_mem_interior_of_target {N : ℕ} (D : Dissection N) {e f : ℝ}
    (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f)
    (htgt : D.target = baseBetaTarget e f (by linarith) hef) :
    mkPt (escapeV e f).1 (escapeV e f).2 ∈ interior D.target.carrier := by
  rw [htgt]; exact escapeV_mem_interior he hef hf2

/-! ## 9. The companion point `A = c·u` is **not** interior — a negative about `hAint`

`rem:route1uniform` defines `A = c·u` as *"the upper end of the side's first `c`-edge"*, i.e. a
point of the target's **left side**, and `V = c·u + (c,0) = A + (c,0)` (`escapeV_eq_A_shift`).
`RouteOneWallOnly.flank_from_wall_only` and `RouteOne.route_one_flank_from_configuration` both
carry `hAint : A ∈ interior D.target.carrier` alongside `hV`.  For the configuration's own `A`
that hypothesis is **false**: `A` is on the boundary.

This is recorded here as a sharp negative, not as an obstacle discovered and left: it says that
`hAint` cannot be discharged the way `hV` just was, and that any use of those two theorems at
`rem:route1uniform`'s configuration must either take `A` strictly inside the side's `c`-edge in a
*different* placement, or weaken `hAint`.  It is exactly the kind of hypothesis-satisfiability
check the project's vacuity rule demands, done before the composition is claimed. -/

/-- The companion point `A = c·u` of `rem:route1uniform`, `c = f²`. -/
noncomputable def sideA (e f : ℝ) : ℝ × ℝ := (baseLen e f / (2 * f), height e f / f)

/-- **`V = A + (c,0)`**, `c = f²` — the shift of `rem:route1uniform`, verbatim. -/
theorem escapeV_eq_A_shift (e f : ℝ) :
    (escapeV e f).1 = (sideA e f).1 + f ^ 2 ∧ (escapeV e f).2 = (sideA e f).2 := by
  unfold escapeV sideA; exact ⟨rfl, rfl⟩

/-- The left side's linear functional: `g q = q₀·H − (L/2)·q₁`, i.e.
`det3 0 0 q₀ q₁ (L/2) H`.  It vanishes on the whole left side and is `> 0` at `P₁`. -/
theorem leftFunctional_carrier {e f : ℝ} (he : 0 < e) (hef : e < f) :
    ∀ q : Plane, q ∈ (baseBetaTarget e f he hef).carrier →
      0 ≤ q 0 * height e f - baseLen e f / 2 * q 1 := by
  have hH := height_pos he hef
  have hL := baseLen_pos he hef
  have hconv : Convex ℝ {q : Plane | 0 ≤ q 0 * height e f - baseLen e f / 2 * q 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hx0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    have hx1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by simp
    rw [hx0, hx1]
    nlinarith [mul_nonneg ha hx, mul_nonneg hb hy]
  have hsub : (baseBetaTarget e f he hef).carrier
      ⊆ {q : Plane | 0 ≤ q 0 * height e f - baseLen e f / 2 * q 1} := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨k, rfl⟩
    fin_cases k <;>
      simp [baseBetaTarget, mkTri_pts, mkPt_zero, mkPt_one] <;> nlinarith
  exact fun q hq => hsub hq

/-- **`A = c·u` lies on the target's boundary, not in its interior.**  So the hypothesis
`hAint : A ∈ interior D.target.carrier` of `RouteOneWallOnly.flank_from_wall_only` and of
`RouteOne.route_one_flank_from_configuration` is **not** satisfied by `rem:route1uniform`'s own
`A`, in this (or any) placement in which `A` is the upper end of the side's first `c`-edge.

*(2026-09-11, later: those two theorems no longer carry that hypothesis — it is now
`A ∈ D.target.carrier`, which `RouteOneBoundaryA.sideA_mem_carrier` proves.  This negative stands
as stated and is what forced the weakening.)* -/
theorem sideA_not_mem_interior {e f : ℝ} (he : 0 < e) (hef : e < f) :
    mkPt (sideA e f).1 (sideA e f).2 ∉ interior (baseBetaTarget e f he hef).carrier := by
  have hf : (0:ℝ) < f := lt_trans he hef
  have hH := height_pos he hef
  have hL := baseLen_pos he hef
  intro hmem
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hmem
  -- step strictly leftwards by `r/2`
  set q : Plane := mkPt ((sideA e f).1 - r / 2) (sideA e f).2 with hq
  have hdist : dist q (mkPt (sideA e f).1 (sideA e f).2) = r / 2 := by
    have := dist_sq_mkPt ((sideA e f).1 - r / 2) (sideA e f).2 (sideA e f).1 (sideA e f).2
    have hnn : 0 ≤ dist q (mkPt (sideA e f).1 (sideA e f).2) := dist_nonneg
    nlinarith [this, hnn, hr]
  have hin : q ∈ (baseBetaTarget e f he hef).carrier :=
    interior_subset (hball (Metric.mem_ball.mpr (by rw [hdist]; linarith)))
  have hg := leftFunctional_carrier he hef q hin
  rw [hq] at hg
  simp only [mkPt_zero, mkPt_one] at hg
  have hzero : (sideA e f).1 * height e f - baseLen e f / 2 * (sideA e f).2 = 0 := by
    unfold sideA
    field_simp
    ring
  nlinarith [hg, hzero, hr, hH]

/-! ## 10. Axiom audit -/

#print axioms baseBetaTarget_dist_base
#print axioms baseBetaTarget_dist_leg₀
#print axioms baseBetaTarget_dist_leg₁
#print axioms cornerAngle_base₀
#print axioms cornerAngle_base₁
#print axioms cornerAngle_apex
#print axioms baseBetaTarget_htarget
#print axioms cos_modelAlpha
#print axioms escapeV_eq_c_smul_u
#print axioms right_side_margin_pos
#print axioms escapeV_mem_interior
#print axioms escapeV_eq_A_shift
#print axioms sideA_not_mem_interior
#print axioms escapeV_mem_interior_of_target

end Erdos634.BaseBetaTargetCoord
