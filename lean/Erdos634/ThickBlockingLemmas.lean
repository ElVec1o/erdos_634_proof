import Erdos634.BaseBetaTargetCoord
import Erdos634.CertGeom

/-!
# Dissection-level **blocking** lemmas at the thick member `(e,f) = (2,3)`, tile `(6,5,9)`

Erdős #634, base-`β` branch, `N = 23`.  The corpus already holds *filler* content at this thick
member — `ThickJunctionCoords.lean` (the junction filler, `dGB63 = −5/3`, `dBG63 = 23/3`,
`apexH63 = 10√2/3`), `ThickWedgeGram.lean`, `ThickOffsetFiller.lean`.  It holds **no blocking
content**: no theorem saying *"in this explicit configuration, no congruent copy of the tile can be
placed at the forced corner"*.  This file supplies two such lemmas, with witnesses.

## Provenance, and what is *not* claimed

The two corners and rays below come from the canonical refutation certificate for `N = 23`
(room `e2b3`: the `σ : x ↦ 46−x` canonicalisation and **Lemma P**, `report_ramanujan.md` §5).
They are nodes `2` and `9`/`11` of Lemma P's thirteen-node tree.

**The covering claim is NOT formalised and is NOT proved here.**  "These lemmas close all jams,
hence no dissection with base word beginning `a c b` exists" needs the completeness of the
constructor's placement rule (the geometric half of H7 — that the six oriented placements
enumerated at a forced corner are *all* the placements a dissection could use there), which is
unbuilt.  A Lean statement of the covering claim would be a theorem whose hypothesis is discharged
nowhere.  What *is* proved here is each blocking lemma individually: a genuine geometric fact about
the target and about triangles congruent to the tile, independent of the search and of any
placement rule.

## What is proved

* `target63` — the `(2,3)` target `(0,0)–(46,0)–(23, 10√2)`, and `target63_carrier_eq`:
  it is `BaseBetaTargetCoord.baseBetaTarget 2 3` on the nose.
* `not_mem_target63_of_left`, `not_mem_target63_of_below`, `mem_target63` — the three edge
  functionals of the target as exact membership tests.
* **`blocking_B1`** — at the corner `v = (6,0)` with forced ray `d₀ = (7/9, √32/9)`, all six
  oriented placements of a triangle congruent to `(6,5,9)` with a corner at `v` and an edge along
  `d₀` escape the target (each through the **left leg**).
* **`blocking_B2`** — the same at `v = (15,0)`, `d₀ = (−17/81, 14√32/81)`: four escape through the
  left leg, two below the base.
* `B1_witness`, `B2_witness` — **non-vacuity**.  The configurations in which B1 and B2 arise are
  exhibited as actual coordinate triangles: two tiles for B1, six for B2, each proved congruent to
  `(6,5,9)` (`sides_*`), each proved inside the target (`inside_*`), with pairwise disjoint
  interiors (`disj_*`).  Without these the blocking lemmas would be statements about a
  configuration that might not exist — the vacuity trap `CLAUDE.md` names.

Every coordinate is exact in `ℚ(√32)`; `rr = √32 = 4√2`.  No `sorry`; axioms are the standard three.
-/

namespace Erdos634.ThickBlockingLemmas

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.BaseBetaTargetCoord

/-! ## 1. The field element `rr = √32` -/

/-- `rr = √32 = 4√2`, the surd every coordinate at this member lives in. -/
noncomputable def rr : ℝ := Real.sqrt 32

theorem rr_pos : 0 < rr := Real.sqrt_pos.mpr (by norm_num)

theorem rr_sq : rr ^ 2 = 32 := Real.sq_sqrt (by norm_num)

/-! ## 2. The target, and its three edge functionals -/

theorem det_target63 : det3 (0:ℝ) (0:ℝ) (46:ℝ) (0:ℝ) (23:ℝ) (5/2*rr) ≠ 0 := by
  have h : det3 (0:ℝ) (0:ℝ) (46:ℝ) (0:ℝ) (23:ℝ) (5/2*rr) = 115*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- The base-`β` target at `(e,f) = (2,3)`: `(0,0)`, `(46,0)`, `(23, 10√2)`. -/
noncomputable def target63 : Tri := mkTri 0 0 46 0 23 (5/2*rr) det_target63

theorem baseLen_63 : baseLen 2 3 = (46:ℝ) := by unfold baseLen Nq; norm_num

theorem height_63 : height 2 3 = 5/2*rr := by
  unfold height Dr rr
  norm_num
  ring

/-- **The model is the corpus's `baseBetaTarget 2 3`.**  Not a new convention. -/
theorem target63_carrier_eq :
    target63.carrier = (baseBetaTarget 2 3 (by norm_num) (by norm_num)).carrier := by
  have hpts : target63.pts = (baseBetaTarget 2 3 (by norm_num) (by norm_num)).pts := by
    funext k
    fin_cases k
    · rfl
    · show mkPt (46:ℝ) 0 = mkPt (baseLen 2 3) 0
      rw [baseLen_63]
    · show mkPt (23:ℝ) (5/2*rr) = mkPt (baseLen 2 3 / 2) (height 2 3)
      rw [baseLen_63, height_63]; norm_num
  unfold Tri.carrier
  rw [hpts]

/-- An affine functional bounded **below** at the three vertices is bounded below on the carrier.
The mirror of `CertGeom.le_of_forall_pts_le`, which the separation certificates need. -/
theorem ge_of_forall_pts_ge {t : Tri} (f : Plane →ᵃ[ℝ] ℝ) {c : ℝ} (h : ∀ k, c ≤ f (t.pts k)) :
    ∀ x ∈ t.carrier, c ≤ f x := by
  have hconv : Convex ℝ (f ⁻¹' Set.Ici c) := (convex_Ici c).affine_preimage f
  have hsub : t.carrier ⊆ f ⁻¹' Set.Ici c :=
    convexHull_min (Set.range_subset_iff.mpr h) hconv
  exact fun x hx => hsub hx

/-- **Beyond the left leg is outside the target.**  The left leg carries the functional
`L(x,y) = (5/2)·√32·x − 23·y`, nonnegative on the target; a point with `L < 0` is outside. -/
theorem not_mem_target63_of_left {x y : ℝ} (h : 0 < 23*y - 5/2*rr*x) :
    mkPt x y ∉ target63.carrier := by
  intro hm
  have hb : ∀ z ∈ target63.carrier, lineFun 0 0 23 (5/2*rr) z ≤ 0 := by
    refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k <;>
      simp [target63, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
      nlinarith [rr_pos]
  have := hb _ hm
  simp only [lineFun_apply, mkPt_zero, mkPt_one] at this
  nlinarith

/-- **Below the base is outside the target.** -/
theorem not_mem_target63_of_below {x y : ℝ} (h : y < 0) : mkPt x y ∉ target63.carrier := by
  intro hm
  have hb : ∀ z ∈ target63.carrier, lineFun 46 0 0 0 z ≤ 0 := by
    refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k <;>
      simp [target63, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
      nlinarith [rr_pos]
  have := hb _ hm
  simp only [lineFun_apply, mkPt_zero, mkPt_one] at this
  nlinarith

/-- **The containment test.**  Nonnegativity of the three edge functionals puts a point in the
target: `y ≥ 0` (base), `(5/2)√32·x − 23y ≥ 0` (left leg), `(5/2)√32·(46−x) − 23y ≥ 0` (right). -/
theorem mem_target63 {x y : ℝ} (hb : 0 ≤ y) (hl : 0 ≤ 5/2*rr*x - 23*y)
    (hr : 0 ≤ 5/2*rr*(46 - x) - 23*y) : mkPt x y ∈ target63.carrier := by
  refine mem_carrier_of_dets (x₀ := 0) (y₀ := 0) (x₁ := 46) (y₁ := 0) (x₂ := 23) (y₂ := 5/2*rr)
    ?_ ?_ ?_ ?_
  · have h : det3 (0:ℝ) (0:ℝ) (46:ℝ) (0:ℝ) (23:ℝ) (5/2*rr) = 115*rr := by unfold det3; ring
    rw [h]; nlinarith [rr_pos]
  · unfold det3; nlinarith [hr]
  · unfold det3; nlinarith [hl]
  · unfold det3; nlinarith [hb]

/-! ## 3. Blocking Lemma **B1** — corner `(6,0)`, ray `(7/9, √32/9)` -/

theorem det_b1alpha59 : det3 (6 : ℝ) (0:ℝ) (89/9 : ℝ) ((5/9 : ℝ)*rr) (71/9 : ℝ) ((14/9 : ℝ)*rr) ≠ 0 := by
  have h : det3 (6 : ℝ) (0:ℝ) (89/9 : ℝ) ((5/9 : ℝ)*rr) (71/9 : ℝ) ((14/9 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `alpha59` at the corner `(6,0)` on the ray `(7/9, √32/9)`. -/
noncomputable def b1alpha59 : Tri := mkTri (6 : ℝ) (0:ℝ) (89/9 : ℝ) ((5/9 : ℝ)*rr) (71/9 : ℝ) ((14/9 : ℝ)*rr) det_b1alpha59

/-- **`b1alpha59` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b1alpha59 :
    dist (b1alpha59.pts 0) (b1alpha59.pts 1) ^ 2 = (25 : ℝ) ∧
    dist (b1alpha59.pts 1) (b1alpha59.pts 2) ^ 2 = (36 : ℝ) ∧
    dist (b1alpha59.pts 2) (b1alpha59.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (89/9 : ℝ) ((5/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq
  · show dist (mkPt (89/9 : ℝ) ((5/9 : ℝ)*rr)) (mkPt (71/9 : ℝ) ((14/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq
  · show dist (mkPt (71/9 : ℝ) ((14/9 : ℝ)*rr)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((196/81 : ℝ)) * rr_sq

/-- **Escape lemma B1.**  `b1alpha59` is not contained in the target: its vertex `2` lies strictly beyond the target's **left leg**. -/
theorem escape_b1alpha59 : ¬ (b1alpha59.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b1alpha59.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b1alpha59.pts 2 = mkPt (71/9 : ℝ) ((14/9 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_b1alpha95 : det3 (6 : ℝ) (0:ℝ) (13 : ℝ) ((1 : ℝ)*rr) (571/81 : ℝ) ((70/81 : ℝ)*rr) ≠ 0 := by
  have h : det3 (6 : ℝ) (0:ℝ) (13 : ℝ) ((1 : ℝ)*rr) (571/81 : ℝ) ((70/81 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `alpha95` at the corner `(6,0)` on the ray `(7/9, √32/9)`. -/
noncomputable def b1alpha95 : Tri := mkTri (6 : ℝ) (0:ℝ) (13 : ℝ) ((1 : ℝ)*rr) (571/81 : ℝ) ((70/81 : ℝ)*rr) det_b1alpha95

/-- **`b1alpha95` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b1alpha95 :
    dist (b1alpha95.pts 0) (b1alpha95.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (b1alpha95.pts 1) (b1alpha95.pts 2) ^ 2 = (36 : ℝ) ∧
    dist (b1alpha95.pts 2) (b1alpha95.pts 0) ^ 2 = (25 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (13 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq
  · show dist (mkPt (13 : ℝ) ((1 : ℝ)*rr)) (mkPt (571/81 : ℝ) ((70/81 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((121/6561 : ℝ)) * rr_sq
  · show dist (mkPt (571/81 : ℝ) ((70/81 : ℝ)*rr)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((4900/6561 : ℝ)) * rr_sq

/-- **Escape lemma B1.**  `b1alpha95` is not contained in the target: its vertex `2` lies strictly beyond the target's **left leg**. -/
theorem escape_b1alpha95 : ¬ (b1alpha95.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b1alpha95.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b1alpha95.pts 2 = mkPt (571/81 : ℝ) ((70/81 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_b1beta69 : det3 (6 : ℝ) (0:ℝ) (32/3 : ℝ) ((2/3 : ℝ)*rr) (9 : ℝ) ((3/2 : ℝ)*rr) ≠ 0 := by
  have h : det3 (6 : ℝ) (0:ℝ) (32/3 : ℝ) ((2/3 : ℝ)*rr) (9 : ℝ) ((3/2 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `beta69` at the corner `(6,0)` on the ray `(7/9, √32/9)`. -/
noncomputable def b1beta69 : Tri := mkTri (6 : ℝ) (0:ℝ) (32/3 : ℝ) ((2/3 : ℝ)*rr) (9 : ℝ) ((3/2 : ℝ)*rr) det_b1beta69

/-- **`b1beta69` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b1beta69 :
    dist (b1beta69.pts 0) (b1beta69.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (b1beta69.pts 1) (b1beta69.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (b1beta69.pts 2) (b1beta69.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (32/3 : ℝ) ((2/3 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((4/9 : ℝ)) * rr_sq
  · show dist (mkPt (32/3 : ℝ) ((2/3 : ℝ)*rr)) (mkPt (9 : ℝ) ((3/2 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq
  · show dist (mkPt (9 : ℝ) ((3/2 : ℝ)*rr)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((9/4 : ℝ)) * rr_sq

/-- **Escape lemma B1.**  `b1beta69` is not contained in the target: its vertex `2` lies strictly beyond the target's **left leg**. -/
theorem escape_b1beta69 : ¬ (b1beta69.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b1beta69.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b1beta69.pts 2 = mkPt (9 : ℝ) ((3/2 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_b1beta96 : det3 (6 : ℝ) (0:ℝ) (13 : ℝ) ((1 : ℝ)*rr) (8 : ℝ) ((1 : ℝ)*rr) ≠ 0 := by
  have h : det3 (6 : ℝ) (0:ℝ) (13 : ℝ) ((1 : ℝ)*rr) (8 : ℝ) ((1 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `beta96` at the corner `(6,0)` on the ray `(7/9, √32/9)`. -/
noncomputable def b1beta96 : Tri := mkTri (6 : ℝ) (0:ℝ) (13 : ℝ) ((1 : ℝ)*rr) (8 : ℝ) ((1 : ℝ)*rr) det_b1beta96

/-- **`b1beta96` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b1beta96 :
    dist (b1beta96.pts 0) (b1beta96.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (b1beta96.pts 1) (b1beta96.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (b1beta96.pts 2) (b1beta96.pts 0) ^ 2 = (36 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (13 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq
  · show dist (mkPt (13 : ℝ) ((1 : ℝ)*rr)) (mkPt (8 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (8 : ℝ) ((1 : ℝ)*rr)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq

/-- **Escape lemma B1.**  `b1beta96` is not contained in the target: its vertex `2` lies strictly beyond the target's **left leg**. -/
theorem escape_b1beta96 : ¬ (b1beta96.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b1beta96.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b1beta96.pts 2 = mkPt (8 : ℝ) ((1 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_b1gamma65 : det3 (6 : ℝ) (0:ℝ) (32/3 : ℝ) ((2/3 : ℝ)*rr) (47/27 : ℝ) ((25/54 : ℝ)*rr) ≠ 0 := by
  have h : det3 (6 : ℝ) (0:ℝ) (32/3 : ℝ) ((2/3 : ℝ)*rr) (47/27 : ℝ) ((25/54 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `gamma65` at the corner `(6,0)` on the ray `(7/9, √32/9)`. -/
noncomputable def b1gamma65 : Tri := mkTri (6 : ℝ) (0:ℝ) (32/3 : ℝ) ((2/3 : ℝ)*rr) (47/27 : ℝ) ((25/54 : ℝ)*rr) det_b1gamma65

/-- **`b1gamma65` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b1gamma65 :
    dist (b1gamma65.pts 0) (b1gamma65.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (b1gamma65.pts 1) (b1gamma65.pts 2) ^ 2 = (81 : ℝ) ∧
    dist (b1gamma65.pts 2) (b1gamma65.pts 0) ^ 2 = (25 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (32/3 : ℝ) ((2/3 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((4/9 : ℝ)) * rr_sq
  · show dist (mkPt (32/3 : ℝ) ((2/3 : ℝ)*rr)) (mkPt (47/27 : ℝ) ((25/54 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((121/2916 : ℝ)) * rr_sq
  · show dist (mkPt (47/27 : ℝ) ((25/54 : ℝ)*rr)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((625/2916 : ℝ)) * rr_sq

/-- **Escape lemma B1.**  `b1gamma65` is not contained in the target: its vertex `2` lies strictly beyond the target's **left leg**. -/
theorem escape_b1gamma65 : ¬ (b1gamma65.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b1gamma65.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b1gamma65.pts 2 = mkPt (47/27 : ℝ) ((25/54 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_b1gamma56 : det3 (6 : ℝ) (0:ℝ) (89/9 : ℝ) ((5/9 : ℝ)*rr) (8/9 : ℝ) ((5/9 : ℝ)*rr) ≠ 0 := by
  have h : det3 (6 : ℝ) (0:ℝ) (89/9 : ℝ) ((5/9 : ℝ)*rr) (8/9 : ℝ) ((5/9 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `gamma56` at the corner `(6,0)` on the ray `(7/9, √32/9)`. -/
noncomputable def b1gamma56 : Tri := mkTri (6 : ℝ) (0:ℝ) (89/9 : ℝ) ((5/9 : ℝ)*rr) (8/9 : ℝ) ((5/9 : ℝ)*rr) det_b1gamma56

/-- **`b1gamma56` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b1gamma56 :
    dist (b1gamma56.pts 0) (b1gamma56.pts 1) ^ 2 = (25 : ℝ) ∧
    dist (b1gamma56.pts 1) (b1gamma56.pts 2) ^ 2 = (81 : ℝ) ∧
    dist (b1gamma56.pts 2) (b1gamma56.pts 0) ^ 2 = (36 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (89/9 : ℝ) ((5/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq
  · show dist (mkPt (89/9 : ℝ) ((5/9 : ℝ)*rr)) (mkPt (8/9 : ℝ) ((5/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (8/9 : ℝ) ((5/9 : ℝ)*rr)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq

/-- **Escape lemma B1.**  `b1gamma56` is not contained in the target: its vertex `2` lies strictly beyond the target's **left leg**. -/
theorem escape_b1gamma56 : ¬ (b1gamma56.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b1gamma56.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b1gamma56.pts 2 = mkPt (8/9 : ℝ) ((5/9 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

/-- **BLOCKING LEMMA B1.**  At the corner `v = (6,0)` with the forced ray
`d₀ = (7/9, √32/9)`, **every** one of the six oriented placements of a triangle congruent to
`(6,5,9)` with a corner at `v` and an edge along `d₀` escapes the target.  Each is congruent to
the tile (`sides_*`) and none is contained in `target63`.

This is a fact about the target alone: no placed tile is referred to. -/
theorem blocking_B1 :
    ¬ (b1alpha59.carrier ⊆ target63.carrier) ∧
    ¬ (b1alpha95.carrier ⊆ target63.carrier) ∧
    ¬ (b1beta69.carrier ⊆ target63.carrier) ∧
    ¬ (b1beta96.carrier ⊆ target63.carrier) ∧
    ¬ (b1gamma65.carrier ⊆ target63.carrier) ∧
    ¬ (b1gamma56.carrier ⊆ target63.carrier) :=
  ⟨escape_b1alpha59, escape_b1alpha95, escape_b1beta69, escape_b1beta96, escape_b1gamma65, escape_b1gamma56⟩

/-- **The frame of B1.**  Each of the six candidates has its vertex `0` at the corner `v` and
its vertex `1` on the forced ray `v + t·d₀` (`t = 5, 9, 6, 9, 6, 5` respectively) — i.e. they are
placements *at that corner along that ray*, which is what makes `blocking_B1` a statement about
the forced corner and not about six unrelated triangles. -/
theorem B1_frame :
    (b1alpha59.pts 0 = mkPt (6 : ℝ) (0:ℝ) ∧ b1alpha59.pts 1 = mkPt (89/9 : ℝ) ((5/9 : ℝ)*rr)) ∧
    (b1alpha95.pts 0 = mkPt (6 : ℝ) (0:ℝ) ∧ b1alpha95.pts 1 = mkPt (13 : ℝ) ((1 : ℝ)*rr)) ∧
    (b1beta69.pts 0 = mkPt (6 : ℝ) (0:ℝ) ∧ b1beta69.pts 1 = mkPt (32/3 : ℝ) ((2/3 : ℝ)*rr)) ∧
    (b1beta96.pts 0 = mkPt (6 : ℝ) (0:ℝ) ∧ b1beta96.pts 1 = mkPt (13 : ℝ) ((1 : ℝ)*rr)) ∧
    (b1gamma65.pts 0 = mkPt (6 : ℝ) (0:ℝ) ∧ b1gamma65.pts 1 = mkPt (32/3 : ℝ) ((2/3 : ℝ)*rr)) ∧
    (b1gamma56.pts 0 = mkPt (6 : ℝ) (0:ℝ) ∧ b1gamma56.pts 1 = mkPt (89/9 : ℝ) ((5/9 : ℝ)*rr)) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ## 4. Non-vacuity witness for B1 -/

theorem det_w1t0 : det3 (0 : ℝ) (0:ℝ) (6 : ℝ) (0:ℝ) (23/3 : ℝ) ((5/6 : ℝ)*rr) ≠ 0 := by
  have h : det3 (0 : ℝ) (0:ℝ) (6 : ℝ) (0:ℝ) (23/3 : ℝ) ((5/6 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Witness tile 0 of the configuration in which B1 is invoked. -/
noncomputable def w1t0 : Tri := mkTri (0 : ℝ) (0:ℝ) (6 : ℝ) (0:ℝ) (23/3 : ℝ) ((5/6 : ℝ)*rr) det_w1t0

/-- **`w1t0` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_w1t0 :
    dist (w1t0.pts 0) (w1t0.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (w1t0.pts 1) (w1t0.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (w1t0.pts 2) (w1t0.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (0 : ℝ) (0:ℝ)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (23/3 : ℝ) ((5/6 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq
  · show dist (mkPt (23/3 : ℝ) ((5/6 : ℝ)*rr)) (mkPt (0 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq

/-- **`w1t0` lies inside the target.** -/
theorem inside_w1t0 : w1t0.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [w1t0, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

theorem det_w1t1 : det3 (6 : ℝ) (0:ℝ) (15 : ℝ) (0:ℝ) (89/9 : ℝ) ((5/9 : ℝ)*rr) ≠ 0 := by
  have h : det3 (6 : ℝ) (0:ℝ) (15 : ℝ) (0:ℝ) (89/9 : ℝ) ((5/9 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Witness tile 1 of the configuration in which B1 is invoked. -/
noncomputable def w1t1 : Tri := mkTri (6 : ℝ) (0:ℝ) (15 : ℝ) (0:ℝ) (89/9 : ℝ) ((5/9 : ℝ)*rr) det_w1t1

/-- **`w1t1` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_w1t1 :
    dist (w1t1.pts 0) (w1t1.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (w1t1.pts 1) (w1t1.pts 2) ^ 2 = (36 : ℝ) ∧
    dist (w1t1.pts 2) (w1t1.pts 0) ^ 2 = (25 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (89/9 : ℝ) ((5/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq
  · show dist (mkPt (89/9 : ℝ) ((5/9 : ℝ)*rr)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq

/-- **`w1t1` lies inside the target.** -/
theorem inside_w1t1 : w1t1.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [w1t1, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

/-- **`w1t0` and `w1t1` have disjoint interiors.** -/
theorem disj_w1t0_w1t1 : Disjoint (interior w1t0.carrier) (interior w1t1.carrier) := by
  have key : Disjoint (interior w1t0.carrier) (interior w1t1.carrier) :=
    interiors_disjoint_of_separating (lineFun (23/3 : ℝ) ((5/6 : ℝ)*rr) (6 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w1t0, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w1t1, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **Non-vacuity of B1.**  The configuration in which B1 is invoked really exists: two triangles
congruent to `(6,5,9)`, both inside the target, with disjoint interiors, and `(6,0)` is a vertex of
both.  So B1 is not a statement about an empty configuration. -/
theorem B1_witness :
    w1t0.carrier ⊆ target63.carrier ∧ w1t1.carrier ⊆ target63.carrier ∧
    Disjoint (interior w1t0.carrier) (interior w1t1.carrier) ∧
    w1t0.pts 1 = mkPt (6:ℝ) (0:ℝ) ∧ w1t1.pts 0 = mkPt (6:ℝ) (0:ℝ) :=
  ⟨inside_w1t0, inside_w1t1, disj_w1t0_w1t1, rfl, rfl⟩

/-! ## 5. Blocking Lemma **B2** — corner `(15,0)`, ray `(−17/81, 14√32/81)` -/

theorem det_b2alpha59 : det3 (15 : ℝ) (0:ℝ) (1130/81 : ℝ) ((70/81 : ℝ)*rr) (8 : ℝ) ((1 : ℝ)*rr) ≠ 0 := by
  have h : det3 (15 : ℝ) (0:ℝ) (1130/81 : ℝ) ((70/81 : ℝ)*rr) (8 : ℝ) ((1 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `alpha59` at the corner `(15,0)` on the ray `(−17/81, 14√32/81)`. -/
noncomputable def b2alpha59 : Tri := mkTri (15 : ℝ) (0:ℝ) (1130/81 : ℝ) ((70/81 : ℝ)*rr) (8 : ℝ) ((1 : ℝ)*rr) det_b2alpha59

/-- **`b2alpha59` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b2alpha59 :
    dist (b2alpha59.pts 0) (b2alpha59.pts 1) ^ 2 = (25 : ℝ) ∧
    dist (b2alpha59.pts 1) (b2alpha59.pts 2) ^ 2 = (36 : ℝ) ∧
    dist (b2alpha59.pts 2) (b2alpha59.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (1130/81 : ℝ) ((70/81 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((4900/6561 : ℝ)) * rr_sq
  · show dist (mkPt (1130/81 : ℝ) ((70/81 : ℝ)*rr)) (mkPt (8 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((121/6561 : ℝ)) * rr_sq
  · show dist (mkPt (8 : ℝ) ((1 : ℝ)*rr)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq

/-- **Escape lemma B2.**  `b2alpha59` is not contained in the target: its vertex `2` lies strictly beyond the target's **left leg**. -/
theorem escape_b2alpha59 : ¬ (b2alpha59.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b2alpha59.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b2alpha59.pts 2 = mkPt (8 : ℝ) ((1 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_b2alpha95 : det3 (15 : ℝ) (0:ℝ) (118/9 : ℝ) ((14/9 : ℝ)*rr) (100/9 : ℝ) ((5/9 : ℝ)*rr) ≠ 0 := by
  have h : det3 (15 : ℝ) (0:ℝ) (118/9 : ℝ) ((14/9 : ℝ)*rr) (100/9 : ℝ) ((5/9 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `alpha95` at the corner `(15,0)` on the ray `(−17/81, 14√32/81)`. -/
noncomputable def b2alpha95 : Tri := mkTri (15 : ℝ) (0:ℝ) (118/9 : ℝ) ((14/9 : ℝ)*rr) (100/9 : ℝ) ((5/9 : ℝ)*rr) det_b2alpha95

/-- **`b2alpha95` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b2alpha95 :
    dist (b2alpha95.pts 0) (b2alpha95.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (b2alpha95.pts 1) (b2alpha95.pts 2) ^ 2 = (36 : ℝ) ∧
    dist (b2alpha95.pts 2) (b2alpha95.pts 0) ^ 2 = (25 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (118/9 : ℝ) ((14/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((196/81 : ℝ)) * rr_sq
  · show dist (mkPt (118/9 : ℝ) ((14/9 : ℝ)*rr)) (mkPt (100/9 : ℝ) ((5/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq
  · show dist (mkPt (100/9 : ℝ) ((5/9 : ℝ)*rr)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq

/-- **Escape lemma B2.**  `b2alpha95` is not contained in the target: its vertex `1` lies strictly beyond the target's **left leg**. -/
theorem escape_b2alpha95 : ¬ (b2alpha95.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b2alpha95.pts 1) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  have he : b2alpha95.pts 1 = mkPt (118/9 : ℝ) ((14/9 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_b2beta69 : det3 (15 : ℝ) (0:ℝ) (371/27 : ℝ) ((28/27 : ℝ)*rr) (2134/243 : ℝ) ((559/486 : ℝ)*rr) ≠ 0 := by
  have h : det3 (15 : ℝ) (0:ℝ) (371/27 : ℝ) ((28/27 : ℝ)*rr) (2134/243 : ℝ) ((559/486 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `beta69` at the corner `(15,0)` on the ray `(−17/81, 14√32/81)`. -/
noncomputable def b2beta69 : Tri := mkTri (15 : ℝ) (0:ℝ) (371/27 : ℝ) ((28/27 : ℝ)*rr) (2134/243 : ℝ) ((559/486 : ℝ)*rr) det_b2beta69

/-- **`b2beta69` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b2beta69 :
    dist (b2beta69.pts 0) (b2beta69.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (b2beta69.pts 1) (b2beta69.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (b2beta69.pts 2) (b2beta69.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (371/27 : ℝ) ((28/27 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((784/729 : ℝ)) * rr_sq
  · show dist (mkPt (371/27 : ℝ) ((28/27 : ℝ)*rr)) (mkPt (2134/243 : ℝ) ((559/486 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((3025/236196 : ℝ)) * rr_sq
  · show dist (mkPt (2134/243 : ℝ) ((559/486 : ℝ)*rr)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((312481/236196 : ℝ)) * rr_sq

/-- **Escape lemma B2.**  `b2beta69` is not contained in the target: its vertex `2` lies strictly beyond the target's **left leg**. -/
theorem escape_b2beta69 : ¬ (b2beta69.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b2beta69.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b2beta69.pts 2 = mkPt (2134/243 : ℝ) ((559/486 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_b2beta96 : det3 (15 : ℝ) (0:ℝ) (118/9 : ℝ) ((14/9 : ℝ)*rr) (7913/729 : ℝ) ((559/729 : ℝ)*rr) ≠ 0 := by
  have h : det3 (15 : ℝ) (0:ℝ) (118/9 : ℝ) ((14/9 : ℝ)*rr) (7913/729 : ℝ) ((559/729 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `beta96` at the corner `(15,0)` on the ray `(−17/81, 14√32/81)`. -/
noncomputable def b2beta96 : Tri := mkTri (15 : ℝ) (0:ℝ) (118/9 : ℝ) ((14/9 : ℝ)*rr) (7913/729 : ℝ) ((559/729 : ℝ)*rr) det_b2beta96

/-- **`b2beta96` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b2beta96 :
    dist (b2beta96.pts 0) (b2beta96.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (b2beta96.pts 1) (b2beta96.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (b2beta96.pts 2) (b2beta96.pts 0) ^ 2 = (36 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (118/9 : ℝ) ((14/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((196/81 : ℝ)) * rr_sq
  · show dist (mkPt (118/9 : ℝ) ((14/9 : ℝ)*rr)) (mkPt (7913/729 : ℝ) ((559/729 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((330625/531441 : ℝ)) * rr_sq
  · show dist (mkPt (7913/729 : ℝ) ((559/729 : ℝ)*rr)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((312481/531441 : ℝ)) * rr_sq

/-- **Escape lemma B2.**  `b2beta96` is not contained in the target: its vertex `1` lies strictly beyond the target's **left leg**. -/
theorem escape_b2beta96 : ¬ (b2beta96.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b2beta96.pts 1) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  have he : b2beta96.pts 1 = mkPt (118/9 : ℝ) ((14/9 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_b2gamma65 : det3 (15 : ℝ) (0:ℝ) (371/27 : ℝ) ((28/27 : ℝ)*rr) (290/27 : ℝ) ((-25/54 : ℝ)*rr) ≠ 0 := by
  have h : det3 (15 : ℝ) (0:ℝ) (371/27 : ℝ) ((28/27 : ℝ)*rr) (290/27 : ℝ) ((-25/54 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `gamma65` at the corner `(15,0)` on the ray `(−17/81, 14√32/81)`. -/
noncomputable def b2gamma65 : Tri := mkTri (15 : ℝ) (0:ℝ) (371/27 : ℝ) ((28/27 : ℝ)*rr) (290/27 : ℝ) ((-25/54 : ℝ)*rr) det_b2gamma65

/-- **`b2gamma65` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b2gamma65 :
    dist (b2gamma65.pts 0) (b2gamma65.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (b2gamma65.pts 1) (b2gamma65.pts 2) ^ 2 = (81 : ℝ) ∧
    dist (b2gamma65.pts 2) (b2gamma65.pts 0) ^ 2 = (25 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (371/27 : ℝ) ((28/27 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((784/729 : ℝ)) * rr_sq
  · show dist (mkPt (371/27 : ℝ) ((28/27 : ℝ)*rr)) (mkPt (290/27 : ℝ) ((-25/54 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((9/4 : ℝ)) * rr_sq
  · show dist (mkPt (290/27 : ℝ) ((-25/54 : ℝ)*rr)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((625/2916 : ℝ)) * rr_sq

/-- **Escape lemma B2.**  `b2gamma65` is not contained in the target: its vertex `2` lies strictly **below the base**. -/
theorem escape_b2gamma65 : ¬ (b2gamma65.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b2gamma65.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b2gamma65.pts 2 = mkPt (290/27 : ℝ) ((-25/54 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_below (by nlinarith [rr_pos]) hv

theorem det_b2gamma56 : det3 (15 : ℝ) (0:ℝ) (1130/81 : ℝ) ((70/81 : ℝ)*rr) (89/9 : ℝ) ((-5/9 : ℝ)*rr) ≠ 0 := by
  have h : det3 (15 : ℝ) (0:ℝ) (1130/81 : ℝ) ((70/81 : ℝ)*rr) (89/9 : ℝ) ((-5/9 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Candidate `gamma56` at the corner `(15,0)` on the ray `(−17/81, 14√32/81)`. -/
noncomputable def b2gamma56 : Tri := mkTri (15 : ℝ) (0:ℝ) (1130/81 : ℝ) ((70/81 : ℝ)*rr) (89/9 : ℝ) ((-5/9 : ℝ)*rr) det_b2gamma56

/-- **`b2gamma56` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_b2gamma56 :
    dist (b2gamma56.pts 0) (b2gamma56.pts 1) ^ 2 = (25 : ℝ) ∧
    dist (b2gamma56.pts 1) (b2gamma56.pts 2) ^ 2 = (81 : ℝ) ∧
    dist (b2gamma56.pts 2) (b2gamma56.pts 0) ^ 2 = (36 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (1130/81 : ℝ) ((70/81 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((4900/6561 : ℝ)) * rr_sq
  · show dist (mkPt (1130/81 : ℝ) ((70/81 : ℝ)*rr)) (mkPt (89/9 : ℝ) ((-5/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((13225/6561 : ℝ)) * rr_sq
  · show dist (mkPt (89/9 : ℝ) ((-5/9 : ℝ)*rr)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq

/-- **Escape lemma B2.**  `b2gamma56` is not contained in the target: its vertex `2` lies strictly **below the base**. -/
theorem escape_b2gamma56 : ¬ (b2gamma56.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (b2gamma56.pts 2) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : b2gamma56.pts 2 = mkPt (89/9 : ℝ) ((-5/9 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_below (by nlinarith [rr_pos]) hv

/-- **BLOCKING LEMMA B2.**  At the corner `v = (15,0)` with the forced ray
`d₀ = (−17/81, 14√32/81)`, every one of the six oriented placements of a triangle congruent to
`(6,5,9)` with a corner at `v` and an edge along `d₀` escapes the target — four through the left
leg, two below the base.  Again a fact about the target alone. -/
theorem blocking_B2 :
    ¬ (b2alpha59.carrier ⊆ target63.carrier) ∧
    ¬ (b2alpha95.carrier ⊆ target63.carrier) ∧
    ¬ (b2beta69.carrier ⊆ target63.carrier) ∧
    ¬ (b2beta96.carrier ⊆ target63.carrier) ∧
    ¬ (b2gamma65.carrier ⊆ target63.carrier) ∧
    ¬ (b2gamma56.carrier ⊆ target63.carrier) :=
  ⟨escape_b2alpha59, escape_b2alpha95, escape_b2beta69, escape_b2beta96, escape_b2gamma65, escape_b2gamma56⟩

/-- **The frame of B2.**  Each of the six candidates has its vertex `0` at the corner `v` and
its vertex `1` on the forced ray `v + t·d₀` (`t = 5, 9, 6, 9, 6, 5` respectively) — i.e. they are
placements *at that corner along that ray*, which is what makes `blocking_B2` a statement about
the forced corner and not about six unrelated triangles. -/
theorem B2_frame :
    (b2alpha59.pts 0 = mkPt (15 : ℝ) (0:ℝ) ∧ b2alpha59.pts 1 = mkPt (1130/81 : ℝ) ((70/81 : ℝ)*rr)) ∧
    (b2alpha95.pts 0 = mkPt (15 : ℝ) (0:ℝ) ∧ b2alpha95.pts 1 = mkPt (118/9 : ℝ) ((14/9 : ℝ)*rr)) ∧
    (b2beta69.pts 0 = mkPt (15 : ℝ) (0:ℝ) ∧ b2beta69.pts 1 = mkPt (371/27 : ℝ) ((28/27 : ℝ)*rr)) ∧
    (b2beta96.pts 0 = mkPt (15 : ℝ) (0:ℝ) ∧ b2beta96.pts 1 = mkPt (118/9 : ℝ) ((14/9 : ℝ)*rr)) ∧
    (b2gamma65.pts 0 = mkPt (15 : ℝ) (0:ℝ) ∧ b2gamma65.pts 1 = mkPt (371/27 : ℝ) ((28/27 : ℝ)*rr)) ∧
    (b2gamma56.pts 0 = mkPt (15 : ℝ) (0:ℝ) ∧ b2gamma56.pts 1 = mkPt (1130/81 : ℝ) ((70/81 : ℝ)*rr)) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ## 6. Non-vacuity witness for B2 — the six-tile configuration -/

theorem det_w2t0 : det3 (0 : ℝ) (0:ℝ) (6 : ℝ) (0:ℝ) (23/3 : ℝ) ((5/6 : ℝ)*rr) ≠ 0 := by
  have h : det3 (0 : ℝ) (0:ℝ) (6 : ℝ) (0:ℝ) (23/3 : ℝ) ((5/6 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Witness tile 0 of the six-tile configuration in which B2 is invoked. -/
noncomputable def w2t0 : Tri := mkTri (0 : ℝ) (0:ℝ) (6 : ℝ) (0:ℝ) (23/3 : ℝ) ((5/6 : ℝ)*rr) det_w2t0

/-- **`w2t0` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_w2t0 :
    dist (w2t0.pts 0) (w2t0.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (w2t0.pts 1) (w2t0.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (w2t0.pts 2) (w2t0.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (0 : ℝ) (0:ℝ)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (23/3 : ℝ) ((5/6 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq
  · show dist (mkPt (23/3 : ℝ) ((5/6 : ℝ)*rr)) (mkPt (0 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq

/-- **`w2t0` lies inside the target.** -/
theorem inside_w2t0 : w2t0.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [w2t0, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

theorem det_w2t1 : det3 (6 : ℝ) (0:ℝ) (15 : ℝ) (0:ℝ) (100/9 : ℝ) ((5/9 : ℝ)*rr) ≠ 0 := by
  have h : det3 (6 : ℝ) (0:ℝ) (15 : ℝ) (0:ℝ) (100/9 : ℝ) ((5/9 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Witness tile 1 of the six-tile configuration in which B2 is invoked. -/
noncomputable def w2t1 : Tri := mkTri (6 : ℝ) (0:ℝ) (15 : ℝ) (0:ℝ) (100/9 : ℝ) ((5/9 : ℝ)*rr) det_w2t1

/-- **`w2t1` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_w2t1 :
    dist (w2t1.pts 0) (w2t1.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (w2t1.pts 1) (w2t1.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (w2t1.pts 2) (w2t1.pts 0) ^ 2 = (36 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (100/9 : ℝ) ((5/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq
  · show dist (mkPt (100/9 : ℝ) ((5/9 : ℝ)*rr)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq

/-- **`w2t1` lies inside the target.** -/
theorem inside_w2t1 : w2t1.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [w2t1, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

theorem det_w2t2 : det3 (6 : ℝ) (0:ℝ) (41/3 : ℝ) ((5/6 : ℝ)*rr) (23/3 : ℝ) ((5/6 : ℝ)*rr) ≠ 0 := by
  have h : det3 (6 : ℝ) (0:ℝ) (41/3 : ℝ) ((5/6 : ℝ)*rr) (23/3 : ℝ) ((5/6 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Witness tile 2 of the six-tile configuration in which B2 is invoked. -/
noncomputable def w2t2 : Tri := mkTri (6 : ℝ) (0:ℝ) (41/3 : ℝ) ((5/6 : ℝ)*rr) (23/3 : ℝ) ((5/6 : ℝ)*rr) det_w2t2

/-- **`w2t2` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_w2t2 :
    dist (w2t2.pts 0) (w2t2.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (w2t2.pts 1) (w2t2.pts 2) ^ 2 = (36 : ℝ) ∧
    dist (w2t2.pts 2) (w2t2.pts 0) ^ 2 = (25 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (6 : ℝ) (0:ℝ)) (mkPt (41/3 : ℝ) ((5/6 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq
  · show dist (mkPt (41/3 : ℝ) ((5/6 : ℝ)*rr)) (mkPt (23/3 : ℝ) ((5/6 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (23/3 : ℝ) ((5/6 : ℝ)*rr)) (mkPt (6 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq

/-- **`w2t2` lies inside the target.** -/
theorem inside_w2t2 : w2t2.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [w2t2, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

theorem det_w2t3 : det3 (15 : ℝ) (0:ℝ) (20 : ℝ) (0:ℝ) (22 : ℝ) ((1 : ℝ)*rr) ≠ 0 := by
  have h : det3 (15 : ℝ) (0:ℝ) (20 : ℝ) (0:ℝ) (22 : ℝ) ((1 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Witness tile 3 of the six-tile configuration in which B2 is invoked. -/
noncomputable def w2t3 : Tri := mkTri (15 : ℝ) (0:ℝ) (20 : ℝ) (0:ℝ) (22 : ℝ) ((1 : ℝ)*rr) det_w2t3

/-- **`w2t3` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_w2t3 :
    dist (w2t3.pts 0) (w2t3.pts 1) ^ 2 = (25 : ℝ) ∧
    dist (w2t3.pts 1) (w2t3.pts 2) ^ 2 = (36 : ℝ) ∧
    dist (w2t3.pts 2) (w2t3.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (20 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (20 : ℝ) (0:ℝ)) (mkPt (22 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq
  · show dist (mkPt (22 : ℝ) ((1 : ℝ)*rr)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq

/-- **`w2t3` lies inside the target.** -/
theorem inside_w2t3 : w2t3.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [w2t3, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

theorem det_w2t4 : det3 (15 : ℝ) (0:ℝ) (59/3 : ℝ) ((2/3 : ℝ)*rr) (18 : ℝ) ((3/2 : ℝ)*rr) ≠ 0 := by
  have h : det3 (15 : ℝ) (0:ℝ) (59/3 : ℝ) ((2/3 : ℝ)*rr) (18 : ℝ) ((3/2 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Witness tile 4 of the six-tile configuration in which B2 is invoked. -/
noncomputable def w2t4 : Tri := mkTri (15 : ℝ) (0:ℝ) (59/3 : ℝ) ((2/3 : ℝ)*rr) (18 : ℝ) ((3/2 : ℝ)*rr) det_w2t4

/-- **`w2t4` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_w2t4 :
    dist (w2t4.pts 0) (w2t4.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (w2t4.pts 1) (w2t4.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (w2t4.pts 2) (w2t4.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (59/3 : ℝ) ((2/3 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((4/9 : ℝ)) * rr_sq
  · show dist (mkPt (59/3 : ℝ) ((2/3 : ℝ)*rr)) (mkPt (18 : ℝ) ((3/2 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq
  · show dist (mkPt (18 : ℝ) ((3/2 : ℝ)*rr)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((9/4 : ℝ)) * rr_sq

/-- **`w2t4` lies inside the target.** -/
theorem inside_w2t4 : w2t4.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [w2t4, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

theorem det_w2t5 : det3 (15 : ℝ) (0:ℝ) (18 : ℝ) ((3/2 : ℝ)*rr) (371/27 : ℝ) ((28/27 : ℝ)*rr) ≠ 0 := by
  have h : det3 (15 : ℝ) (0:ℝ) (18 : ℝ) ((3/2 : ℝ)*rr) (371/27 : ℝ) ((28/27 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- Witness tile 5 of the six-tile configuration in which B2 is invoked. -/
noncomputable def w2t5 : Tri := mkTri (15 : ℝ) (0:ℝ) (18 : ℝ) ((3/2 : ℝ)*rr) (371/27 : ℝ) ((28/27 : ℝ)*rr) det_w2t5

/-- **`w2t5` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_w2t5 :
    dist (w2t5.pts 0) (w2t5.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (w2t5.pts 1) (w2t5.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (w2t5.pts 2) (w2t5.pts 0) ^ 2 = (36 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (15 : ℝ) (0:ℝ)) (mkPt (18 : ℝ) ((3/2 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((9/4 : ℝ)) * rr_sq
  · show dist (mkPt (18 : ℝ) ((3/2 : ℝ)*rr)) (mkPt (371/27 : ℝ) ((28/27 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((625/2916 : ℝ)) * rr_sq
  · show dist (mkPt (371/27 : ℝ) ((28/27 : ℝ)*rr)) (mkPt (15 : ℝ) (0:ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((784/729 : ℝ)) * rr_sq

/-- **`w2t5` lies inside the target.** -/
theorem inside_w2t5 : w2t5.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [w2t5, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

/-- **`w2t0` and `w2t1` have disjoint interiors.** -/
theorem disj_w2t0_w2t1 : Disjoint (interior w2t0.carrier) (interior w2t1.carrier) := by
  have key : Disjoint (interior w2t0.carrier) (interior w2t1.carrier) :=
    interiors_disjoint_of_separating (lineFun (23/3 : ℝ) ((5/6 : ℝ)*rr) (6 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t0, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t1, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t0` and `w2t2` have disjoint interiors.** -/
theorem disj_w2t0_w2t2 : Disjoint (interior w2t0.carrier) (interior w2t2.carrier) := by
  have key : Disjoint (interior w2t0.carrier) (interior w2t2.carrier) :=
    interiors_disjoint_of_separating (lineFun (23/3 : ℝ) ((5/6 : ℝ)*rr) (6 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t0, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t2, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t0` and `w2t3` have disjoint interiors.** -/
theorem disj_w2t0_w2t3 : Disjoint (interior w2t0.carrier) (interior w2t3.carrier) := by
  have key : Disjoint (interior w2t0.carrier) (interior w2t3.carrier) :=
    interiors_disjoint_of_separating (lineFun (23/3 : ℝ) ((5/6 : ℝ)*rr) (6 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t0, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t3, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t0` and `w2t4` have disjoint interiors.** -/
theorem disj_w2t0_w2t4 : Disjoint (interior w2t0.carrier) (interior w2t4.carrier) := by
  have key : Disjoint (interior w2t0.carrier) (interior w2t4.carrier) :=
    interiors_disjoint_of_separating (lineFun (23/3 : ℝ) ((5/6 : ℝ)*rr) (6 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t0, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t4, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t0` and `w2t5` have disjoint interiors.** -/
theorem disj_w2t0_w2t5 : Disjoint (interior w2t0.carrier) (interior w2t5.carrier) := by
  have key : Disjoint (interior w2t0.carrier) (interior w2t5.carrier) :=
    interiors_disjoint_of_separating (lineFun (23/3 : ℝ) ((5/6 : ℝ)*rr) (6 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t0, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t5, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t1` and `w2t2` have disjoint interiors.** -/
theorem disj_w2t1_w2t2 : Disjoint (interior w2t1.carrier) (interior w2t2.carrier) := by
  have key : Disjoint (interior w2t1.carrier) (interior w2t2.carrier) :=
    interiors_disjoint_of_separating (lineFun (6 : ℝ) (0:ℝ) (100/9 : ℝ) ((5/9 : ℝ)*rr))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t1, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t2, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t1` and `w2t3` have disjoint interiors.** -/
theorem disj_w2t1_w2t3 : Disjoint (interior w2t1.carrier) (interior w2t3.carrier) := by
  have key : Disjoint (interior w2t1.carrier) (interior w2t3.carrier) :=
    interiors_disjoint_of_separating (lineFun (100/9 : ℝ) ((5/9 : ℝ)*rr) (15 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t1, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t3, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t1` and `w2t4` have disjoint interiors.** -/
theorem disj_w2t1_w2t4 : Disjoint (interior w2t1.carrier) (interior w2t4.carrier) := by
  have key : Disjoint (interior w2t1.carrier) (interior w2t4.carrier) :=
    interiors_disjoint_of_separating (lineFun (100/9 : ℝ) ((5/9 : ℝ)*rr) (15 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t1, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t4, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t1` and `w2t5` have disjoint interiors.** -/
theorem disj_w2t1_w2t5 : Disjoint (interior w2t1.carrier) (interior w2t5.carrier) := by
  have key : Disjoint (interior w2t1.carrier) (interior w2t5.carrier) :=
    interiors_disjoint_of_separating (lineFun (100/9 : ℝ) ((5/9 : ℝ)*rr) (15 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t1, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t5, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t2` and `w2t3` have disjoint interiors.** -/
theorem disj_w2t2_w2t3 : Disjoint (interior w2t2.carrier) (interior w2t3.carrier) := by
  have key : Disjoint (interior w2t2.carrier) (interior w2t3.carrier) :=
    interiors_disjoint_of_separating (lineFun (41/3 : ℝ) ((5/6 : ℝ)*rr) (6 : ℝ) (0:ℝ))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t2, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t3, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t2` and `w2t4` have disjoint interiors.** -/
theorem disj_w2t2_w2t4 : Disjoint (interior w2t2.carrier) (interior w2t4.carrier) := by
  have key : Disjoint (interior w2t4.carrier) (interior w2t2.carrier) :=
    interiors_disjoint_of_separating (lineFun (15 : ℝ) (0:ℝ) (18 : ℝ) ((3/2 : ℝ)*rr))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t4, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t2, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key.symm

/-- **`w2t2` and `w2t5` have disjoint interiors.** -/
theorem disj_w2t2_w2t5 : Disjoint (interior w2t2.carrier) (interior w2t5.carrier) := by
  have key : Disjoint (interior w2t5.carrier) (interior w2t2.carrier) :=
    interiors_disjoint_of_separating (lineFun (15 : ℝ) (0:ℝ) (371/27 : ℝ) ((28/27 : ℝ)*rr))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t5, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t2, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key.symm

/-- **`w2t3` and `w2t4` have disjoint interiors.** -/
theorem disj_w2t3_w2t4 : Disjoint (interior w2t3.carrier) (interior w2t4.carrier) := by
  have key : Disjoint (interior w2t3.carrier) (interior w2t4.carrier) :=
    interiors_disjoint_of_separating (lineFun (15 : ℝ) (0:ℝ) (22 : ℝ) ((1 : ℝ)*rr))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t3, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t4, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t3` and `w2t5` have disjoint interiors.** -/
theorem disj_w2t3_w2t5 : Disjoint (interior w2t3.carrier) (interior w2t5.carrier) := by
  have key : Disjoint (interior w2t3.carrier) (interior w2t5.carrier) :=
    interiors_disjoint_of_separating (lineFun (15 : ℝ) (0:ℝ) (22 : ℝ) ((1 : ℝ)*rr))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t3, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t5, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **`w2t4` and `w2t5` have disjoint interiors.** -/
theorem disj_w2t4_w2t5 : Disjoint (interior w2t4.carrier) (interior w2t5.carrier) := by
  have key : Disjoint (interior w2t4.carrier) (interior w2t5.carrier) :=
    interiors_disjoint_of_separating (lineFun (15 : ℝ) (0:ℝ) (18 : ℝ) ((3/2 : ℝ)*rr))
      (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (le_of_forall_pts_le _ (by
        intro k; fin_cases k <;>
          simp [w2t4, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
      (ge_of_forall_pts_ge _ (by
        intro k; fin_cases k <;>
          simp [w2t5, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
          nlinarith [rr_pos]))
  exact key

/-- **Non-vacuity of B2.**  The six-tile configuration in which B2 is invoked really exists:
six triangles each congruent to `(6,5,9)` (`sides_w2t*`), each inside the target (`inside_w2t*`),
with pairwise disjoint interiors.  So B2 is invoked at a configuration that is not empty. -/
theorem B2_witness :
    w2t0.carrier ⊆ target63.carrier ∧
    w2t1.carrier ⊆ target63.carrier ∧
    w2t2.carrier ⊆ target63.carrier ∧
    w2t3.carrier ⊆ target63.carrier ∧
    w2t4.carrier ⊆ target63.carrier ∧
    w2t5.carrier ⊆ target63.carrier ∧
    Disjoint (interior w2t0.carrier) (interior w2t1.carrier) ∧
    Disjoint (interior w2t0.carrier) (interior w2t2.carrier) ∧
    Disjoint (interior w2t0.carrier) (interior w2t3.carrier) ∧
    Disjoint (interior w2t0.carrier) (interior w2t4.carrier) ∧
    Disjoint (interior w2t0.carrier) (interior w2t5.carrier) ∧
    Disjoint (interior w2t1.carrier) (interior w2t2.carrier) ∧
    Disjoint (interior w2t1.carrier) (interior w2t3.carrier) ∧
    Disjoint (interior w2t1.carrier) (interior w2t4.carrier) ∧
    Disjoint (interior w2t1.carrier) (interior w2t5.carrier) ∧
    Disjoint (interior w2t2.carrier) (interior w2t3.carrier) ∧
    Disjoint (interior w2t2.carrier) (interior w2t4.carrier) ∧
    Disjoint (interior w2t2.carrier) (interior w2t5.carrier) ∧
    Disjoint (interior w2t3.carrier) (interior w2t4.carrier) ∧
    Disjoint (interior w2t3.carrier) (interior w2t5.carrier) ∧
    Disjoint (interior w2t4.carrier) (interior w2t5.carrier) :=
  ⟨inside_w2t0, inside_w2t1, inside_w2t2, inside_w2t3, inside_w2t4, inside_w2t5, disj_w2t0_w2t1, disj_w2t0_w2t2, disj_w2t0_w2t3, disj_w2t0_w2t4, disj_w2t0_w2t5, disj_w2t1_w2t2, disj_w2t1_w2t3, disj_w2t1_w2t4, disj_w2t1_w2t5, disj_w2t2_w2t3, disj_w2t2_w2t4, disj_w2t2_w2t5, disj_w2t3_w2t4, disj_w2t3_w2t5, disj_w2t4_w2t5⟩

/-! ## 7. Axiom check -/

#print axioms blocking_B1
#print axioms B1_frame
#print axioms B2_frame
#print axioms blocking_B2
#print axioms B1_witness
#print axioms B2_witness
#print axioms target63_carrier_eq

end Erdos634.ThickBlockingLemmas
