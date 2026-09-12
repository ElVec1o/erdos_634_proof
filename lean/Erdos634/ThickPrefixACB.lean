import Erdos634.BaseBetaTargetCoord
import Erdos634.CertGeom

/-!
# The `a c b` prefix kill at thick base-`β` members, **parametric in `f`** (`e = f − 1`, `f ≥ 6`)

Erdős #634, base-`β` branch, the thick family `e = f − 1` (`N = 2f² + 2f − 1`: `83, 111, 143, 179, …`;
`N = 83` is `f = 6`).  Tile `(a,b,c) = (f² − f, 2f − 1, f²)`; field `ℚ(√D)`, `D = 4f² − (f−1)² = 3f² + 2f − 1`;
target `(0,0)–(L,0)–(L/2, H)` with `L = (f−1)(2f² + 2f − 1)`, `H = (2f−1)√D/2` — this is
`BaseBetaTargetCoord.baseBetaTarget (f−1) f` on the nose (`tgt_carrier_eq`).

## Provenance

Room `e2b3`'s **Lemma P** (`report_ramanujan.md` §5) kills every base word beginning `a c b` at
`(e,f) = (2,3)` in a 13-node, 6-tile exhaustion.  The 2026-09-12 prefix-lift attack
(`private/ROOM/attack/report_prefixlift.md`) re-ran that exhaustion with tile and target as exact
functions of `(e,f)`: on the whole family `e = f−1`, `f ≥ 6`, the prefix `a c b` dies in **one and the
same 6-node, 3-tile tree** — same forced corners, same rays, same placement types, and the *same
rejection reason for every candidate* — and every rejection is an escape through the target's **left
leg**, i.e. a single affine functional applied to one explicit vertex.  Exact validity region: the
tree is identical for every member with `e/f > t* = 0.82578…`, the largest root of
`t⁴ − t³ − 4t² + t + 2` (the binding candidate is `α(b on ray, c off)` at `(a+c, 0)`); for
`e = f−1` that is exactly `f ≥ 6`.

## What is proved here (all for real `f ≥ 6`, `e := f − 1`)

* `tgt f hf` — the target; `tgt_carrier_eq` identifies it with `baseBetaTarget (f−1) f`;
  `not_mem_tgt_of_left`, `mem_tgt` — the left-leg escape test and the containment test.
* **Twenty-three escape facts** `esc_*`: at each of the six nodes of the tree, for each candidate
  placement that the exhaustion rejects for a geometric reason, the named off-ray (or on-ray) vertex
  lies strictly beyond the left leg, hence the candidate triangle is not contained in the target
  (`blocking_N0`, …, `blocking_N5` collect them per node).  Each candidate is an explicit `Tri` with
  its frame recorded (`frame_*`: vertex `0` is the corner, vertex `1` is on the forced ray).
* **The configurations are real**: `T1, T2a, T2b, T3, T3p` are the tiles of the tree's five
  placements; each is congruent to the tile (`sides_*`: squared sides `a², b², c²`), inside the
  target (`inside_*`), and the three node-configurations `{T1,T2a}`, `{T1,T2b,T3}`, `{T1,T2b,T3p}`
  have pairwise disjoint interiors (`disj_*`).  So no hypothesis below is vacuous: `f = 6` and
  `f = 7` are literal instances (`witness_83`, `witness_111`).

## What is **not** proved here

* The **covering claim** — "hence no dissection of the target has a base word beginning `a c b`" —
  is not formalised.  It needs the completeness of the constructor's placement rule (the geometric
  half of H7: at the lexicographically minimal uncovered point every covering tile has a corner
  there with an edge along the boundary ray, so the six oriented placements are *all* of them).
  That hypothesis is discharged nowhere in the corpus, and a Lean statement carrying it would be the
  `word42_junction_dies` trap.  The base-rule rejections (a base edge must be a whole block of the
  prefix) are word-level and not stated here; the single aperture rejection (node `N5`, candidate
  `γ(a on ray, b off)`, which overlaps `T1`) is not stated here.
* Nothing at `e ≠ f − 1`, and nothing at `f ≤ 5` (at `f = 5` the binding inequality fails and the
  tree has 9 nodes; at `f = 3` it is Lemma P's 13).

No `sorry`; axioms are the standard three.
-/

namespace Erdos634.ThickPrefixACB

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.BaseBetaTargetCoord

/-! ## 1. The surd, the target -/

/-- `D(f) = 4f² − (f−1)² = 3f² + 2f − 1`. -/
noncomputable def Dq (f : ℝ) : ℝ := 3*f^2 + 2*f - 1
/-- `rr f = √D`. -/
noncomputable def rr (f : ℝ) : ℝ := Real.sqrt (Dq f)
/-- `L = e·N = (f−1)(3f² − (f−1)²) = (f−1)(2f² + 2f − 1)`. -/
noncomputable def Lq (f : ℝ) : ℝ := (f-1)*(2*f^2+2*f-1)
/-- `H = b√D/2 = (2f−1)√D/2`. -/
noncomputable def Hq (f : ℝ) : ℝ := (2*f-1)/2 * rr f

theorem Dq_pos {f : ℝ} (hf : 6 ≤ f) : 0 < Dq f := by unfold Dq; nlinarith
theorem rr_pos {f : ℝ} (hf : 6 ≤ f) : 0 < rr f := Real.sqrt_pos.mpr (Dq_pos hf)
theorem rr_sq {f : ℝ} (hf : 6 ≤ f) : rr f ^ 2 = Dq f := Real.sq_sqrt (le_of_lt (Dq_pos hf))
theorem Lq_pos {f : ℝ} (hf : 6 ≤ f) : 0 < Lq f := by unfold Lq; nlinarith
theorem Hq_pos {f : ℝ} (hf : 6 ≤ f) : 0 < Hq f := by
  unfold Hq; exact mul_pos (by linarith) (rr_pos hf)

theorem det_tgt {f : ℝ} (hf : 6 ≤ f) : det3 (0:ℝ) (0:ℝ) (Lq f) (0:ℝ) (Lq f / 2) (Hq f) ≠ 0 := by
  have h : det3 (0:ℝ) (0:ℝ) (Lq f) (0:ℝ) (Lq f / 2) (Hq f) = Lq f * Hq f := by unfold det3; ring
  rw [h]; exact ne_of_gt (mul_pos (Lq_pos hf) (Hq_pos hf))

/-- The thick base-`β` target at `(e,f) = (f−1, f)`. -/
noncomputable def tgt (f : ℝ) (hf : 6 ≤ f) : Tri := mkTri 0 0 (Lq f) 0 (Lq f / 2) (Hq f) (det_tgt hf)

theorem baseLen_eq {f : ℝ} : baseLen (f-1) f = Lq f := by unfold baseLen Nq Lq; ring
theorem height_eq {f : ℝ} (hf : 6 ≤ f) : height (f-1) f = Hq f := by
  unfold height Dr Hq rr Dq
  have : (4 * f ^ 2 - (f - 1) ^ 2) = 3*f^2 + 2*f - 1 := by ring
  rw [this]; ring

/-- **The model is the corpus's `baseBetaTarget (f−1) f`.**  Not a new convention. -/
theorem tgt_carrier_eq {f : ℝ} (hf : 6 ≤ f) :
    (tgt f hf).carrier = (baseBetaTarget (f-1) f (by linarith) (by linarith)).carrier := by
  have hpts : (tgt f hf).pts = (baseBetaTarget (f-1) f (by linarith) (by linarith)).pts := by
    funext k
    fin_cases k
    · rfl
    · show mkPt (Lq f) 0 = mkPt (baseLen (f-1) f) 0
      rw [baseLen_eq]
    · show mkPt (Lq f / 2) (Hq f) = mkPt (baseLen (f-1) f / 2) (height (f-1) f)
      rw [baseLen_eq, height_eq hf]
  unfold Tri.carrier
  rw [hpts]

/-- **Beyond the left leg is outside the target.**  The left leg carries the functional
`H·x − (L/2)·y`, nonnegative on the target; a point with it negative is outside. -/
theorem not_mem_tgt_of_left {f : ℝ} (hf : 6 ≤ f) {x y : ℝ} (h : 0 < Lq f / 2 * y - Hq f * x) :
    mkPt x y ∉ (tgt f hf).carrier := by
  intro hm
  have hL := Lq_pos hf; have hH := Hq_pos hf
  have hb : ∀ z ∈ (tgt f hf).carrier, lineFun 0 0 (Lq f / 2) (Hq f) z ≤ 0 := by
    refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k <;>
      simp [tgt, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
      nlinarith [mul_pos hL hH]
  have := hb _ hm
  simp only [lineFun_apply, mkPt_zero, mkPt_one] at this
  nlinarith

/-- **The containment test.** -/
theorem mem_tgt {f : ℝ} (hf : 6 ≤ f) {x y : ℝ} (hb : 0 ≤ y) (hl : 0 ≤ Hq f * x - Lq f / 2 * y)
    (hr : 0 ≤ Hq f * (Lq f - x) - Lq f / 2 * y) : mkPt x y ∈ (tgt f hf).carrier := by
  have hL := Lq_pos hf; have hH := Hq_pos hf
  refine mem_carrier_of_dets (x₀ := 0) (y₀ := 0) (x₁ := Lq f) (y₁ := 0) (x₂ := Lq f / 2) (y₂ := Hq f)
    ?_ ?_ ?_ ?_
  · have h : det3 (0:ℝ) (0:ℝ) (Lq f) (0:ℝ) (Lq f / 2) (Hq f) = Lq f * Hq f := by unfold det3; ring
    rw [h]; exact mul_pos hL hH
  · unfold det3; nlinarith [hr]
  · unfold det3; nlinarith [hl]
  · unfold det3; nlinarith [hb]

/-- The affine functional bounded below at the vertices is bounded below on the carrier. -/
theorem ge_of_forall_pts_ge {t : Tri} (g : Plane →ᵃ[ℝ] ℝ) {c : ℝ} (h : ∀ k, c ≤ g (t.pts k)) :
    ∀ x ∈ t.carrier, c ≤ g x := by
  have hconv : Convex ℝ (g ⁻¹' Set.Ici c) := (convex_Ici c).affine_preimage g
  have hsub : t.carrier ⊆ g ⁻¹' Set.Ici c :=
    convexHull_min (Set.range_subset_iff.mpr h) hconv
  exact fun x hx => hsub hx

/-! ## 2. The five placed tiles of the tree -/

theorem det_T1 {f : ℝ} (hf : 6 ≤ f) :
    det3 (0 : ℝ) (0:ℝ) (f^2 - f : ℝ) (0:ℝ) ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (0 : ℝ) (0:ℝ) (f^2 - f : ℝ) (0:ℝ) ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- `T1`: the corner tile, `β` at `(0,0)`, `a` on the base — node `N0`'s unique placement. -/
noncomputable def T1 (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (0 : ℝ) (0:ℝ) (f^2 - f : ℝ) (0:ℝ) ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (det_T1 hf)

theorem sides_T1 {f : ℝ} (hf : 6 ≤ f) :
    dist ((T1 f hf).pts 0) ((T1 f hf).pts 1) ^ 2 = (f^4 - 2*f^3 + f^2 : ℝ) ∧
    dist ((T1 f hf).pts 1) ((T1 f hf).pts 2) ^ 2 = (4*f^2 - 4*f + 1 : ℝ) ∧
    dist ((T1 f hf).pts 2) ((T1 f hf).pts 0) ^ 2 = (f^4 : ℝ) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have hr2 := rr_sq hf
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (0 : ℝ) ((0:ℝ))) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) ((0 : ℝ)) * hr2
  · show dist (mkPt (f^2 - f : ℝ) ((0:ℝ))) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^2 - 4*f + 1) / (4*f^2) : ℝ)) * hr2
  · show dist (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) (mkPt (0 : ℝ) ((0:ℝ))) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^2 - 4*f + 1) / (4*f^2) : ℝ)) * hr2

theorem inside_T1 {f : ℝ} (hf : 6 ≤ f) : (T1 f hf).carrier ⊆ (tgt f hf).carrier := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k
  · show mkPt (0 : ℝ) (0:ℝ) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_refl 0
    · have key : Hq f * (0 : ℝ) - Lq f / 2 * (0:ℝ) = 0 := by
        unfold Lq Hq; field_simp; ring
      rw [key]
    · have key : Hq f * (Lq f - (0 : ℝ)) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity)))
  · show mkPt (f^2 - f : ℝ) (0:ℝ) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_refl 0
    · have key : Hq f * (f^2 - f : ℝ) - Lq f / 2 * (0:ℝ) = rr f * ((2*f^3 - 3*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - (f^2 - f : ℝ)) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity)))
  · show mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_of_lt (mul_pos (div_pos (by nlinarith [h6]) (mul_pos (by norm_num) hfpos)) hr)
    · have key : Hq f * ((2*f^3 - 3*f + 1) / (2*f) : ℝ) - Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) = 0 := by
        unfold Lq Hq; field_simp; ring
      rw [key]
    · have key : Hq f * (Lq f - ((2*f^3 - 3*f + 1) / (2*f) : ℝ)) - Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2 * f : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5]) (mul_pos (by norm_num) hfpos)))

theorem det_T2a {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) (2*f^2 - f : ℝ) (0:ℝ) ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) (2*f^2 - f : ℝ) (0:ℝ) ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- `T2a`: `α(c on base, b off)` at `(a,0)` — node `N1`'s first placement (leads to `N2`). -/
noncomputable def T2a (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) (2*f^2 - f : ℝ) (0:ℝ) ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (det_T2a hf)

theorem sides_T2a {f : ℝ} (hf : 6 ≤ f) :
    dist ((T2a f hf).pts 0) ((T2a f hf).pts 1) ^ 2 = (f^4 : ℝ) ∧
    dist ((T2a f hf).pts 1) ((T2a f hf).pts 2) ^ 2 = (f^4 - 2*f^3 + f^2 : ℝ) ∧
    dist ((T2a f hf).pts 2) ((T2a f hf).pts 0) ^ 2 = (4*f^2 - 4*f + 1 : ℝ) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have hr2 := rr_sq hf
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (f^2 - f : ℝ) ((0:ℝ))) (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) ((0 : ℝ)) * hr2
  · show dist (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) (mkPt ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^4 - 12*f^3 + 13*f^2 - 6*f + 1) / (4*f^4) : ℝ)) * hr2
  · show dist (mkPt ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^4 - 12*f^3 + 13*f^2 - 6*f + 1) / (4*f^4) : ℝ)) * hr2

theorem inside_T2a {f : ℝ} (hf : 6 ≤ f) : (T2a f hf).carrier ⊆ (tgt f hf).carrier := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k
  · show mkPt (f^2 - f : ℝ) (0:ℝ) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_refl 0
    · have key : Hq f * (f^2 - f : ℝ) - Lq f / 2 * (0:ℝ) = rr f * ((2*f^3 - 3*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - (f^2 - f : ℝ)) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity)))
  · show mkPt (2*f^2 - f : ℝ) (0:ℝ) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_refl 0
    · have key : Hq f * (2*f^2 - f : ℝ) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^3 - 4*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - (2*f^2 - f : ℝ)) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^4 - 6*f^3 - 2*f^2 + 4*f - 1) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity)))
  · show mkPt ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_of_lt (mul_pos (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (mul_pos (by norm_num) (pow_pos hfpos 2))) hr)
    · have key : Hq f * ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) - Lq f / 2 * (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((2*f^4 + 5*f^3 - 11*f^2 + 6*f - 1) / (2 * f^2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (mul_pos (by norm_num) (pow_pos hfpos 2))))
    · have key : Hq f * (Lq f - ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ)) - Lq f / 2 * (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((4*f^4 - 6*f^3 - 2*f^2 + 4*f - 1) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity)))

theorem det_T2b {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) (2*f^2 - f : ℝ) (0:ℝ) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) (2*f^2 - f : ℝ) (0:ℝ) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- `T2b`: `β(c on base, a off)` at `(a,0)` — node `N1`'s second placement (leads to `N3`). -/
noncomputable def T2b (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) (2*f^2 - f : ℝ) (0:ℝ) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (det_T2b hf)

theorem sides_T2b {f : ℝ} (hf : 6 ≤ f) :
    dist ((T2b f hf).pts 0) ((T2b f hf).pts 1) ^ 2 = (f^4 : ℝ) ∧
    dist ((T2b f hf).pts 1) ((T2b f hf).pts 2) ^ 2 = (4*f^2 - 4*f + 1 : ℝ) ∧
    dist ((T2b f hf).pts 2) ((T2b f hf).pts 0) ^ 2 = (f^4 - 2*f^3 + f^2 : ℝ) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have hr2 := rr_sq hf
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (f^2 - f : ℝ) ((0:ℝ))) (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) ((0 : ℝ)) * hr2
  · show dist (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^4 - 12*f^3 + 13*f^2 - 6*f + 1) / (4*f^4) : ℝ)) * hr2
  · show dist (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^4 - 12*f^3 + 13*f^2 - 6*f + 1) / (4*f^4) : ℝ)) * hr2

theorem inside_T2b {f : ℝ} (hf : 6 ≤ f) : (T2b f hf).carrier ⊆ (tgt f hf).carrier := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k
  · show mkPt (f^2 - f : ℝ) (0:ℝ) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_refl 0
    · have key : Hq f * (f^2 - f : ℝ) - Lq f / 2 * (0:ℝ) = rr f * ((2*f^3 - 3*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - (f^2 - f : ℝ)) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity)))
  · show mkPt (2*f^2 - f : ℝ) (0:ℝ) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_refl 0
    · have key : Hq f * (2*f^2 - f : ℝ) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^3 - 4*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - (2*f^2 - f : ℝ)) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^4 - 6*f^3 - 2*f^2 + 4*f - 1) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity)))
  · show mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_of_lt (mul_pos (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (mul_pos (by norm_num) (pow_pos hfpos 2))) hr)
    · have key : Hq f * ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) - Lq f / 2 * (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((2*f^3 - 3*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ)) - Lq f / 2 * (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((4*f^6 - 8*f^5 + 3*f^4 + 8*f^3 - 12*f^2 + 6*f - 1) / (2 * f^2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5, pow_nonneg h6 6]) (mul_pos (by norm_num) (pow_pos hfpos 2))))

theorem det_T3 {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- `T3`: `α(c on ray β, b off)` at `(a,0)` above `T2b` — node `N3`'s first placement (leads to `N4`). -/
noncomputable def T3 (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (det_T3 hf)

theorem sides_T3 {f : ℝ} (hf : 6 ≤ f) :
    dist ((T3 f hf).pts 0) ((T3 f hf).pts 1) ^ 2 = (f^4 : ℝ) ∧
    dist ((T3 f hf).pts 1) ((T3 f hf).pts 2) ^ 2 = (f^4 - 2*f^3 + f^2 : ℝ) ∧
    dist ((T3 f hf).pts 2) ((T3 f hf).pts 0) ^ 2 = (4*f^2 - 4*f + 1 : ℝ) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have hr2 := rr_sq hf
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (f^2 - f : ℝ) ((0:ℝ))) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^2 - 4*f + 1) / (4*f^2) : ℝ)) * hr2
  · show dist (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) ((0 : ℝ)) * hr2
  · show dist (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^2 - 4*f + 1) / (4*f^2) : ℝ)) * hr2

theorem inside_T3 {f : ℝ} (hf : 6 ≤ f) : (T3 f hf).carrier ⊆ (tgt f hf).carrier := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k
  · show mkPt (f^2 - f : ℝ) (0:ℝ) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_refl 0
    · have key : Hq f * (f^2 - f : ℝ) - Lq f / 2 * (0:ℝ) = rr f * ((2*f^3 - 3*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - (f^2 - f : ℝ)) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity)))
  · show mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_of_lt (mul_pos (div_pos (by nlinarith [h6]) (mul_pos (by norm_num) hfpos)) hr)
    · have key : Hq f * ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) - Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((2*f^3 - 3*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ)) - Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((4*f^5 - 8*f^4 - f^3 + 10*f^2 - 6*f + 1) / (2 * f : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5]) (mul_pos (by norm_num) hfpos)))
  · show mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_of_lt (mul_pos (div_pos (by nlinarith [h6]) (mul_pos (by norm_num) hfpos)) hr)
    · have key : Hq f * ((2*f^3 - 3*f + 1) / (2*f) : ℝ) - Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) = 0 := by
        unfold Lq Hq; field_simp; ring
      rw [key]
    · have key : Hq f * (Lq f - ((2*f^3 - 3*f + 1) / (2*f) : ℝ)) - Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2 * f : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5]) (mul_pos (by norm_num) hfpos)))

theorem det_T3p {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- `T3p`: `β(c on ray β, a off)` at `(a,0)` above `T2b` — node `N3`'s second placement (leads to `N5`). -/
noncomputable def T3p (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f) (det_T3p hf)

theorem sides_T3p {f : ℝ} (hf : 6 ≤ f) :
    dist ((T3p f hf).pts 0) ((T3p f hf).pts 1) ^ 2 = (f^4 : ℝ) ∧
    dist ((T3p f hf).pts 1) ((T3p f hf).pts 2) ^ 2 = (4*f^2 - 4*f + 1 : ℝ) ∧
    dist ((T3p f hf).pts 2) ((T3p f hf).pts 0) ^ 2 = (f^4 - 2*f^3 + f^2 : ℝ) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have hr2 := rr_sq hf
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (f^2 - f : ℝ) ((0:ℝ))) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^2 - 4*f + 1) / (4*f^2) : ℝ)) * hr2
  · show dist (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) (mkPt ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f)) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((4*f^10 - 20*f^9 + 9*f^8 + 84*f^7 - 118*f^6 - 24*f^5 + 159*f^4 - 140*f^3 + 58*f^2 - 12*f + 1) / (4*f^10) : ℝ)) * hr2
  · show dist (mkPt ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ^ 2 = _
    rw [dist_sq_mkPt]; unfold Dq at hr2
    linear_combination (norm := (field_simp; ring)) (((16*f^10 - 48*f^9 + 4*f^8 + 136*f^7 - 164*f^6 - 8*f^5 + 157*f^4 - 140*f^3 + 58*f^2 - 12*f + 1) / (4*f^10) : ℝ)) * hr2

theorem inside_T3p {f : ℝ} (hf : 6 ≤ f) : (T3p f hf).carrier ⊆ (tgt f hf).carrier := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k
  · show mkPt (f^2 - f : ℝ) (0:ℝ) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_refl 0
    · have key : Hq f * (f^2 - f : ℝ) - Lq f / 2 * (0:ℝ) = rr f * ((2*f^3 - 3*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - (f^2 - f : ℝ)) - Lq f / 2 * (0:ℝ) = rr f * ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity)))
  · show mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_of_lt (mul_pos (div_pos (by nlinarith [h6]) (mul_pos (by norm_num) hfpos)) hr)
    · have key : Hq f * ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) - Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((2*f^3 - 3*f^2 + f) / (2 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (by positivity)))
    · have key : Hq f * (Lq f - ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ)) - Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((4*f^5 - 8*f^4 - f^3 + 10*f^2 - 6*f + 1) / (2 * f : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5]) (mul_pos (by norm_num) hfpos)))
  · show mkPt ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f) ∈ (tgt f hf).carrier
    refine mem_tgt hf ?_ ?_ ?_
    · exact le_of_lt (mul_pos (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5]) (mul_pos (by norm_num) (pow_pos hfpos 5))) hr)
    · have key : Hq f * ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) - Lq f / 2 * (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f) = 0 := by
        unfold Lq Hq; field_simp; ring
      rw [key]
    · have key : Hq f * (Lq f - ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ)) - Lq f / 2 * (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f) = rr f * ((4*f^9 - 10*f^8 + 6*f^7 + 25*f^6 - 45*f^5 + 6*f^4 + 35*f^3 - 29*f^2 + 9*f - 1) / (2 * f^5 : ℝ)) := by
        unfold Lq Hq; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5, pow_nonneg h6 6, pow_nonneg h6 7, pow_nonneg h6 8, pow_nonneg h6 9]) (mul_pos (by norm_num) (pow_pos hfpos 5))))

/-! ## 3. The node configurations have pairwise disjoint interiors -/

theorem disj_T1_T2a {f : ℝ} (hf : 6 ≤ f) : Disjoint (interior (T1 f hf).carrier) (interior (T2a f hf).carrier) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine interiors_disjoint_of_separating (lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ))) (lineFun_linear_ne_zero (Or.inl (by intro h; field_simp at h; nlinarith [h, h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]))) 0 ?_ ?_
  · refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (0 : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (0 : ℝ) ((0:ℝ))) = -(rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (neg_neg_of_pos (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity))))
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
  · refine ge_of_forall_pts_ge _ ?_
    intro k
    fin_cases k
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ)))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (2*f^2 - f : ℝ) ((0:ℝ)))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) = (rr f * ((2*f^2 - f) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) = (rr f * ((8*f^3 - 12*f^2 + 6*f - 1) / (2 * f^3 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (mul_pos (by norm_num) (pow_pos hfpos 3))))

theorem disj_T1_T2b {f : ℝ} (hf : 6 ≤ f) : Disjoint (interior (T1 f hf).carrier) (interior (T2b f hf).carrier) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine interiors_disjoint_of_separating (lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ))) (lineFun_linear_ne_zero (Or.inl (by intro h; field_simp at h; nlinarith [h, h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]))) 0 ?_ ?_
  · refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (0 : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (0 : ℝ) ((0:ℝ))) = -(rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (neg_neg_of_pos (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity))))
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
  · refine ge_of_forall_pts_ge _ ?_
    intro k
    fin_cases k
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ)))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (2*f^2 - f : ℝ) ((0:ℝ)))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) = (rr f * ((2*f^2 - f) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) = (rr f * ((2*f^3 - 5*f^2 + 4*f - 1) / (2 * f : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (mul_pos (by norm_num) hfpos)))

theorem disj_T1_T3 {f : ℝ} (hf : 6 ≤ f) : Disjoint (interior (T1 f hf).carrier) (interior (T3 f hf).carrier) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine interiors_disjoint_of_separating (lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ))) (lineFun_linear_ne_zero (Or.inl (by intro h; field_simp at h; nlinarith [h, h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]))) 0 ?_ ?_
  · refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (0 : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (0 : ℝ) ((0:ℝ))) = -(rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (neg_neg_of_pos (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity))))
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
  · refine ge_of_forall_pts_ge _ ?_
    intro k
    fin_cases k
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ)))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = (rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]

theorem disj_T2b_T3 {f : ℝ} (hf : 6 ≤ f) : Disjoint (interior (T2b f hf).carrier) (interior (T3 f hf).carrier) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine interiors_disjoint_of_separating (lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) (lineFun_linear_ne_zero (Or.inl (by intro h; field_simp at h; nlinarith [h, h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]))) 0 ?_ ?_
  · refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k
    · show lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) = -(rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (neg_neg_of_pos (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity))))
    · show lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) ≤ 0
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
  · refine ge_of_forall_pts_ge _ ?_
    intro k
    fin_cases k
    · show 0 ≤ lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (f^2 - f : ℝ) ((0:ℝ)))
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show 0 ≤ lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f))
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show 0 ≤ lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f))
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = (rr f * ((2*f^3 - 5*f^2 + 4*f - 1) / (2 * f : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (mul_pos (by norm_num) hfpos)))

theorem disj_T1_T3p {f : ℝ} (hf : 6 ≤ f) : Disjoint (interior (T1 f hf).carrier) (interior (T3p f hf).carrier) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine interiors_disjoint_of_separating (lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ))) (lineFun_linear_ne_zero (Or.inl (by intro h; field_simp at h; nlinarith [h, h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]))) 0 ?_ ?_
  · refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (0 : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (0 : ℝ) ((0:ℝ))) = -(rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (neg_neg_of_pos (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity))))
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) ≤ 0
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
  · refine ge_of_forall_pts_ge _ ?_
    intro k
    fin_cases k
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ)))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = (rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))
    · show 0 ≤ lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f))
      have key : lineFun ((2*f^3 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (f^2 - f : ℝ) ((0:ℝ)) (mkPt ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f)) = (rr f * ((2*f^6 - 7*f^5 + f^4 + 15*f^3 - 17*f^2 + 7*f - 1) / (2 * f^4 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5, pow_nonneg h6 6]) (mul_pos (by norm_num) (pow_pos hfpos 4))))

theorem disj_T2b_T3p {f : ℝ} (hf : 6 ≤ f) : Disjoint (interior (T2b f hf).carrier) (interior (T3p f hf).carrier) := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hr := rr_pos hf
  refine interiors_disjoint_of_separating (lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) (lineFun_linear_ne_zero (Or.inl (by intro h; field_simp at h; nlinarith [h, h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]))) 0 ?_ ?_
  · refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k
    · show lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (f^2 - f : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) ≤ 0
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (2*f^2 - f : ℝ) ((0:ℝ))) = -(rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (neg_neg_of_pos (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity))))
    · show lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) ≤ 0
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
  · refine ge_of_forall_pts_ge _ ?_
    intro k
    fin_cases k
    · show 0 ≤ lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (f^2 - f : ℝ) ((0:ℝ)))
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt (f^2 - f : ℝ) ((0:ℝ))) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show 0 ≤ lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f))
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^3 - 2*f^2 - 3*f + 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f)) = 0 := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]
    · show 0 ≤ lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f))
      have key : lineFun (f^2 - f : ℝ) ((0:ℝ)) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (mkPt ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f)) = (rr f * ((2*f^3 - 5*f^2 + 4*f - 1) / (2 * f : ℝ))) := by simp only [lineFun_apply, mkPt_zero, mkPt_one]; field_simp; ring
      rw [key]; exact le_of_lt (mul_pos hr (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (mul_pos (by norm_num) hfpos)))

/-! ## 4. The twenty-three escape facts, node by node -/

theorem det_cN0_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    det3 (0 : ℝ) (0:ℝ) (2*f - 1 : ℝ) (0:ℝ) ((f^2 + 2*f - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (0 : ℝ) (0:ℝ) (2*f - 1 : ℝ) (0:ℝ) ((f^2 + 2*f - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `alpha(b on ray, c off)` at node N0. -/
noncomputable def cN0_alpha_bc (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (0 : ℝ) (0:ℝ) (2*f - 1 : ℝ) (0:ℝ) ((f^2 + 2*f - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) (det_cN0_alpha_bc hf)

theorem esc_cN0_alpha_bc {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN0_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN0_alpha_bc f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN0_alpha_bc f hf).pts 2 = mkPt ((f^2 + 2*f - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f - 1) / (2) : ℝ) * rr f) - Hq f * ((f^2 + 2*f - 1) / (2) : ℝ) = rr f * ((f^4 - 2*f^3 - 3*f^2 + 4*f - 1) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN0_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    (cN0_alpha_bc f hf).pts 0 = (mkPt (0 : ℝ) (0:ℝ)) ∧ (cN0_alpha_bc f hf).pts 1 = (mkPt (2*f - 1 : ℝ) (0:ℝ)) := ⟨rfl, rfl⟩

theorem det_cN0_alpha_cb {f : ℝ} (hf : 6 ≤ f) :
    det3 (0 : ℝ) (0:ℝ) (f^2 : ℝ) (0:ℝ) ((2*f^3 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (0 : ℝ) (0:ℝ) (f^2 : ℝ) (0:ℝ) ((2*f^3 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `alpha(c on ray, b off)` at node N0. -/
noncomputable def cN0_alpha_cb (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (0 : ℝ) (0:ℝ) (f^2 : ℝ) (0:ℝ) ((2*f^3 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (det_cN0_alpha_cb hf)

theorem esc_cN0_alpha_cb {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN0_alpha_cb f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN0_alpha_cb f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN0_alpha_cb f hf).pts 2 = mkPt ((2*f^3 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) - Hq f * ((2*f^3 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) = rr f * ((2*f^5 - 5*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2 * f^2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5]) (mul_pos (by norm_num) (pow_pos hfpos 2)))

theorem frame_cN0_alpha_cb {f : ℝ} (hf : 6 ≤ f) :
    (cN0_alpha_cb f hf).pts 0 = (mkPt (0 : ℝ) (0:ℝ)) ∧ (cN0_alpha_cb f hf).pts 1 = (mkPt (f^2 : ℝ) (0:ℝ)) := ⟨rfl, rfl⟩

theorem det_cN0_gamma_ab {f : ℝ} (hf : 6 ≤ f) :
    det3 (0 : ℝ) (0:ℝ) (f^2 - f : ℝ) (0:ℝ) ((-2*f^2 + 3*f - 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (0 : ℝ) (0:ℝ) (f^2 - f : ℝ) (0:ℝ) ((-2*f^2 + 3*f - 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(a on ray, b off)` at node N0. -/
noncomputable def cN0_gamma_ab (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (0 : ℝ) (0:ℝ) (f^2 - f : ℝ) (0:ℝ) ((-2*f^2 + 3*f - 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (det_cN0_gamma_ab hf)

theorem esc_cN0_gamma_ab {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN0_gamma_ab f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN0_gamma_ab f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN0_gamma_ab f hf).pts 2 = mkPt ((-2*f^2 + 3*f - 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) - Hq f * ((-2*f^2 + 3*f - 1) / (2*f) : ℝ) = rr f * ((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2 * f : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (mul_pos (by norm_num) hfpos))

theorem frame_cN0_gamma_ab {f : ℝ} (hf : 6 ≤ f) :
    (cN0_gamma_ab f hf).pts 0 = (mkPt (0 : ℝ) (0:ℝ)) ∧ (cN0_gamma_ab f hf).pts 1 = (mkPt (f^2 - f : ℝ) (0:ℝ)) := ⟨rfl, rfl⟩

theorem det_cN0_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    det3 (0 : ℝ) (0:ℝ) (2*f - 1 : ℝ) (0:ℝ) ((-f^2 + 2*f - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (0 : ℝ) (0:ℝ) (2*f - 1 : ℝ) (0:ℝ) ((-f^2 + 2*f - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(b on ray, a off)` at node N0. -/
noncomputable def cN0_gamma_ba (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (0 : ℝ) (0:ℝ) (2*f - 1 : ℝ) (0:ℝ) ((-f^2 + 2*f - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) (det_cN0_gamma_ba hf)

theorem esc_cN0_gamma_ba {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN0_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN0_gamma_ba f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN0_gamma_ba f hf).pts 2 = mkPt ((-f^2 + 2*f - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f - 1) / (2) : ℝ) * rr f) - Hq f * ((-f^2 + 2*f - 1) / (2) : ℝ) = rr f * ((f^4 - 4*f^2 + 4*f - 1) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN0_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    (cN0_gamma_ba f hf).pts 0 = (mkPt (0 : ℝ) (0:ℝ)) ∧ (cN0_gamma_ba f hf).pts 1 = (mkPt (2*f - 1 : ℝ) (0:ℝ)) := ⟨rfl, rfl⟩

theorem det_cN1_gamma_ab {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) (2*f^2 - 2*f : ℝ) (0:ℝ) ((2*f^3 - 4*f^2 + 3*f - 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) (2*f^2 - 2*f : ℝ) (0:ℝ) ((2*f^3 - 4*f^2 + 3*f - 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(a on ray, b off)` at node N1. -/
noncomputable def cN1_gamma_ab (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) (2*f^2 - 2*f : ℝ) (0:ℝ) ((2*f^3 - 4*f^2 + 3*f - 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) (det_cN1_gamma_ab hf)

theorem esc_cN1_gamma_ab {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN1_gamma_ab f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN1_gamma_ab f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN1_gamma_ab f hf).pts 2 = mkPt ((2*f^3 - 4*f^2 + 3*f - 1) / (2*f) : ℝ) (((2*f - 1) / (2*f) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((2*f - 1) / (2*f) : ℝ) * rr f) - Hq f * ((2*f^3 - 4*f^2 + 3*f - 1) / (2*f) : ℝ) = rr f * ((4*f^3 - 8*f^2 + 5*f - 1) / (2 * f : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3]) (mul_pos (by norm_num) hfpos))

theorem frame_cN1_gamma_ab {f : ℝ} (hf : 6 ≤ f) :
    (cN1_gamma_ab f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN1_gamma_ab f hf).pts 1 = (mkPt (2*f^2 - 2*f : ℝ) (0:ℝ)) := ⟨rfl, rfl⟩

theorem det_cN1_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) (f^2 + f - 1 : ℝ) (0:ℝ) ((f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) (f^2 + f - 1 : ℝ) (0:ℝ) ((f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(b on ray, a off)` at node N1. -/
noncomputable def cN1_gamma_ba (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) (f^2 + f - 1 : ℝ) (0:ℝ) ((f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) (det_cN1_gamma_ba hf)

theorem esc_cN1_gamma_ba {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN1_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN1_gamma_ba f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN1_gamma_ba f hf).pts 2 = mkPt ((f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f - 1) / (2) : ℝ) * rr f) - Hq f * ((f^2 - 1) / (2) : ℝ) = rr f * ((f^4 - 2*f^3 - f^2 + 3*f - 1) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN1_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    (cN1_gamma_ba f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN1_gamma_ba f hf).pts 1 = (mkPt (f^2 + f - 1 : ℝ) (0:ℝ)) := ⟨rfl, rfl⟩

theorem det_cN2_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((f^4 + 2*f^3 + 2*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((f^4 + 2*f^3 + 2*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `alpha(b on ray, c off)` at node N2. -/
noncomputable def cN2_alpha_bc (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((f^4 + 2*f^3 + 2*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (det_cN2_alpha_bc hf)

theorem esc_cN2_alpha_bc {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN2_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN2_alpha_bc f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN2_alpha_bc f hf).pts 2 = mkPt ((f^4 + 2*f^3 + 2*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) - Hq f * ((f^4 + 2*f^3 + 2*f^2 - 4*f + 1) / (2*f^2) : ℝ) = rr f * ((f^6 - 6*f^4 - f^3 + 10*f^2 - 6*f + 1) / (2 * f^2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5, pow_nonneg h6 6]) (mul_pos (by norm_num) (pow_pos hfpos 2)))

theorem frame_cN2_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    (cN2_alpha_bc f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN2_alpha_bc f hf).pts 1 = (mkPt ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN2_alpha_cb {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ((2*f^6 - 4*f^5 + 9*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ((2*f^6 - 4*f^5 + 9*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `alpha(c on ray, b off)` at node N2. -/
noncomputable def cN2_alpha_cb (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ((2*f^6 - 4*f^5 + 9*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) (det_cN2_alpha_cb hf)

theorem esc_cN2_alpha_cb {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN2_alpha_cb f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN2_alpha_cb f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN2_alpha_cb f hf).pts 2 = mkPt ((2*f^6 - 4*f^5 + 9*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) - Hq f * ((2*f^6 - 4*f^5 + 9*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) = rr f * ((6*f^6 - 21*f^5 + 9*f^4 + 20*f^3 - 22*f^2 + 8*f - 1) / (2 * f^4 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5, pow_nonneg h6 6]) (mul_pos (by norm_num) (pow_pos hfpos 4)))

theorem frame_cN2_alpha_cb {f : ℝ} (hf : 6 ≤ f) :
    (cN2_alpha_cb f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN2_alpha_cb f hf).pts 1 = (mkPt ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN2_beta_ac {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) ((3*f^2 - 3*f) / (2) : ℝ) (((f) / (2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) ((3*f^2 - 3*f) / (2) : ℝ) (((f) / (2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `beta(a on ray, c off)` at node N2. -/
noncomputable def cN2_beta_ac (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) ((3*f^2 - 3*f) / (2) : ℝ) (((f) / (2) : ℝ) * rr f) (det_cN2_beta_ac hf)

theorem esc_cN2_beta_ac {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN2_beta_ac f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN2_beta_ac f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN2_beta_ac f hf).pts 2 = mkPt ((3*f^2 - 3*f) / (2) : ℝ) (((f) / (2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f) / (2) : ℝ) * rr f) - Hq f * ((3*f^2 - 3*f) / (2) : ℝ) = rr f * ((f^4 - 3*f^3 + 3*f^2 - f) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN2_beta_ac {f : ℝ} (hf : 6 ≤ f) :
    (cN2_beta_ac f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN2_beta_ac f hf).pts 1 = (mkPt ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN2_beta_ca {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ((3*f^2 - 4*f + 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ((3*f^2 - 4*f + 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `beta(c on ray, a off)` at node N2. -/
noncomputable def cN2_beta_ca (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ((3*f^2 - 4*f + 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) (det_cN2_beta_ca hf)

theorem esc_cN2_beta_ca {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN2_beta_ca f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN2_beta_ca f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN2_beta_ca f hf).pts 2 = mkPt ((3*f^2 - 4*f + 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f - 1) / (2) : ℝ) * rr f) - Hq f * ((3*f^2 - 4*f + 1) / (2) : ℝ) = rr f * ((f^4 - 4*f^3 + 4*f^2 - f) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN2_beta_ca {f : ℝ} (hf : 6 ≤ f) :
    (cN2_beta_ca f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN2_beta_ca f hf).pts 1 = (mkPt ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN2_gamma_ab {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) ((2*f^5 - 6*f^4 + 2*f^3 + 6*f^2 - 5*f + 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) ((2*f^5 - 6*f^4 + 2*f^3 + 6*f^2 - 5*f + 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(a on ray, b off)` at node N2. -/
noncomputable def cN2_gamma_ab (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) ((2*f^5 - 6*f^4 + 2*f^3 + 6*f^2 - 5*f + 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f) (det_cN2_gamma_ab hf)

theorem esc_cN2_gamma_ab {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN2_gamma_ab f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN2_gamma_ab f hf).pts 1) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  have he : (cN2_gamma_ab f hf).pts 1 = mkPt ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) - Hq f * ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) = rr f * ((f^5 - 5*f^4 + 2*f^3 + 6*f^2 - 5*f + 1) / (2 * f : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5]) (mul_pos (by norm_num) hfpos))

theorem frame_cN2_gamma_ab {f : ℝ} (hf : 6 ≤ f) :
    (cN2_gamma_ab f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN2_gamma_ab f hf).pts 1 = (mkPt ((3*f^3 - f^2 - 3*f + 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN2_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(b on ray, a off)` at node N2. -/
noncomputable def cN2_gamma_ba (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (det_cN2_gamma_ba hf)

theorem esc_cN2_gamma_ba {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN2_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN2_gamma_ba f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN2_gamma_ba f hf).pts 2 = mkPt ((3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) - Hq f * ((3*f^2 - 4*f + 1) / (2*f^2) : ℝ) = rr f * ((2*f^5 - 3*f^4 - 5*f^3 + 11*f^2 - 6*f + 1) / (2 * f^2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5]) (mul_pos (by norm_num) (pow_pos hfpos 2)))

theorem frame_cN2_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    (cN2_gamma_ba f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN2_gamma_ba f hf).pts 1 = (mkPt ((2*f^4 + 3*f^2 - 4*f + 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN3_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^5 + 2*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f) ((3*f^2 - 3*f) / (2) : ℝ) (((f) / (2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^5 + 2*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f) ((3*f^2 - 3*f) / (2) : ℝ) (((f) / (2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `alpha(b on ray, c off)` at node N3. -/
noncomputable def cN3_alpha_bc (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((2*f^5 + 2*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f) ((3*f^2 - 3*f) / (2) : ℝ) (((f) / (2) : ℝ) * rr f) (det_cN3_alpha_bc hf)

theorem esc_cN3_alpha_bc {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN3_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN3_alpha_bc f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN3_alpha_bc f hf).pts 2 = mkPt ((3*f^2 - 3*f) / (2) : ℝ) (((f) / (2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f) / (2) : ℝ) * rr f) - Hq f * ((3*f^2 - 3*f) / (2) : ℝ) = rr f * ((f^4 - 3*f^3 + 3*f^2 - f) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN3_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    (cN3_alpha_bc f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN3_alpha_bc f hf).pts 1 = (mkPt ((2*f^5 + 2*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN3_beta_ac {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `beta(a on ray, c off)` at node N3. -/
noncomputable def cN3_beta_ac (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) (det_cN3_beta_ac hf)

theorem esc_cN3_beta_ac {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN3_beta_ac f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN3_beta_ac f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN3_beta_ac f hf).pts 2 = mkPt ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) - Hq f * ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) = rr f * ((2*f^2 - f) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity))

theorem frame_cN3_beta_ac {f : ℝ} (hf : 6 ≤ f) :
    (cN3_beta_ac f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN3_beta_ac f hf).pts 1 = (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN3_gamma_ab {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((2*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((2*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(a on ray, b off)` at node N3. -/
noncomputable def cN3_gamma_ab (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ((2*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (det_cN3_gamma_ab hf)

theorem esc_cN3_gamma_ab {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN3_gamma_ab f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN3_gamma_ab f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN3_gamma_ab f hf).pts 2 = mkPt ((2*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) - Hq f * ((2*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) = rr f * ((2*f^2 - f) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity))

theorem frame_cN3_gamma_ab {f : ℝ} (hf : 6 ≤ f) :
    (cN3_gamma_ab f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN3_gamma_ab f hf).pts 1 = (mkPt ((4*f^4 - 4*f^3 - 3*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((2*f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN3_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^5 + 2*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f) ((f^3 - 3*f^2 + 3*f - 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^5 + 2*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f) ((f^3 - 3*f^2 + 3*f - 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(b on ray, a off)` at node N3. -/
noncomputable def cN3_gamma_ba (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((2*f^5 + 2*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f) ((f^3 - 3*f^2 + 3*f - 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) (det_cN3_gamma_ba hf)

theorem esc_cN3_gamma_ba {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN3_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN3_gamma_ba f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN3_gamma_ba f hf).pts 2 = mkPt ((f^3 - 3*f^2 + 3*f - 1) / (2*f) : ℝ) (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f^2 - 2*f + 1) / (2*f) : ℝ) * rr f) - Hq f * ((f^3 - 3*f^2 + 3*f - 1) / (2*f) : ℝ) = rr f * ((f^4 - 3*f^3 + 3*f^2 - f) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN3_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    (cN3_gamma_ba f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN3_gamma_ba f hf).pts 1 = (mkPt ((2*f^5 + 2*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^3) : ℝ) (((4*f^2 - 4*f + 1) / (2*f^3) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN4_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    det3 (2*f^2 - f : ℝ) (0:ℝ) (2*f^2 + f - 1 : ℝ) (0:ℝ) ((5*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (2*f^2 - f : ℝ) (0:ℝ) (2*f^2 + f - 1 : ℝ) (0:ℝ) ((5*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `alpha(b on ray, c off)` at node N4. -/
noncomputable def cN4_alpha_bc (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (2*f^2 - f : ℝ) (0:ℝ) (2*f^2 + f - 1 : ℝ) (0:ℝ) ((5*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) (det_cN4_alpha_bc hf)

theorem esc_cN4_alpha_bc {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN4_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN4_alpha_bc f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN4_alpha_bc f hf).pts 2 = mkPt ((5*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f - 1) / (2) : ℝ) * rr f) - Hq f * ((5*f^2 - 1) / (2) : ℝ) = rr f * ((f^4 - 6*f^3 + f^2 + 3*f - 1) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN4_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    (cN4_alpha_bc f hf).pts 0 = (mkPt (2*f^2 - f : ℝ) (0:ℝ)) ∧ (cN4_alpha_bc f hf).pts 1 = (mkPt (2*f^2 + f - 1 : ℝ) (0:ℝ)) := ⟨rfl, rfl⟩

theorem det_cN4_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    det3 (2*f^2 - f : ℝ) (0:ℝ) (2*f^2 + f - 1 : ℝ) (0:ℝ) ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (2*f^2 - f : ℝ) (0:ℝ) (2*f^2 + f - 1 : ℝ) (0:ℝ) ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(b on ray, a off)` at node N4. -/
noncomputable def cN4_gamma_ba (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (2*f^2 - f : ℝ) (0:ℝ) (2*f^2 + f - 1 : ℝ) (0:ℝ) ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) (det_cN4_gamma_ba hf)

theorem esc_cN4_gamma_ba {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN4_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN4_gamma_ba f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN4_gamma_ba f hf).pts 2 = mkPt ((3*f^2 - 1) / (2) : ℝ) (((f - 1) / (2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f - 1) / (2) : ℝ) * rr f) - Hq f * ((3*f^2 - 1) / (2) : ℝ) = rr f * ((f^4 - 4*f^3 + 3*f - 1) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN4_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    (cN4_gamma_ba f hf).pts 0 = (mkPt (2*f^2 - f : ℝ) (0:ℝ)) ∧ (cN4_gamma_ba f hf).pts 1 = (mkPt (2*f^2 + f - 1 : ℝ) (0:ℝ)) := ⟨rfl, rfl⟩

theorem det_cN5_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^8 + 2*f^7 - 2*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^6) : ℝ) (((8*f^5 - 8*f^4 - 10*f^3 + 16*f^2 - 7*f + 1) / (2*f^6) : ℝ) * rr f) ((3*f^4 - 6*f^3 - 2*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^8 + 2*f^7 - 2*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^6) : ℝ) (((8*f^5 - 8*f^4 - 10*f^3 + 16*f^2 - 7*f + 1) / (2*f^6) : ℝ) * rr f) ((3*f^4 - 6*f^3 - 2*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `alpha(b on ray, c off)` at node N5. -/
noncomputable def cN5_alpha_bc (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((2*f^8 + 2*f^7 - 2*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^6) : ℝ) (((8*f^5 - 8*f^4 - 10*f^3 + 16*f^2 - 7*f + 1) / (2*f^6) : ℝ) * rr f) ((3*f^4 - 6*f^3 - 2*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) (det_cN5_alpha_bc hf)

theorem esc_cN5_alpha_bc {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN5_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN5_alpha_bc f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN5_alpha_bc f hf).pts 2 = mkPt ((3*f^4 - 6*f^3 - 2*f^2 + 4*f - 1) / (2*f^2) : ℝ) (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f^3 + f^2 - 3*f + 1) / (2*f^2) : ℝ) * rr f) - Hq f * ((3*f^4 - 6*f^3 - 2*f^2 + 4*f - 1) / (2*f^2) : ℝ) = rr f * ((f^4 - 2*f^3 + 3*f^2 - f) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN5_alpha_bc {f : ℝ} (hf : 6 ≤ f) :
    (cN5_alpha_bc f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN5_alpha_bc f hf).pts 1 = (mkPt ((2*f^8 + 2*f^7 - 2*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^6) : ℝ) (((8*f^5 - 8*f^4 - 10*f^3 + 16*f^2 - 7*f + 1) / (2*f^6) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN5_alpha_cb {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) ((2*f^6 - 9*f^4 + 10*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) ((2*f^6 - 9*f^4 + 10*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `alpha(c on ray, b off)` at node N5. -/
noncomputable def cN5_alpha_cb (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) ((2*f^6 - 9*f^4 + 10*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) (det_cN5_alpha_cb hf)

theorem esc_cN5_alpha_cb {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN5_alpha_cb f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN5_alpha_cb f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN5_alpha_cb f hf).pts 2 = mkPt ((2*f^6 - 9*f^4 + 10*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) - Hq f * ((2*f^6 - 9*f^4 + 10*f^2 - 6*f + 1) / (2*f^4) : ℝ) = rr f * ((2*f^2 - f) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity))

theorem frame_cN5_alpha_cb {f : ℝ} (hf : 6 ≤ f) :
    (cN5_alpha_cb f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN5_alpha_cb f hf).pts 1 = (mkPt ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN5_beta_ac {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f) ((4*f^9 - 2*f^8 - 27*f^7 + 9*f^6 + 54*f^5 - 36*f^4 - 21*f^3 + 27*f^2 - 9*f + 1) / (2*f^7) : ℝ) (((6*f^7 - 3*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^7) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f) ((4*f^9 - 2*f^8 - 27*f^7 + 9*f^6 + 54*f^5 - 36*f^4 - 21*f^3 + 27*f^2 - 9*f + 1) / (2*f^7) : ℝ) (((6*f^7 - 3*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^7) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `beta(a on ray, c off)` at node N5. -/
noncomputable def cN5_beta_ac (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f) ((4*f^9 - 2*f^8 - 27*f^7 + 9*f^6 + 54*f^5 - 36*f^4 - 21*f^3 + 27*f^2 - 9*f + 1) / (2*f^7) : ℝ) (((6*f^7 - 3*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^7) : ℝ) * rr f) (det_cN5_beta_ac hf)

theorem esc_cN5_beta_ac {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN5_beta_ac f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN5_beta_ac f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN5_beta_ac f hf).pts 2 = mkPt ((4*f^9 - 2*f^8 - 27*f^7 + 9*f^6 + 54*f^5 - 36*f^4 - 21*f^3 + 27*f^2 - 9*f + 1) / (2*f^7) : ℝ) (((6*f^7 - 3*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^7) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((6*f^7 - 3*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^7) : ℝ) * rr f) - Hq f * ((4*f^9 - 2*f^8 - 27*f^7 + 9*f^6 + 54*f^5 - 36*f^4 - 21*f^3 + 27*f^2 - 9*f + 1) / (2*f^7) : ℝ) = rr f * ((2*f^4 + f^3 - 7*f^2 + 5*f - 1) / (2 * f : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (mul_pos (by norm_num) hfpos))

theorem frame_cN5_beta_ac {f : ℝ} (hf : 6 ≤ f) :
    (cN5_beta_ac f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN5_beta_ac f hf).pts 1 = (mkPt ((4*f^7 - 4*f^6 - 12*f^5 + 16*f^4 + 5*f^3 - 15*f^2 + 7*f - 1) / (2*f^5) : ℝ) (((4*f^5 - 6*f^4 - 4*f^3 + 11*f^2 - 6*f + 1) / (2*f^5) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN5_beta_ca {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) ((4*f^10 - 4*f^9 - 27*f^8 + 36*f^7 + 45*f^6 - 90*f^5 + 15*f^4 + 48*f^3 - 36*f^2 + 10*f - 1) / (2*f^8) : ℝ) (((6*f^8 - 9*f^7 - 21*f^6 + 44*f^5 - 6*f^4 - 35*f^3 + 29*f^2 - 9*f + 1) / (2*f^8) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) ((4*f^10 - 4*f^9 - 27*f^8 + 36*f^7 + 45*f^6 - 90*f^5 + 15*f^4 + 48*f^3 - 36*f^2 + 10*f - 1) / (2*f^8) : ℝ) (((6*f^8 - 9*f^7 - 21*f^6 + 44*f^5 - 6*f^4 - 35*f^3 + 29*f^2 - 9*f + 1) / (2*f^8) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `beta(c on ray, a off)` at node N5. -/
noncomputable def cN5_beta_ca (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f) ((4*f^10 - 4*f^9 - 27*f^8 + 36*f^7 + 45*f^6 - 90*f^5 + 15*f^4 + 48*f^3 - 36*f^2 + 10*f - 1) / (2*f^8) : ℝ) (((6*f^8 - 9*f^7 - 21*f^6 + 44*f^5 - 6*f^4 - 35*f^3 + 29*f^2 - 9*f + 1) / (2*f^8) : ℝ) * rr f) (det_cN5_beta_ca hf)

theorem esc_cN5_beta_ca {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN5_beta_ca f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN5_beta_ca f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN5_beta_ca f hf).pts 2 = mkPt ((4*f^10 - 4*f^9 - 27*f^8 + 36*f^7 + 45*f^6 - 90*f^5 + 15*f^4 + 48*f^3 - 36*f^2 + 10*f - 1) / (2*f^8) : ℝ) (((6*f^8 - 9*f^7 - 21*f^6 + 44*f^5 - 6*f^4 - 35*f^3 + 29*f^2 - 9*f + 1) / (2*f^8) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((6*f^8 - 9*f^7 - 21*f^6 + 44*f^5 - 6*f^4 - 35*f^3 + 29*f^2 - 9*f + 1) / (2*f^8) : ℝ) * rr f) - Hq f * ((4*f^10 - 4*f^9 - 27*f^8 + 36*f^7 + 45*f^6 - 90*f^5 + 15*f^4 + 48*f^3 - 36*f^2 + 10*f - 1) / (2*f^8) : ℝ) = rr f * ((2*f^5 - 3*f^4 - 5*f^3 + 11*f^2 - 6*f + 1) / (2 * f^2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4, pow_nonneg h6 5]) (mul_pos (by norm_num) (pow_pos hfpos 2)))

theorem frame_cN5_beta_ca {f : ℝ} (hf : 6 ≤ f) :
    (cN5_beta_ca f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN5_beta_ca f hf).pts 1 = (mkPt ((4*f^6 - 2*f^5 - 12*f^4 + 4*f^3 + 9*f^2 - 6*f + 1) / (2*f^4) : ℝ) (((4*f^4 - 2*f^3 - 6*f^2 + 5*f - 1) / (2*f^4) : ℝ) * rr f)) := ⟨rfl, rfl⟩

theorem det_cN5_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^8 + 2*f^7 - 2*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^6) : ℝ) (((8*f^5 - 8*f^4 - 10*f^3 + 16*f^2 - 7*f + 1) / (2*f^6) : ℝ) * rr f) ((f^6 - 6*f^5 + 10*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) (((f^5 - 3*f^4 - f^3 + 7*f^2 - 5*f + 1) / (2*f^4) : ℝ) * rr f) ≠ 0 := by
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have h : det3 (f^2 - f : ℝ) (0:ℝ) ((2*f^8 + 2*f^7 - 2*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^6) : ℝ) (((8*f^5 - 8*f^4 - 10*f^3 + 16*f^2 - 7*f + 1) / (2*f^6) : ℝ) * rr f) ((f^6 - 6*f^5 + 10*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) (((f^5 - 3*f^4 - f^3 + 7*f^2 - 5*f + 1) / (2*f^4) : ℝ) * rr f) = rr f * ((2*f^2 - 3*f + 1) / (2 : ℝ)) := by
    unfold det3; field_simp; ring
  rw [h]; exact ne_of_gt (mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2]) (by positivity)))

/-- Candidate `gamma(b on ray, a off)` at node N5. -/
noncomputable def cN5_gamma_ba (f : ℝ) (hf : 6 ≤ f) : Tri :=
  mkTri (f^2 - f : ℝ) (0:ℝ) ((2*f^8 + 2*f^7 - 2*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^6) : ℝ) (((8*f^5 - 8*f^4 - 10*f^3 + 16*f^2 - 7*f + 1) / (2*f^6) : ℝ) * rr f) ((f^6 - 6*f^5 + 10*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) (((f^5 - 3*f^4 - f^3 + 7*f^2 - 5*f + 1) / (2*f^4) : ℝ) * rr f) (det_cN5_gamma_ba hf)

theorem esc_cN5_gamma_ba {f : ℝ} (hf : 6 ≤ f) : ¬ ((cN5_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hfpos : (0:ℝ) < f := by linarith
  have hf0 : f ≠ 0 := ne_of_gt hfpos
  have h6 : (0:ℝ) ≤ f - 6 := by linarith
  have hv : ((cN5_gamma_ba f hf).pts 2) ∈ (tgt f hf).carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  have he : (cN5_gamma_ba f hf).pts 2 = mkPt ((f^6 - 6*f^5 + 10*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) (((f^5 - 3*f^4 - f^3 + 7*f^2 - 5*f + 1) / (2*f^4) : ℝ) * rr f) := rfl
  rw [he] at hv
  refine not_mem_tgt_of_left hf ?_ hv
  have key : Lq f / 2 * (((f^5 - 3*f^4 - f^3 + 7*f^2 - 5*f + 1) / (2*f^4) : ℝ) * rr f) - Hq f * ((f^6 - 6*f^5 + 10*f^4 - 10*f^2 + 6*f - 1) / (2*f^4) : ℝ) = rr f * ((f^4 - 4*f^3 + 4*f^2 - f) / (2 : ℝ)) := by
    unfold Lq Hq; field_simp; ring
  rw [key]; exact mul_pos (rr_pos hf) (div_pos (by nlinarith [h6, pow_nonneg h6 2, pow_nonneg h6 3, pow_nonneg h6 4]) (by positivity))

theorem frame_cN5_gamma_ba {f : ℝ} (hf : 6 ≤ f) :
    (cN5_gamma_ba f hf).pts 0 = (mkPt (f^2 - f : ℝ) (0:ℝ)) ∧ (cN5_gamma_ba f hf).pts 1 = (mkPt ((2*f^8 + 2*f^7 - 2*f^6 - 24*f^5 + 20*f^4 + 14*f^3 - 21*f^2 + 8*f - 1) / (2*f^6) : ℝ) (((8*f^5 - 8*f^4 - 10*f^3 + 16*f^2 - 7*f + 1) / (2*f^6) : ℝ) * rr f)) := ⟨rfl, rfl⟩

/-- `N0`: corner `(0,0)`, ray = base. -/
theorem blocking_N0 {f : ℝ} (hf : 6 ≤ f) :
    ¬ ((cN0_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN0_alpha_cb f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN0_gamma_ab f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN0_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) :=
  ⟨esc_cN0_alpha_bc hf, esc_cN0_alpha_cb hf, esc_cN0_gamma_ab hf, esc_cN0_gamma_ba hf⟩

/-- `N1`: corner `(a,0)`, ray = base (after `T1`). -/
theorem blocking_N1 {f : ℝ} (hf : 6 ≤ f) :
    ¬ ((cN1_gamma_ab f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN1_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) :=
  ⟨esc_cN1_gamma_ab hf, esc_cN1_gamma_ba hf⟩

/-- `N2`: corner `(a,0)`, ray at angle `α` (after `T1, T2a`); every candidate escapes. -/
theorem blocking_N2 {f : ℝ} (hf : 6 ≤ f) :
    ¬ ((cN2_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN2_alpha_cb f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN2_beta_ac f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN2_beta_ca f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN2_gamma_ab f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN2_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) :=
  ⟨esc_cN2_alpha_bc hf, esc_cN2_alpha_cb hf, esc_cN2_beta_ac hf, esc_cN2_beta_ca hf, esc_cN2_gamma_ab hf, esc_cN2_gamma_ba hf⟩

/-- `N3`: corner `(a,0)`, ray at angle `β` (after `T1, T2b`). -/
theorem blocking_N3 {f : ℝ} (hf : 6 ≤ f) :
    ¬ ((cN3_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN3_beta_ac f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN3_gamma_ab f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN3_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) :=
  ⟨esc_cN3_alpha_bc hf, esc_cN3_beta_ac hf, esc_cN3_gamma_ab hf, esc_cN3_gamma_ba hf⟩

/-- `N4`: corner `(a+c,0)`, ray = base (after `T1, T2b, T3`); the `b`-block candidates escape — the binding inequality of the family. -/
theorem blocking_N4 {f : ℝ} (hf : 6 ≤ f) :
    ¬ ((cN4_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN4_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) :=
  ⟨esc_cN4_alpha_bc hf, esc_cN4_gamma_ba hf⟩

/-- `N5`: corner `(a,0)`, ray at angle `2β` (after `T1, T2b, T3p`). -/
theorem blocking_N5 {f : ℝ} (hf : 6 ≤ f) :
    ¬ ((cN5_alpha_bc f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN5_alpha_cb f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN5_beta_ac f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN5_beta_ca f hf).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cN5_gamma_ba f hf).carrier ⊆ (tgt f hf).carrier) :=
  ⟨esc_cN5_alpha_bc hf, esc_cN5_alpha_cb hf, esc_cN5_beta_ac hf, esc_cN5_beta_ca hf, esc_cN5_gamma_ba hf⟩

/-! ## 5. Witnesses: the configurations at the two smallest members -/

/-- **Non-vacuity at `N = 83` (`f = 6`)**: the deepest configuration `{T1, T2b, T3}` is three
tiles congruent to `(30,11,36)`, inside the target, with pairwise disjoint interiors. -/
theorem witness_83 :
    (T1 6 (le_refl 6)).carrier ⊆ (tgt 6 (le_refl 6)).carrier ∧
    (T2b 6 (le_refl 6)).carrier ⊆ (tgt 6 (le_refl 6)).carrier ∧
    (T3 6 (le_refl 6)).carrier ⊆ (tgt 6 (le_refl 6)).carrier ∧
    Disjoint (interior (T1 6 (le_refl 6)).carrier) (interior (T2b 6 (le_refl 6)).carrier) ∧
    Disjoint (interior (T1 6 (le_refl 6)).carrier) (interior (T3 6 (le_refl 6)).carrier) ∧
    Disjoint (interior (T2b 6 (le_refl 6)).carrier) (interior (T3 6 (le_refl 6)).carrier) :=
  ⟨inside_T1 _, inside_T2b _, inside_T3 _, disj_T1_T2b _, disj_T1_T3 _, disj_T2b_T3 _⟩

/-- **Non-vacuity at `N = 111` (`f = 7`).** -/
theorem witness_111 :
    (T1 7 (by norm_num)).carrier ⊆ (tgt 7 (by norm_num)).carrier ∧
    (T2b 7 (by norm_num)).carrier ⊆ (tgt 7 (by norm_num)).carrier ∧
    (T3 7 (by norm_num)).carrier ⊆ (tgt 7 (by norm_num)).carrier ∧
    Disjoint (interior (T1 7 (by norm_num)).carrier) (interior (T2b 7 (by norm_num)).carrier) ∧
    Disjoint (interior (T1 7 (by norm_num)).carrier) (interior (T3 7 (by norm_num)).carrier) ∧
    Disjoint (interior (T2b 7 (by norm_num)).carrier) (interior (T3 7 (by norm_num)).carrier) :=
  ⟨inside_T1 _, inside_T2b _, inside_T3 _, disj_T1_T2b _, disj_T1_T3 _, disj_T2b_T3 _⟩

end Erdos634.ThickPrefixACB
