import Erdos634.RunPartition

/-!
# The `c|a` junction closed, and the march composed along the whole base word (`e = 1`)

Written 2026-09-12, sequential step 5 after `RunPartition.lean`.  Step 4 left six things at the
`c|a` junction of the `e = 1` march (target `baseBetaTarget 1 f`, tile `(f, f²−1, f²)`, base word
`f` letters `a`, one `b`, one `c`, first and last letter `a`): the cap `bCapMSet` in the `GB`
branch (S1), the flat cap `cCapSet` and the fan `{3α, 2β}` in the `BG` branch (S2, S3), the whole
`cSlotTile'` side (S4), and the pockets (S5).  This file closes the junction and composes.

## What is proved

* **S1, `bCapM_dies`.**  The mirrored cap's `c`-edge runs along the `c`-tile's `b`-edge `[V, A]`
  and overruns the apex `A` by one unit (`capM_far_eq`: its far vertex is `V + (c/b)(A − V)`).
  The filler at `B` (`junction_a_c`'s flush or offset `α`-tile) carries its interior across the
  line beyond `A` (`RunPartition.CSlot.filler_blocks`), so a point of the open extension `(A, A')`
  lies on the cap's edge and in the filler's interior — `Dissection.edge_point_not_interior`.
  No run partition, no side conditions beyond `2 ≤ f`.
* **S4, the mirror.**  Rather than redoing the determinants, the plane is reflected in the
  vertical line `x = L/2` (`reflX`, an `AffineIsometryEquiv`; `reflCD`, the reflected
  `CongruentDissection` with the *same* target, via `DissectionMap.mapDissection` and a re-labelled
  target).  Under it `cSlotTile' X ↦ cSlotTile (L − X − f²)`, `bCapSet X ↦ bCapMSet (L − X)`,
  `bOverSet X ↦ bOverMSet (L − X)`, `flushMSet/offsetMSet (X + f²) ↦` the flush/offset filler at
  `L − X − f²`.  So `cslot'_gb_dies`: after `cSlotTile'` with the `β`-tile at `B` (cap or
  overshoot, as `junction_a_c`/`junction_b'_c` deliver it) the `GB` branch of `junction_c'_a` —
  the mirrored filler at `V` — is dead, by `bCapM_dies`/`bOverM_dies` on the reflection.
* **S2 and S3 are bypassed, not solved.**  The `BG` branch after a `c`-slot restarts the run
  induction from the `BG` tile itself: `run_rigid` looks only at the `BG` tile and the laid run,
  never at what covers `V`.  So whatever completes the figure at `V` — the flat cap, the split, the
  fan — the run to the right is the `BG` march, and a `BG` tile on `[L − 2f, L − f]` or `[L − f, L]`
  has its apex outside the target (`bg_run_to_end_dies`, from `MarchKills.bg_apex_second_to_last_outside`
  and `.bg_apex_last_outside`).  When the `c`-slot is followed by `a^q b a^r`, the run reaches the
  `b`-slot, `junction_a_b`/`junction_b'_a` force `BG` again, and the last run dies the same way
  (`bg_then_b_then_run_dies`, `bslot'_then_run_dies`).  The fan's internal placements and the
  pockets (S5) are therefore never needed.
* **The composites.**  `word_b_first_dies` (`a^p b a^q c a^r`) and `word_c_first_dies`
  (`a^p c a^q b a^r`), `p, r ≥ 1`, `q ≥ 0` (`q = 0` is the pin, handled by `junction_b'_c`,
  `junction_c_b`, `junction_c'_b`), `p + q + r = n = f ≥ 3`: **`False`**.  Hypotheses are exactly
  the standard bundle (`2 ≤ f`, `n = f`, `3 ≤ n`, normal position `htgt`, `ModelData`,
  `AngleData`) and the base word laid as letters with positions; nothing about placements.
  `base_word_dies` packages both shapes.
* Non-vacuity at `f = 4` (`N = 47`, prime): `word_b_first_hyps_f4'`, `word_c_first_hyps_f4`
  (positions, fit, `p + q + r = 4`, the angle bundle at the model's own angles for `f = 4`).

## What is NOT proved (the honest residue)

* The **base word** itself — that a congruent dissection of the `e = 1` target lays its base as
  `f` letters `a`, one `b`, one `c`, first and last `a` — is a hypothesis here.  Its paper status
  is PROVED (the corner and side analysis: `thm:secondc`, `cor:pbound`, `prop:cornerpara`), not
  VERIFIED; nothing in this file touches it.
* **Normal position** (`htgt`), `ModelData` and `AngleData` are the standard bundle; `AngleData`
  is inhabited by the model angles at every natural `f ≥ 2`.
* `f ≥ 3`: the hypothesis `3 ≤ n` is inherited from `RunPartition.run_b_sub_a_dies`
  (`OrderForcing.east_cover_gap`); `f = 2` (`N = 11`) is outside every theorem here.
* The fan's placements (S3) and the pocket-area argument (S5) remain unbuilt; they are not on the
  path any more.
* The `e ≥ 2` members of the base-β branch are untouched: this file is the `e = 1` family only.

## Non-vacuity of the bundle

`bundle_witness`: for every natural `f ≥ 2` there is a concrete tile `modelTri f` (the
`(f, f²−1, f²)` triangle with its vertices in `ModelData`'s order) whose corner angles are the model
angles and satisfy `AngleData`; any congruent dissection with that model has `ModelData` and
`AngleData` for the same `α, β, γ`.  The numeric hypotheses of the two word theorems are checked at
`f = 4` (`word_b_first_hyps_f4'`, `word_c_first_hyps_f4`); the slot configurations the word
hypotheses name lie inside the target (`MarchSlots.ab_config_f4`, `.ca_config_f4`,
`RunPartition.CSlot.config_f4`).

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.MarchCompose

open Erdos634.Geometry Erdos634.CertCoord Set
open Erdos634.MarchCoords Erdos634.MarchKills Erdos634.MarchKillsFan Erdos634.MarchInduction
  Erdos634.MarchSlots Erdos634.BaseBetaTargetCoord Erdos634.RunPartition
  Erdos634.RunPartition.CSlot Erdos634.DissectionMap

/-! ## A. S1: the mirrored cap `bCapMSet` dies by overlap with the filler at `B` -/

section capM
variable {f : ℝ} (hf : 2 ≤ f) (x₀ : ℝ)
include hf

/-- The cap's far vertex `W = (x₀ − b − 1/2, h_b)` is `V + (c/b)(A − V)`: the cap's `c`-edge runs
along `[V, A]` and overruns `A` by one unit. -/
theorem capM_far_eq : mkPt (x₀ - (f ^ 2 - 1) - 1 / 2) (hB f)
    = AffineMap.lineMap (Vpt x₀) (Apt x₀ f) (f ^ 2 / (f ^ 2 - 1)) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  simp only [Vpt, Apt, lineMap_mkPt, hC, hB]
  exact mkPt_congr (by unfold dBG; field_simp; ring) (by field_simp; ring)

/-- `A` lies on the cap's edge `[V, W]`. -/
theorem A_mem_capM_edge :
    Apt x₀ f ∈ segment ℝ (Vpt x₀) (mkPt (x₀ - (f ^ 2 - 1) - 1 / 2) (hB f)) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  rw [segment_eq_image_lineMap]
  refine ⟨(f ^ 2 - 1) / f ^ 2, ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · simp only [Vpt, Apt, lineMap_mkPt, hC, hB]
    exact mkPt_congr (by unfold dBG; field_simp; ring) (by field_simp; ring)

/-- `A'` (the extension point beyond `A`) lies on the cap's edge `[V, W]` too. -/
theorem A'_mem_capM_edge :
    Apt' x₀ f ∈ segment ℝ (Vpt x₀) (mkPt (x₀ - (f ^ 2 - 1) - 1 / 2) (hB f)) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have h2 : (0:ℝ) < 2 * f ^ 2 - 1 := by nlinarith
  rw [segment_eq_image_lineMap]
  refine ⟨(2 * f ^ 2 - 1) / (2 * f ^ 2), ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · simp only [Vpt, Apt', lineMap_mkPt, hB]
    exact mkPt_congr (by field_simp; ring) (by field_simp; ring)

end capM

/-- **S1: `bCapMSet` dies.**  In a dissection containing a tile with vertex set `bCapMSet x₀ f`
and a tile whose interior contains the open extension `(A, A')` of the line `V A` beyond the
`c`-tile's apex, contradiction: the midpoint of `(A, A')` lies on the cap's `c`-edge `[V, W]` and
in the other tile's interior. -/
theorem bCapM_dies_of_blocks {N : ℕ} (D : Dissection N) {f : ℝ} (hf : 2 ≤ f) (x₀ : ℝ)
    {l m : Fin N} (hl : Set.range (D.tile l).pts = bCapMSet x₀ f)
    (hm : openSegment ℝ (Apt x₀ f) (Apt' x₀ f) ⊆ interior (D.tile m).carrier) : False := by
  set W := mkPt (x₀ - (f ^ 2 - 1) - 1 / 2) (hB f) with hW
  have hl' : Set.range (D.tile l).pts = {Vpt x₀, W, mkPt (x₀ - 1 / 2) (hB f)} := by
    rw [hl]; unfold bCapMSet; exact triple_swap
  obtain ⟨k, hk, -⟩ := edge_index_of_range hl'
  have hVW : segment ℝ (Vpt x₀) W ⊆ (D.tile l).edge k := by
    rcases hk with h | h
    · rw [h]
    · rw [h, segment_symm]
  have hsub : segment ℝ (Apt x₀ f) (Apt' x₀ f) ⊆ segment ℝ (Vpt x₀) W :=
    (convex_segment _ _).segment_subset (A_mem_capM_edge hf x₀) (A'_mem_capM_edge hf x₀)
  have hy : (1 / 2 : ℝ) • Apt x₀ f + (1 / 2 : ℝ) • Apt' x₀ f
      ∈ openSegment ℝ (Apt x₀ f) (Apt' x₀ f) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  exact D.edge_point_not_interior (hVW (hsub (openSegment_subset_segment ℝ _ _ hy))) m (hm hy)

/-- **S1 with the filler at `B` as `junction_a_c` supplies it.** -/
theorem bCapM_dies {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 2 ≤ f) (x₀ : ℝ)
    {l m : Fin N} (hl : Set.range (D.tile l).pts = bCapMSet x₀ f)
    (hm : FillerAtB D f x₀ (by linarith) m) : False :=
  bCapM_dies_of_blocks D.toDissection hf x₀ hl (filler_blocks D hf x₀ hm)

/-! ## B. The reflection in `x = L/2`, and S4 -/

/-- The linear reflection `(x, y) ↦ (−x, y)`. -/
noncomputable def negX : Plane →ₗ[ℝ] Plane where
  toFun p := mkPt (-(p 0)) (p 1)
  map_add' := by intro a b; apply plane_ext <;> simp <;> ring
  map_smul' := by intro c a; apply plane_ext <;> simp

theorem negX_apply (p : Plane) : negX p = mkPt (-(p 0)) (p 1) := rfl

theorem negX_involutive : Function.Involutive negX := by
  intro p; apply plane_ext <;> simp [negX_apply]

/-- `negX` as a linear equivalence (it is an involution). -/
noncomputable def negXEquiv : Plane ≃ₗ[ℝ] Plane := LinearEquiv.ofInvolutive negX negX_involutive

theorem negXEquiv_apply (p : Plane) : negXEquiv p = mkPt (-(p 0)) (p 1) := rfl

/-- `negX` preserves the inner product, hence is a linear isometry equivalence. -/
noncomputable def negXIso : Plane ≃ₗᵢ[ℝ] Plane :=
  negXEquiv.isometryOfInner (by
    intro x y
    simp only [negXEquiv_apply, PiLp.inner_apply, Fin.sum_univ_two, mkPt_zero, mkPt_one,
      RCLike.inner_apply, conj_trivial]
    ring)

theorem negXIso_apply (p : Plane) : negXIso p = mkPt (-(p 0)) (p 1) := by
  simp only [negXIso, LinearEquiv.coe_isometryOfInner, negXEquiv_apply]

/-- **The reflection of the plane in the vertical line `x = L/2`**, `(x, y) ↦ (L − x, y)`, as an
affine isometry equivalence. -/
noncomputable def reflX (L : ℝ) : Plane ≃ᵃⁱ[ℝ] Plane :=
  AffineIsometryEquiv.mk' (fun p => mkPt (L - p 0) (p 1)) negXIso 0 (by
    intro p
    apply plane_ext
    · simp [negXIso_apply]; ring
    · simp [negXIso_apply])

@[simp] theorem reflX_apply (L x y : ℝ) : reflX L (mkPt x y) = mkPt (L - x) y := by
  simp [reflX]

@[simp] theorem reflX_toAffineEquiv_apply (L x y : ℝ) :
    (reflX L).toAffineEquiv (mkPt x y) = mkPt (L - x) y := by
  rw [AffineIsometryEquiv.coe_toAffineEquiv]; exact reflX_apply L x y

/-- The vertex set of a transported tile is the image of the vertex set. -/
theorem mapTri_range (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    Set.range (mapTri e T).pts = e '' Set.range T.pts := by
  simp only [mapTri]; exact Set.range_comp _ _

theorem image_triple (g : Plane → Plane) (A B C : Plane) :
    g '' ({A, B, C} : Set Plane) = {g A, g B, g C} := by
  simp only [Set.image_insert_eq, Set.image_singleton]

/-- A dissection with its target replaced by a triangle with the same carrier. -/
noncomputable def retarget {N : ℕ} (D : Dissection N) (T : Tri)
    (h : T.carrier = D.target.carrier) : Dissection N where
  target := T
  tile := D.tile
  covers := D.covers.trans h.symm
  interiors_disjoint := D.interiors_disjoint

/-- The reflected `e = 1` target has the same carrier (its vertices are the same three points,
listed in another order). -/
theorem reflTarget_carrier {f : ℝ} (hf : 1 < f) :
    (mapTri (reflX (baseLen 1 f)).toAffineEquiv (baseBetaTarget 1 f one_pos hf)).carrier
      = (baseBetaTarget 1 f one_pos hf).carrier := by
  simp only [Tri.carrier]
  congr 1
  rw [mapTri_range, range_pts_eq, image_triple]
  simp only [baseBetaTarget_pts₀, baseBetaTarget_pts₁, baseBetaTarget_pts₂,
    reflX_toAffineEquiv_apply, sub_zero, sub_self]
  rw [Set.insert_comm]
  exact triple_congr rfl rfl (mkPt_congr (by ring) rfl)

/-- **The reflected congruent dissection**, target unchanged. -/
noncomputable def reflCD {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 1 < f)
    (htgt : D.target = baseBetaTarget 1 f one_pos hf) : CongruentDissection N where
  toDissection := retarget (mapDissection (reflX (baseLen 1 f)).toAffineEquiv D.toDissection)
    (baseBetaTarget 1 f one_pos hf)
    (by rw [mapDissection_target, htgt]; exact (reflTarget_carrier hf).symm)
  model := D.model
  tiles_congruent := fun i => (D.tiles_congruent i).map_left (reflX (baseLen 1 f))

theorem reflCD_target {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 1 < f)
    (htgt : D.target = baseBetaTarget 1 f one_pos hf) :
    (reflCD D hf htgt).target = baseBetaTarget 1 f one_pos hf := rfl

theorem reflCD_range {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 1 < f)
    (htgt : D.target = baseBetaTarget 1 f one_pos hf) (i : Fin N) :
    Set.range ((reflCD D hf htgt).tile i).pts
      = (reflX (baseLen 1 f)).toAffineEquiv '' Set.range (D.tile i).pts :=
  mapTri_range _ _

theorem reflCD_modelData {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 1 < f)
    (htgt : D.target = baseBetaTarget 1 f one_pos hf) (hM : ModelData D f α β γ) :
    ModelData (reflCD D hf htgt) f α β γ :=
  ⟨hM.hs0, hM.hs1, hM.hs2, hM.hα', hM.hβ', hM.hγ'⟩

/-- **S4: after `cSlotTile'`, the `GB` branch is dead.**  With the `c`-tile in the reflection
`cSlotTile' X` on `[X, X + f²]`, the `β`-tile at its left end `B` a cap or overshoot
(`junction_a_c`/`junction_b'_c`), and the `α`-tile at `V = (X + f², 0)` a mirrored filler
(`junction_c'_a`'s `GB` branch): contradiction.  Proof: reflect in `x = L/2`; the configuration
becomes `cSlotTile (L − X − f²)` with the filler at its left end and `bCapMSet`/`bOverMSet` at its
right end, killed by `bCapM_dies`/`bOverM_dies`. -/
theorem cslot'_gb_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {X : ℝ} (hX : f ≤ X) (hXL : X + f ^ 2 ≤ baseLen 1 f) {i l m : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile' X f (by linarith)).pts)
    (hl : Set.range (D.tile l).pts = bCapSet X f ∨ Set.range (D.tile l).pts = bOverSet X f)
    (hm : Set.range (D.tile m).pts = flushMSet (X + f ^ 2) f ∨
          Set.range (D.tile m).pts = offsetMSet (X + f ^ 2) f) : False := by
  have hf1 : 1 < f := by linarith
  have hi' : Set.range ((reflCD D hf1 htgt).tile i).pts
      = Set.range (cSlotTile (baseLen 1 f - X - f ^ 2) f hf1).pts := by
    rw [reflCD_range, hi, range_cSlotTile', image_triple, range_cSlotTile]
    simp only [reflX_toAffineEquiv_apply]
    rw [Set.insert_comm]
    exact triple_congr (mkPt_congr (by ring) rfl) (mkPt_congr (by ring) rfl)
      (mkPt_congr (by ring) rfl)
  have hm' : FillerAtB (reflCD D hf1 htgt) f (baseLen 1 f - X) hf1 m := by
    unfold FillerAtB
    rw [reflCD_range, flush_at hf1, offset_at hf1]
    rcases hm with h | h
    · left
      rw [h]; unfold flushMSet; rw [image_triple]
      simp only [reflX_toAffineEquiv_apply]
      exact triple_congr (mkPt_congr (by ring) rfl) (mkPt_congr (by ring) rfl)
        (mkPt_congr (by ring) rfl)
    · right
      rw [h]; unfold offsetMSet; rw [image_triple]
      simp only [reflX_toAffineEquiv_apply]
      rw [Set.pair_comm]
      exact triple_congr (mkPt_congr (by ring) rfl) (mkPt_congr (by ring) rfl)
        (mkPt_congr (by ring) rfl)
  have hx : f ^ 2 ≤ baseLen 1 f - X := by linarith
  have hL : baseLen 1 f - X + f ≤ baseLen 1 f := by linarith
  have hM' := reflCD_modelData D hf1 htgt hM
  have hi'' : Set.range ((reflCD D hf1 htgt).tile i).pts
      = Set.range (cSlotTile (baseLen 1 f - X - f ^ 2) f (by linarith)).pts := hi'
  rcases hl with h | h
  · refine bCapM_dies (reflCD D hf1 htgt) hf (baseLen 1 f - X) (l := l) ?_ hm'
    rw [reflCD_range, h]; unfold bCapSet bCapMSet; rw [image_triple]
    simp only [reflX_toAffineEquiv_apply]
    exact triple_congr rfl (mkPt_congr (by ring) rfl) (mkPt_congr (by ring) rfl)
  · refine bOverM_dies (reflCD D hf1 htgt) hf hn hn3 rfl hM' hx hL hi'' (l := l) ?_ hm'
    rw [reflCD_range, h]; unfold bOverSet bOverMSet; rw [image_triple]
    simp only [reflX_toAffineEquiv_apply]
    exact triple_congr rfl (mkPt_congr (by ring) rfl) (mkPt_congr (by ring) rfl)

/-! ## C. A `BG` run that reaches the far corner dies -/

/-- **A `BG` tile at the head of an `a`-run that ends at the far corner is impossible.**  If
`r = 1` the tile is on `[L − f, L]` and its apex is outside (`bg_apex_last_outside`); if `r ≥ 2`
the run is the march (`run_rigid`), its tile on `[L − 2f, L − f]` is `BG`, and that apex is
outside (`bg_apex_second_to_last_outside`). -/
theorem bg_run_to_end_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {t : ℝ} (ht : 0 < t) {r : ℕ} (hr : 1 ≤ r)
    (hfit : t + r * f = baseLen 1 f) (hrun : LaysARun D f t r)
    (hbase : ∃ i, Set.range (D.tile i).pts = Set.range (aTileBG t f (by linarith)).pts) :
    False := by
  have hf1 : 1 < f := by linarith
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · have hr1 : r = 1 := by omega
    subst hr1
    obtain ⟨i, hi⟩ := hbase
    obtain ⟨k, hk⟩ := mem_range_of_eq hi (by rw [range_aTileBG]; right; right; rfl)
    have hmem := pts_mem_target D.toDissection i k
    rw [hk, htgt] at hmem
    have ht' : t = baseLen 1 f - f := by push_cast at hfit; linarith
    rw [ht'] at hmem
    exact bg_apex_last_outside hf1 hmem
  · have hnL : t + r * f ≤ baseLen 1 f := hfit.le
    have hMk := run_rigid D hf htgt hM hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel hA.hirr ht hnL hrun hbase
      (r - 2) (by omega)
    obtain ⟨i, hi⟩ := hMk.1 (r - 2) le_rfl
    obtain ⟨k, hk⟩ := mem_range_of_eq hi (by rw [range_aTileBG]; right; right; rfl)
    have hmem := pts_mem_target D.toDissection i k
    rw [hk, htgt] at hmem
    have ht' : t + ((r - 2 : ℕ) : ℝ) * f = baseLen 1 f - 2 * f := by
      rw [Nat.cast_sub hr2]; push_cast; linarith
    rw [ht'] at hmem
    exact bg_apex_second_to_last_outside hf1 hmem

/-! ## D. The slots followed by runs -/

/-- The first letter of a laid run, with its positions normalised. -/
theorem run_first {N : ℕ} (D : CongruentDissection N) {f t : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hrun : LaysARun D f t r) :
    ∃ (i : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile i).pts k = mkPt t 0 ∧
      (D.tile i).pts m = mkPt (t + f) 0 := by
  obtain ⟨i, k, m, hkm, hk, hm⟩ := hrun 0 (by omega)
  exact ⟨i, k, m, hkm, by rw [hk]; congr 1; simp, by rw [hm]; congr 1; simp⟩

/-- **A `c`-slot followed by `a^r` to the far corner dies**, in either reflection, given the tile
at its left end `B` as the junction theorems deliver it (the `α`-filler for `cSlotTile`, the
`β`-cap/overshoot for `cSlotTile'`).  `GB` after the slot: S1/K2 (`bCapM_dies`, `bOverM_dies`)
or S4 (`cslot'_gb_dies`); `BG` after the slot: the run to the corner (`bg_run_to_end_dies`),
whatever completes the figure at `V`. -/
theorem cslot_then_run_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx : f ^ 2 + f ≤ x₀) {r : ℕ} (hr : 1 ≤ r)
    (hfit : x₀ + r * f = baseLen 1 f) (hrun : LaysARun D f x₀ r) {i : Fin N}
    (hc : (Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts ∧
            ∃ m, FillerAtB D f x₀ (by linarith) m) ∨
          (Set.range (D.tile i).pts = Set.range (cSlotTile' (x₀ - f ^ 2) f (by linarith)).pts ∧
            ∃ m, Set.range (D.tile m).pts = bCapSet (x₀ - f ^ 2) f ∨
                 Set.range (D.tile m).pts = bOverSet (x₀ - f ^ 2) f)) : False := by
  have hf0 : (0:ℝ) < f := by linarith
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hrf : f ≤ r * f := by nlinarith
  have hx0 : 0 < x₀ := by nlinarith
  have hxL : x₀ < baseLen 1 f := by linarith
  have hxf : x₀ + f ≤ baseLen 1 f := by linarith
  obtain ⟨j, k, m', hkm, hk, hm'⟩ := run_first D hr hrun
  rcases hc with ⟨hi, m, hm⟩ | ⟨hi, m, hm⟩
  · rcases junction_c_a D hf htgt hM hA hx0 hxL hi hkm hk hm' with
      ⟨-, l, -, -, -, -, hcap | hover⟩ | ⟨hj, -⟩
    · exact bCapM_dies D hf x₀ hcap hm
    · exact bOverM_dies D hf hn hn3 htgt hM (by linarith) hxf hi hover hm
    · exact bg_run_to_end_dies D hf htgt hM hA hx0 hr hfit hrun ⟨j, hj⟩
  · rcases junction_c'_a D hf htgt hM hA hx0 hxL hi hkm hk hm' with
      ⟨-, l, -, -, -, -, hl⟩ | ⟨hj, -⟩
    · have hl' : Set.range (D.tile l).pts = flushMSet (x₀ - f ^ 2 + f ^ 2) f ∨
          Set.range (D.tile l).pts = offsetMSet (x₀ - f ^ 2 + f ^ 2) f := by
        rwa [show x₀ - f ^ 2 + f ^ 2 = x₀ by ring]
      exact cslot'_gb_dies D hf hn hn3 htgt hM (X := x₀ - f ^ 2) (by linarith) (by linarith)
        hi hm hl'
    · exact bg_run_to_end_dies D hf htgt hM hA hx0 hr hfit hrun ⟨j, hj⟩

/-- **`bSlotTile'` followed by `a^r` to the far corner dies**: `junction_b'_a` forces `BG`, then
the run. -/
theorem bslot'_then_run_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {Y : ℝ} (hY : 0 < Y) {r : ℕ} (hr : 1 ≤ r)
    (hfit : Y + (f ^ 2 - 1) + r * f = baseLen 1 f)
    (hrun : LaysARun D f (Y + (f ^ 2 - 1)) r) {i : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (bSlotTile' Y f (by linarith)).pts) : False := by
  have hf0 : (0:ℝ) < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hrf : f ≤ r * f := by nlinarith
  obtain ⟨j, k, m, hkm, hk, hm⟩ := run_first D hr hrun
  have hi' : Set.range (D.tile i).pts
      = Set.range (bSlotTile' (Y + (f ^ 2 - 1) - (f ^ 2 - 1)) f (by linarith)).pts := by
    rw [hi]; congr 3; ring
  obtain ⟨hj, -⟩ := junction_b'_a D hf htgt hM hA (x₀ := Y + (f ^ 2 - 1)) (by linarith)
    (by linarith) hi' hkm hk hm
  exact bg_run_to_end_dies D hf htgt hM hA (by linarith) hr hfit hrun ⟨j, hj⟩

/-- **`BG` at `x₀`, then `a^q` (`q ≥ 1`), then `b`, then `a^r` to the far corner dies**: the run
is the march to the letter before `b` (`run_last_tile`), the `b`-tile is `bSlotTile'`
(`junction_a_b`), and `bslot'_then_run_dies`. -/
theorem bg_then_b_then_run_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) {q : ℕ} (hq : 1 ≤ q)
    (hrun2 : LaysARun D f x₀ q)
    (hbase : ∃ i, Set.range (D.tile i).pts = Set.range (aTileBG x₀ f (by linarith)).pts)
    {jb : Fin N} {kb mb : Fin 3} (hkmb : kb ≠ mb)
    (hkb : (D.tile jb).pts kb = mkPt (x₀ + q * f) 0)
    (hmb : (D.tile jb).pts mb = mkPt (x₀ + q * f + (f ^ 2 - 1)) 0)
    {r : ℕ} (hr : 1 ≤ r) (hfit : x₀ + q * f + (f ^ 2 - 1) + r * f = baseLen 1 f)
    (hrun3 : LaysARun D f (x₀ + q * f + (f ^ 2 - 1)) r) : False := by
  have hf0 : (0:ℝ) < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hqf : 0 ≤ (q:ℝ) * f := by positivity
  have hrf : f ≤ r * f := by nlinarith
  have hnL : x₀ + q * f ≤ baseLen 1 f := by linarith
  obtain ⟨-, i, hi⟩ := run_last_tile D hf htgt hM hA hx0 hq hnL hrun2 hbase
  have hi' : Set.range (D.tile i).pts
      = Set.range (aTileBG (x₀ + q * f - f) f (by linarith)).pts := hi
  obtain ⟨hjb, -⟩ := junction_a_b D hf htgt hM hA (x₀ := x₀ + q * f) (by linarith)
    (by linarith) hi' hkmb hkb hmb
  exact bslot'_then_run_dies D hf htgt hM hA (by linarith) hr hfit hrun3 hjb

/-! ## E. The composites: one theorem per word shape -/

/-- **THE WORD `a^p b a^q c a^r` ADMITS NO DISSECTION** (`p, r ≥ 1`, `q ≥ 0`, `p + q + r = n`,
`f = n ≥ 3`).  Hypotheses: the standard bundle and the base word laid as letters with positions
— nothing about placements.  Route: `word_b_first` (or, at the pin `q = 0`, `first_run`,
`junction_a_b`, `junction_b'_c`) reaches the `c`-slot with the tile at its left end, then
`cslot_then_run_dies`. -/
theorem word_b_first_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {p q r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) (hpqr : p + q + r = n)
    (hrun1 : LaysARun D f 0 p)
    {jb : Fin N} {kb mb : Fin 3} (hkmb : kb ≠ mb)
    (hkb : (D.tile jb).pts kb = mkPt (p * f) 0)
    (hmb : (D.tile jb).pts mb = mkPt (p * f + (f ^ 2 - 1)) 0)
    (hrun2 : LaysARun D f (p * f + (f ^ 2 - 1)) q)
    {jc : Fin N} {kc mc : Fin 3} (hkmc : kc ≠ mc)
    (hkc : (D.tile jc).pts kc = mkPt (p * f + (f ^ 2 - 1) + q * f) 0)
    (hmc : (D.tile jc).pts mc = mkPt (p * f + (f ^ 2 - 1) + q * f + f ^ 2) 0)
    (hrun3 : LaysARun D f (p * f + (f ^ 2 - 1) + q * f + f ^ 2) r) : False := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hq' : (0:ℝ) ≤ q := by positivity
  have hpf : f ≤ p * f := by nlinarith
  have hqf : 0 ≤ (q:ℝ) * f := by positivity
  have hrf : f ≤ r * f := by nlinarith
  have hsum : (p:ℝ) + q + r = f := by rw [← hn]; exact_mod_cast hpqr
  have hL' := baseLen_one f
  have hfit : p * f + (f ^ 2 - 1) + q * f + f ^ 2 + r * f = baseLen 1 f := by
    rw [hL']; linear_combination f * hsum
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · -- the pin `b c`
    subst hq0
    simp only [Nat.cast_zero, zero_mul, add_zero] at hkc hmc hrun3 hfit
    obtain ⟨-, ⟨i1, hi1⟩, -⟩ := first_run D hf htgt hM hA hp (by linarith) hrun1
    have hi1' : Set.range (D.tile i1).pts = Set.range (aTileBG (p * f - f) f hf1).pts := hi1
    obtain ⟨hjb, -⟩ := junction_a_b D hf htgt hM hA (x₀ := p * f) (by linarith) (by linarith)
      hi1' hkmb hkb hmb
    have hjb' : Set.range (D.tile jb).pts
        = Set.range (bSlotTile' (p * f + (f ^ 2 - 1) - (f ^ 2 - 1)) f hf1).pts := by
      rw [hjb]; congr 3; ring
    refine cslot_then_run_dies D hf hn hn3 htgt hM hA (x₀ := p * f + (f ^ 2 - 1) + f ^ 2)
      (by linarith) hr hfit hrun3 (i := jc) ?_
    rcases junction_b'_c D hf htgt hM hA (x₀ := p * f + (f ^ 2 - 1)) (by linarith) (by linarith)
      hjb' hkmc hkc hmc with ⟨hjc, l, -, -, -, -, hl⟩ | ⟨hjc, l, -, -, -, -, hl⟩
    · left
      refine ⟨by rw [hjc]; congr 3; ring, l, ?_⟩
      unfold FillerAtB
      rw [show p * f + (f ^ 2 - 1) + f ^ 2 - f ^ 2 - f = p * f + (f ^ 2 - 1) - f by ring]
      exact hl
    · right
      refine ⟨by rw [hjc]; congr 3; ring, l, ?_⟩
      rw [show p * f + (f ^ 2 - 1) + f ^ 2 - f ^ 2 = p * f + (f ^ 2 - 1) by ring]
      exact hl
  · -- `q ≥ 1`: `word_b_first` reaches the `c`-slot
    have hL : p * f + (f ^ 2 - 1) + q * f + f ^ 2 ≤ baseLen 1 f := by linarith
    obtain ⟨-, -, -, -, -, -, hc⟩ :=
      word_b_first D hf htgt hM hA hp hq1 hrun1 hkmb hkb hmb hrun2 hkmc hkc hmc hL
    refine cslot_then_run_dies D hf hn hn3 htgt hM hA
      (x₀ := p * f + (f ^ 2 - 1) + q * f + f ^ 2) (by linarith) hr hfit hrun3 (i := jc) ?_
    rcases hc with ⟨hjc, l, -, hl⟩ | ⟨hjc, l, -, hl⟩
    · left
      refine ⟨by rw [hjc]; congr 3; ring, l, ?_⟩
      unfold FillerAtB
      rw [show p * f + (f ^ 2 - 1) + q * f + f ^ 2 - f ^ 2 - f = p * f + (f ^ 2 - 1) + q * f - f
        by ring]
      exact hl
    · right
      refine ⟨by rw [hjc]; congr 3; ring, l, ?_⟩
      rw [show p * f + (f ^ 2 - 1) + q * f + f ^ 2 - f ^ 2 = p * f + (f ^ 2 - 1) + q * f by ring]
      exact hl

/-- **THE WORD `a^p c a^q b a^r` ADMITS NO DISSECTION** (`p, r ≥ 1`, `q ≥ 0`, `p + q + r = n`,
`f = n ≥ 3`).  Route: `word_c_first` (or, at the pin `q = 0`, `first_run`, `junction_a_c`,
`junction_c_b`/`junction_c'_b`) into the `c`-slot's right junction; `GB` there dies by S1/K2/S4,
`BG` there restarts the march, which reaches the `b`-slot and then the far corner
(`bg_then_b_then_run_dies`, `bslot'_then_run_dies`). -/
theorem word_c_first_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {p q r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) (hpqr : p + q + r = n)
    (hrun1 : LaysARun D f 0 p)
    {jc : Fin N} {kc mc : Fin 3} (hkmc : kc ≠ mc)
    (hkc : (D.tile jc).pts kc = mkPt (p * f) 0)
    (hmc : (D.tile jc).pts mc = mkPt (p * f + f ^ 2) 0)
    (hrun2 : LaysARun D f (p * f + f ^ 2) q)
    {jb : Fin N} {kb mb : Fin 3} (hkmb : kb ≠ mb)
    (hkb : (D.tile jb).pts kb = mkPt (p * f + f ^ 2 + q * f) 0)
    (hmb : (D.tile jb).pts mb = mkPt (p * f + f ^ 2 + q * f + (f ^ 2 - 1)) 0)
    (hrun3 : LaysARun D f (p * f + f ^ 2 + q * f + (f ^ 2 - 1)) r) : False := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hc0 : (0:ℝ) < f ^ 2 := by positivity
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hq' : (0:ℝ) ≤ q := by positivity
  have hpf : f ≤ p * f := by nlinarith
  have hqf : 0 ≤ (q:ℝ) * f := by positivity
  have hrf : f ≤ r * f := by nlinarith
  have hsum : (p:ℝ) + q + r = f := by rw [← hn]; exact_mod_cast hpqr
  have hL' := baseLen_one f
  have hfit : p * f + f ^ 2 + q * f + (f ^ 2 - 1) + r * f = baseLen 1 f := by
    rw [hL']; linear_combination f * hsum
  -- the filler at the `c`-slot's left end, in `FillerAtB`'s shape at `x₀ = pf + f²`
  have fillerB : ∀ {l : Fin N},
      (Set.range (D.tile l).pts = Set.range (flushFiller (p * f - f) f hf1).pts ∨
       Set.range (D.tile l).pts = Set.range (offsetFiller (p * f - f) f hf1).pts) →
      FillerAtB D f (p * f + f ^ 2) hf1 l := by
    intro l hl
    unfold FillerAtB
    rw [show p * f + f ^ 2 - f ^ 2 - f = p * f - f by ring]
    exact hl
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · -- the pin `c b`
    subst hq0
    simp only [Nat.cast_zero, zero_mul, add_zero] at hkb hmb hrun3 hfit
    obtain ⟨-, ⟨i1, hi1⟩, -⟩ := first_run D hf htgt hM hA hp (by linarith) hrun1
    have hi1' : Set.range (D.tile i1).pts = Set.range (aTileBG (p * f - f) f hf1).pts := hi1
    rcases junction_a_c D hf htgt hM hA (x₀ := p * f) (by linarith) (by linarith) hi1' hkmc hkc hmc
      with ⟨hjc, l, -, -, -, -, hl⟩ | ⟨hjc, l, -, -, -, -, hl⟩
    · -- `cSlotTile (pf)` with the filler; then `junction_c_b` at `pf + f²`
      have hjc' : Set.range (D.tile jc).pts
          = Set.range (cSlotTile (p * f + f ^ 2 - f ^ 2) f hf1).pts := by
        rw [hjc]; congr 3; ring
      rcases junction_c_b D hf htgt hM hA (x₀ := p * f + f ^ 2) (by linarith) (by linarith) hjc'
        hkmb hkb hmb with ⟨-, l', -, -, -, -, hcap | hover⟩ | ⟨hjb, -⟩
      · exact bCapM_dies D hf (p * f + f ^ 2) hcap (fillerB hl)
      · exact bOverM_dies D hf hn hn3 htgt hM (by linarith) (by linarith) hjc' hover (fillerB hl)
      · exact bslot'_then_run_dies D hf htgt hM hA (Y := p * f + f ^ 2) (by linarith) hr hfit
          hrun3 hjb
    · -- `cSlotTile' (pf)` with the cap/overshoot at `B`; then `junction_c'_b`
      have hjc' : Set.range (D.tile jc).pts
          = Set.range (cSlotTile' (p * f + f ^ 2 - f ^ 2) f hf1).pts := by
        rw [hjc]; congr 3; ring
      rcases junction_c'_b D hf htgt hM hA (x₀ := p * f + f ^ 2) (by linarith) (by linarith) hjc'
        hkmb hkb hmb with ⟨-, l', -, -, -, -, hl'⟩ | ⟨hjb, -⟩
      · exact cslot'_gb_dies D hf hn hn3 htgt hM (X := p * f) hpf (by linarith) hjc hl hl'
      · exact bslot'_then_run_dies D hf htgt hM hA (Y := p * f + f ^ 2) (by linarith) hr hfit
          hrun3 hjb
  · -- `q ≥ 1`: `word_c_first` into the `c|a` junction
    obtain ⟨ja, ka, ma, hkma, hka, hma⟩ := run_first D hq1 hrun2
    have hL : p * f + f ^ 2 + f ≤ baseLen 1 f := by nlinarith
    obtain ⟨-, hbig⟩ := word_c_first D hf htgt hM hA hp hrun1 hkmc hkc hmc hkma hka hma hL
    have hjc_c : Set.range (D.tile jc).pts = Set.range (cSlotTile (p * f) f hf1).pts →
        Set.range (D.tile jc).pts = Set.range (cSlotTile (p * f + f ^ 2 - f ^ 2) f hf1).pts := by
      intro h; rw [h]; congr 3; ring
    rcases hbig with ⟨hjc, ⟨l, -, hl⟩, hca⟩ | ⟨hjc, ⟨l, -, hl⟩, hca⟩
    · rcases hca with ⟨-, l', -, hcap | hover⟩ | ⟨hja, -⟩
      · exact bCapM_dies D hf (p * f + f ^ 2) hcap (fillerB hl)
      · exact bOverM_dies D hf hn hn3 htgt hM (by linarith) (by linarith) (hjc_c hjc) hover
          (fillerB hl)
      · exact bg_then_b_then_run_dies D hf htgt hM hA (x₀ := p * f + f ^ 2) (by linarith) hq1
          hrun2 ⟨ja, hja⟩ hkmb hkb hmb hr hfit hrun3
    · rcases hca with ⟨-, l', -, hl'⟩ | ⟨hja, -⟩
      · exact cslot'_gb_dies D hf hn hn3 htgt hM (X := p * f) hpf (by linarith) hjc hl hl'
      · exact bg_then_b_then_run_dies D hf htgt hM hA (x₀ := p * f + f ^ 2) (by linarith) hq1
          hrun2 ⟨ja, hja⟩ hkmb hkb hmb hr hfit hrun3

/-! ## F. The family, packaged -/

/-- **The base word `a^p b a^q c a^r` laid on the base of `D`**: the runs as `LaysARun`, the `b`-
and `c`-letters as tiles with two vertices at the letter's ends. -/
def LaysWordBFirst {N : ℕ} (D : CongruentDissection N) (f : ℝ) (p q r : ℕ) : Prop :=
  LaysARun D f 0 p ∧
  (∃ (jb : Fin N) (kb mb : Fin 3), kb ≠ mb ∧ (D.tile jb).pts kb = mkPt (p * f) 0 ∧
    (D.tile jb).pts mb = mkPt (p * f + (f ^ 2 - 1)) 0) ∧
  LaysARun D f (p * f + (f ^ 2 - 1)) q ∧
  (∃ (jc : Fin N) (kc mc : Fin 3), kc ≠ mc ∧
    (D.tile jc).pts kc = mkPt (p * f + (f ^ 2 - 1) + q * f) 0 ∧
    (D.tile jc).pts mc = mkPt (p * f + (f ^ 2 - 1) + q * f + f ^ 2) 0) ∧
  LaysARun D f (p * f + (f ^ 2 - 1) + q * f + f ^ 2) r

/-- **The base word `a^p c a^q b a^r` laid on the base of `D`.** -/
def LaysWordCFirst {N : ℕ} (D : CongruentDissection N) (f : ℝ) (p q r : ℕ) : Prop :=
  LaysARun D f 0 p ∧
  (∃ (jc : Fin N) (kc mc : Fin 3), kc ≠ mc ∧ (D.tile jc).pts kc = mkPt (p * f) 0 ∧
    (D.tile jc).pts mc = mkPt (p * f + f ^ 2) 0) ∧
  LaysARun D f (p * f + f ^ 2) q ∧
  (∃ (jb : Fin N) (kb mb : Fin 3), kb ≠ mb ∧
    (D.tile jb).pts kb = mkPt (p * f + f ^ 2 + q * f) 0 ∧
    (D.tile jb).pts mb = mkPt (p * f + f ^ 2 + q * f + (f ^ 2 - 1)) 0) ∧
  LaysARun D f (p * f + f ^ 2 + q * f + (f ^ 2 - 1)) r

/-- **THE `e = 1` BASE-WORD FAMILY DIES.**  A congruent dissection of `baseBetaTarget 1 f`
(`f = n ≥ 3`) with the model data and angle data of the tile `(f, f²−1, f²)`, whose base is laid
as `f` letters `a`, one `b` and one `c` with first and last letter `a` — in either order of `b`
and `c`, with any gap `q ≥ 0` between them — does not exist. -/
theorem base_word_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {p q r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) (hpqr : p + q + r = n)
    (hw : LaysWordBFirst D f p q r ∨ LaysWordCFirst D f p q r) : False := by
  rcases hw with ⟨h1, ⟨jb, kb, mb, hkmb, hkb, hmb⟩, h2, ⟨jc, kc, mc, hkmc, hkc, hmc⟩, h3⟩ |
    ⟨h1, ⟨jc, kc, mc, hkmc, hkc, hmc⟩, h2, ⟨jb, kb, mb, hkmb, hkb, hmb⟩, h3⟩
  · exact word_b_first_dies D hf hn hn3 htgt hM hA hp hr hpqr h1 hkmb hkb hmb h2 hkmc hkc hmc h3
  · exact word_c_first_dies D hf hn hn3 htgt hM hA hp hr hpqr h1 hkmc hkc hmc h2 hkmb hkb hmb h3

/-! ## G. Non-vacuity at `f = 4` (`N = 47`, prime) -/

/-- **The angle bundle at `f = 4`** (tile `(4, 15, 16)`): the model angles satisfy `AngleData`. -/
theorem angleData_f4 : ∃ α β γ : ℝ, AngleData α β γ := by
  refine ⟨modelAlpha 1 4, modelBeta 1 4, 2 * modelAlpha 1 4 + modelBeta 1 4,
    ⟨modelAlpha_pos (by norm_num),
      (modelAlpha_pos (by norm_num)).trans (modelAlpha_lt_modelBeta (by norm_num)),
      (modelAlpha_lt_modelBeta (by norm_num)).ne, rfl,
      modelAngle_rel 1 4, ?_⟩⟩
  have h := modelAlpha_irrational 4 (by norm_num)
  rw [show ((4 : ℕ) : ℝ) = 4 by norm_num] at h
  exact h

/-- **`word_b_first_dies`' numeric hypotheses at `f = 4`, `p = 1`, `q = 2`, `r = 1`** (word
`a b a a c a`, `N = 47`): `n = 4 ≥ 3`, `1 + 2 + 1 = 4`, the letter positions `4, 19, 27, 43` and
the exact fit `43 + 4 = 47 = L`; the angle bundle is inhabited.  (The laid-word hypotheses are
about a dissection, which the theorem says does not exist; the slot configurations they name are
inside the target: `MarchSlots.ab_config_f4`, `.ca_config_f4`, `RunPartition.CSlot.config_f4`.) -/
theorem word_b_first_hyps_f4' :
    ((4 : ℕ) : ℝ) = 4 ∧ 3 ≤ (4 : ℕ) ∧ 1 + 2 + 1 = (4 : ℕ) ∧
    (1 : ℝ) * 4 = 4 ∧ (1 : ℝ) * 4 + (4 ^ 2 - 1) = 19 ∧
    (1 : ℝ) * 4 + (4 ^ 2 - 1) + 2 * 4 = 27 ∧
    (1 : ℝ) * 4 + (4 ^ 2 - 1) + 2 * 4 + 4 ^ 2 = 43 ∧
    (1 : ℝ) * 4 + (4 ^ 2 - 1) + 2 * 4 + 4 ^ 2 + 1 * 4 = baseLen 1 4 ∧
    ∃ α β γ, AngleData α β γ := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by rw [baseLen_one]; norm_num, angleData_f4⟩

/-- **`word_c_first_dies`' numeric hypotheses at `f = 4`, `p = 1`, `q = 1`, `r = 2`** (word
`a c a b a a`): positions `4, 20, 24, 39` and the fit `39 + 2·4 = 47 = L`. -/
theorem word_c_first_hyps_f4 :
    ((4 : ℕ) : ℝ) = 4 ∧ 3 ≤ (4 : ℕ) ∧ 1 + 1 + 2 = (4 : ℕ) ∧
    (1 : ℝ) * 4 = 4 ∧ (1 : ℝ) * 4 + 4 ^ 2 = 20 ∧ (1 : ℝ) * 4 + 4 ^ 2 + 1 * 4 = 24 ∧
    (1 : ℝ) * 4 + 4 ^ 2 + 1 * 4 + (4 ^ 2 - 1) = 39 ∧
    (1 : ℝ) * 4 + 4 ^ 2 + 1 * 4 + (4 ^ 2 - 1) + 2 * 4 = baseLen 1 4 ∧
    ∃ α β γ, AngleData α β γ := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by rw [baseLen_one]; norm_num, angleData_f4⟩

/-- The reflection at `f = 4` sends the `cSlotTile'` configuration of `ca_config_f4`'s mirror to
the `cSlotTile` configuration: `reflX 47` maps `(4, 0) ↦ (43, 0)`, `(20, 0) ↦ (27, 0)`. -/
theorem reflX_f4 : reflX 47 (mkPt 4 0) = mkPt 43 0 ∧ reflX 47 (mkPt 20 0) = mkPt 27 0 := by
  refine ⟨?_, ?_⟩ <;> rw [reflX_apply] <;> norm_num

/-! ### The model bundle is jointly satisfiable: a concrete tile with `ModelData`'s shape

`ModelData D f α β γ` speaks only of `D.model`.  `modelTri f` is the tile `(f, f²−1, f²)` with its
vertices in `ModelData`'s order (vertex `0` opposite the side `f`, vertex `1` opposite `f²−1`,
vertex `2` opposite `f²`), and its corner angles are the model angles `modelAlpha 1 f`,
`modelBeta 1 f`, `2α + β` — which satisfy `AngleData` for every natural `f ≥ 2`.  So the
hypotheses `ModelData` and `AngleData` of every theorem above hold together of any congruent
dissection whose model is `modelTri f`. -/

theorem det_modelTri {f : ℝ} (hf : 1 < f) :
    det3 (f ^ 2) 0 0 0 (dBG f / f) (1 / f * apexH f) ≠ 0 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have : det3 (f ^ 2) 0 0 0 (dBG f / f) (1 / f * apexH f) = -(f * apexH f) := by
    unfold det3; field_simp; ring
  rw [this]; exact neg_ne_zero.mpr (mul_pos (by linarith) (apexH_pos hf)).ne'

/-- The tile `(f, f²−1, f²)` in `ModelData`'s vertex order: `V = (f², 0)`, `B = (0, 0)`, apex
`(dBG/f, h/f)` — `cSlotTile 0 f` with its two base vertices swapped. -/
noncomputable def modelTri (f : ℝ) (hf : 1 < f) : Tri :=
  mkTri (f ^ 2) 0 0 0 (dBG f / f) (1 / f * apexH f) (det_modelTri hf)

open Erdos634.TilePlacement in
theorem modelTri_sides {f : ℝ} (hf : 2 ≤ f) :
    sideOpp (modelTri f (by linarith)) 0 = f ∧
    sideOpp (modelTri f (by linarith)) 1 = f ^ 2 - 1 ∧
    sideOpp (modelTri f (by linarith)) 2 = f ^ 2 := by
  have hf1 : 1 < f := by linarith
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : (0:ℝ) ≤ f ^ 2 - 1 := by nlinarith
  simp only [sideOpp, modelTri, mkTri_pts₀, mkTri_pts₁, mkTri_pts₂]
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt 0 0) (mkPt (dBG f / f) (1 / f * apexH f)) = f
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by linarith)
    rw [dist_sq_zero_kapex hf1]; unfold h2 dBG; field_simp; ring
  · show dist (mkPt (dBG f / f) (1 / f * apexH f)) (mkPt (f ^ 2) 0) = f ^ 2 - 1
    refine dist_eq_of_sq_eq ?_ dist_nonneg hb
    rw [dist_comm, dist_sq_zero_kapex hf1]; unfold h2 dBG; field_simp; ring
  · show dist (mkPt (f ^ 2) 0) (mkPt 0 0) = f ^ 2
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt]; ring

/-- A corner angle is determined by the cosine it satisfies, on `[0, π]`. -/
theorem cornerAngle_eq_of_cos {p q r : Plane} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (h : Real.cos (cornerAngle p q r) = Real.cos θ) : cornerAngle p q r = θ :=
  Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨hθ0, hθπ⟩ h

/-- **The model tile's corner angles are the model angles.** -/
theorem modelTri_angles {f : ℝ} (hf : 2 ≤ f) :
    cornerAngle ((modelTri f (by linarith)).pts 1) ((modelTri f (by linarith)).pts 0)
        ((modelTri f (by linarith)).pts 2) = modelAlpha 1 f ∧
    cornerAngle ((modelTri f (by linarith)).pts 2) ((modelTri f (by linarith)).pts 1)
        ((modelTri f (by linarith)).pts 0) = modelBeta 1 f ∧
    cornerAngle ((modelTri f (by linarith)).pts 0) ((modelTri f (by linarith)).pts 2)
        ((modelTri f (by linarith)).pts 1) = 2 * modelAlpha 1 f + modelBeta 1 f := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  obtain ⟨hs0, hs1, hs2⟩ := modelTri_sides hf
  simp only [Erdos634.TilePlacement.sideOpp] at hs0 hs1 hs2
  have hs0' : dist ((modelTri f hf1).pts 1) ((modelTri f hf1).pts 2) = f := hs0
  have hs1' : dist ((modelTri f hf1).pts 2) ((modelTri f hf1).pts 0) = f ^ 2 - 1 := hs1
  have hs2' : dist ((modelTri f hf1).pts 0) ((modelTri f hf1).pts 1) = f ^ 2 := hs2
  have hα0 := modelAlpha_pos hf1
  have hαπ := modelAlpha_lt_pi_div_three hf1
  have hβ := modelBeta_mem one_pos hf1
  have hpi := Real.pi_pos
  have hcosα := cos_modelAlpha one_pos hf1
  have hcosβ := cos_modelBeta one_pos hf1
  have hrel := modelAngle_rel 1 f
  -- α at vertex 0, by the law of cosines on `B, V, apex`
  have hA : cornerAngle ((modelTri f hf1).pts 1) ((modelTri f hf1).pts 0) ((modelTri f hf1).pts 2)
      = modelAlpha 1 f := by
    refine cornerAngle_eq_of_cos hα0.le (by linarith) ?_
    have hlc := EuclideanGeometry.law_cos ((modelTri f hf1).pts 1) ((modelTri f hf1).pts 0)
      ((modelTri f hf1).pts 2)
    unfold cornerAngle
    rw [hs0', dist_comm ((modelTri f hf1).pts 1), hs2', hs1'] at hlc
    rw [hcosα]
    have hne : 2 * f ^ 2 * (f ^ 2 - 1) ≠ 0 := by positivity
    field_simp
    nlinarith [hlc]
  -- β at vertex 1, by the law of cosines on `apex, B, V`
  have hB : cornerAngle ((modelTri f hf1).pts 2) ((modelTri f hf1).pts 1) ((modelTri f hf1).pts 0)
      = modelBeta 1 f := by
    refine cornerAngle_eq_of_cos hβ.1.le (by linarith) ?_
    have hlc := EuclideanGeometry.law_cos ((modelTri f hf1).pts 2) ((modelTri f hf1).pts 1)
      ((modelTri f hf1).pts 0)
    unfold cornerAngle
    rw [hs1', dist_comm ((modelTri f hf1).pts 2), hs0', hs2'] at hlc
    rw [hcosβ, baseLen_one]
    have hne : 2 * f * f ^ 2 ≠ 0 := by positivity
    field_simp
    nlinarith [hlc]
  refine ⟨hA, hB, ?_⟩
  have hsum := cornerAngle_sum (modelTri f hf1)
  rw [hA, hB] at hsum
  linarith

/-- **The standard bundle is jointly inhabited** for every natural `f ≥ 2`: the tile `modelTri f`
has `ModelData`'s shape with the model angles, and those angles satisfy `AngleData`.  Hence any
congruent dissection `D` with `D.model = modelTri f` satisfies `ModelData D f α β γ` and
`AngleData α β γ` for the same `α, β, γ`. -/
theorem bundle_witness (n : ℕ) (hn : 2 ≤ n) :
    ∃ (T : Tri) (α β γ : ℝ),
      Erdos634.TilePlacement.sideOpp T 0 = n ∧ Erdos634.TilePlacement.sideOpp T 1 = (n : ℝ) ^ 2 - 1 ∧
      Erdos634.TilePlacement.sideOpp T 2 = (n : ℝ) ^ 2 ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = α ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = β ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = γ ∧ AngleData α β γ ∧
      ∀ {N : ℕ} (D : CongruentDissection N), D.model = T → ModelData D n α β γ := by
  have hf : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hf1 : (1:ℝ) < n := by linarith
  obtain ⟨hs0, hs1, hs2⟩ := modelTri_sides hf
  obtain ⟨hA, hB, hC⟩ := modelTri_angles hf
  refine ⟨modelTri n hf1, modelAlpha 1 n, modelBeta 1 n, 2 * modelAlpha 1 n + modelBeta 1 n,
    hs0, hs1, hs2, hA, hB, hC,
    ⟨modelAlpha_pos hf1, (modelAlpha_pos hf1).trans (modelAlpha_lt_modelBeta hf),
      (modelAlpha_lt_modelBeta hf).ne, rfl, modelAngle_rel 1 n,
      modelAlpha_irrational n hn⟩, ?_⟩
  intro N D hD
  exact ⟨by rw [hD]; exact hs0, by rw [hD]; exact hs1, by rw [hD]; exact hs2,
    by rw [hD]; exact hA, by rw [hD]; exact hB, by rw [hD]; exact hC⟩

end Erdos634.MarchCompose

#print axioms Erdos634.MarchCompose.bCapM_dies
#print axioms Erdos634.MarchCompose.reflCD
#print axioms Erdos634.MarchCompose.cslot'_gb_dies
#print axioms Erdos634.MarchCompose.bg_run_to_end_dies
#print axioms Erdos634.MarchCompose.cslot_then_run_dies
#print axioms Erdos634.MarchCompose.bslot'_then_run_dies
#print axioms Erdos634.MarchCompose.bg_then_b_then_run_dies
#print axioms Erdos634.MarchCompose.word_b_first_dies
#print axioms Erdos634.MarchCompose.word_c_first_dies
#print axioms Erdos634.MarchCompose.base_word_dies
#print axioms Erdos634.MarchCompose.angleData_f4
#print axioms Erdos634.MarchCompose.word_b_first_hyps_f4'
#print axioms Erdos634.MarchCompose.word_c_first_hyps_f4
#print axioms Erdos634.MarchCompose.modelTri_angles
#print axioms Erdos634.MarchCompose.bundle_witness
