import Erdos634.ThickBlockingLemmas
import Erdos634.SixPlacements

/-!
# Lemma P, node 2, as a theorem about dissections

Erdős #634, `(e,f) = (2,3)`, tile `(6,5,9)`, `N = 23`.  `ThickBlockingLemmas.blocking_B1` proved
that at the corner `v = (6,0)` with ray `d₀ = (7/9, √32/9)` all six oriented placements escape the
target, and `B1_witness` exhibited the two-tile configuration `w1t0, w1t1` in which that corner
arises.  What was missing — the file said so — was **placement completeness**: that a dissection
extending the configuration *must* use one of those six placements.  With
`PlacementCompleteness.placement_completeness` and `SixPlacements.six_placements` that hypothesis
is now a theorem, and node 2 of Lemma P becomes a statement about dissections:

> `node2_jam`: no `CongruentDissection` whose target is the `(2,3)` base-`β` target and whose
> model is congruent to `(6,5,9)` contains both `w1t0` and `w1t1` as tiles.

This is **one node of thirteen**.  Lemma P itself (no dissection has base word beginning `a c b`)
needs the other twelve, including the three jams that are killed by overlap rather than escape
(nodes 6, 7, 12) and the base-word hypothesis at the root; none of that is here.

The per-node obligations discharged below, exactly: `hlex` (the closure of the unfilled region
lies in `x ≥ 6`, because the target's `x < 6` part is inside `w1t0`), `hfree` (points just
counter-clockwise of `d₀` are in the target and outside both tiles), `hblocked` (a wedge just
clockwise of `d₀` is inside `w1t1`), the six third-vertex evaluations in `ℚ(√32)`, and the six
left-leg escapes — the same six points as `blocking_B1` (`six_eq_B1`).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LemmaPNode2

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.ThickBlockingLemmas
  Erdos634.PlacementCompleteness Erdos634.SixPlacements

theorem rr_bounds : 5 < rr ∧ rr < 6 := by
  constructor <;> nlinarith [rr_sq, rr_pos]

/-- The corner of node 2. -/
noncomputable def v2 : Plane := mkPt 6 0
/-- The forced ray of node 2, a unit vector. -/
noncomputable def d2 : Plane := mkPt (7 / 9) (rr / 9)

theorem d2_unit : d2 0 ^ 2 + d2 1 ^ 2 = 1 := by
  simp only [d2, mkPt_zero, mkPt_one]
  linear_combination (1 / 81 : ℝ) * rr_sq

theorem mkPt_self (p : Plane) : mkPt (p 0) (p 1) = p := plane_ext (by simp) (by simp)

theorem pt_ccw (t s : ℝ) : v2 + t • (d2 + s • perp d2)
    = mkPt (6 + t * (7 / 9 - s * (rr / 9))) (t * (rr / 9 + s * (7 / 9))) := by
  refine plane_ext ?_ ?_ <;> simp [v2, d2] <;> ring

theorem pt_cw (t s : ℝ) : v2 + t • (d2 - s • perp d2)
    = mkPt (6 + t * (7 / 9 + s * (rr / 9))) (t * (rr / 9 - s * (7 / 9))) := by
  refine plane_ext ?_ ?_ <;> simp [v2, d2] <;> ring

/-! ## Membership facts for the target and the two placed tiles -/

theorem target63_y_nonneg {p : Plane} (hp : p ∈ target63.carrier) : 0 ≤ p 1 := by
  by_contra h; push_neg at h
  exact not_mem_target63_of_below h (by rw [mkPt_self]; exact hp)

theorem target63_left {p : Plane} (hp : p ∈ target63.carrier) :
    0 ≤ 5 / 2 * rr * p 0 - 23 * p 1 := by
  by_contra h; push_neg at h
  exact not_mem_target63_of_left (x := p 0) (y := p 1) (by linarith) (by rw [mkPt_self]; exact hp)

/-- The `x < 6` part of the target is inside `w1t0`. -/
theorem mem_w1t0_of {x y : ℝ} (hy : 0 ≤ y) (hl : 0 ≤ 5 / 2 * rr * x - 23 * y) (hx : x ≤ 6) :
    mkPt x y ∈ w1t0.carrier := by
  refine mem_carrier_of_dets (x₀ := 0) (y₀ := 0) (x₁ := 6) (y₁ := 0) (x₂ := 23 / 3)
    (y₂ := (5 / 6 : ℝ) * rr) ?_ ?_ ?_ ?_
  · have h : det3 (0:ℝ) (0:ℝ) (6:ℝ) (0:ℝ) (23/3:ℝ) ((5/6:ℝ)*rr) = 5 * rr := by unfold det3; ring
    rw [h]; nlinarith [rr_pos]
  · unfold det3; nlinarith [rr_pos]
  · unfold det3; nlinarith
  · unfold det3; nlinarith

theorem w1t0_functional {p : Plane} (hp : p ∈ w1t0.carrier) :
    0 ≤ (5 / 3) * p 1 - (5 / 6 * rr) * (p 0 - 6) := by
  have hb : ∀ z ∈ w1t0.carrier, 0 ≤ lineFun 6 0 (23 / 3) ((5 / 6 : ℝ) * rr) z := by
    refine ge_of_forall_pts_ge _ ?_
    intro k
    fin_cases k <;>
      simp [w1t0, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;> nlinarith [rr_pos]
  have := hb p hp
  simp only [lineFun_apply] at this
  linarith

theorem w1t1_functional {p : Plane} (hp : p ∈ w1t1.carrier) :
    (35 / 9) * p 1 - (5 / 9 * rr) * (p 0 - 6) ≤ 0 := by
  have hb : ∀ z ∈ w1t1.carrier, lineFun 6 0 (89 / 9) ((5 / 9 : ℝ) * rr) z ≤ 0 := by
    refine le_of_forall_pts_le _ ?_
    intro k
    fin_cases k <;>
      simp [w1t1, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;> nlinarith [rr_pos]
  have := hb p hp
  simp only [lineFun_apply] at this
  linarith

theorem mem_w1t1_of {x y : ℝ} (h₀ : 0 ≤ (15 - x) * (5 / 9 * rr) - (46 / 9) * y)
    (h₁ : 0 ≤ (x - 6) * (5 / 9 * rr) - (35 / 9) * y) (h₂ : 0 ≤ y) :
    mkPt x y ∈ w1t1.carrier := by
  refine mem_carrier_of_dets (x₀ := 6) (y₀ := 0) (x₁ := 15) (y₁ := 0) (x₂ := 89 / 9)
    (y₂ := (5 / 9 : ℝ) * rr) ?_ ?_ ?_ ?_
  · have h : det3 (6:ℝ) (0:ℝ) (15:ℝ) (0:ℝ) (89/9:ℝ) ((5/9:ℝ)*rr) = 5 * rr := by unfold det3; ring
    rw [h]; nlinarith [rr_pos]
  · unfold det3; nlinarith
  · unfold det3; nlinarith
  · unfold det3; nlinarith

/-! ## The six third vertices, evaluated in `ℚ(√32)` -/

theorem placeThird_eval (ℓ₁ ℓ₂ ℓ₃ p q X Y : ℝ)
    (hp : (ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) / (2 * ℓ₁) = p) (hq : 0 ≤ q) (hq2 : ℓ₂ ^ 2 - p ^ 2 = q ^ 2)
    (hX : 6 + p * (7 / 9) - q * (rr / 9) = X) (hY : p * (rr / 9) + q * (7 / 9) = Y) :
    placeThird v2 d2 ℓ₁ ℓ₂ ℓ₃ = mkPt X Y := by
  rw [placeThird, hp, hq2, Real.sqrt_sq hq]
  refine plane_ext ?_ ?_ <;> simp [v2, d2] <;> linarith

theorem six_1 : placeThird v2 d2 6 9 5 = mkPt 9 ((3 / 2 : ℝ) * rr) :=
  placeThird_eval _ _ _ (23 / 3) (5 / 6 * rr) _ _ (by norm_num) (by have := rr_pos; positivity)
    (by linear_combination (-(25 / 36 : ℝ)) * rr_sq) (by linear_combination (-(5 / 54 : ℝ)) * rr_sq)
    (by ring)

theorem six_2 : placeThird v2 d2 9 6 5 = mkPt 8 ((1 : ℝ) * rr) :=
  placeThird_eval _ _ _ (46 / 9) (5 / 9 * rr) _ _ (by norm_num) (by have := rr_pos; positivity)
    (by linear_combination (-(25 / 81 : ℝ)) * rr_sq) (by linear_combination (-(5 / 81 : ℝ)) * rr_sq)
    (by ring)

theorem six_3 : placeThird v2 d2 6 5 9 = mkPt (47 / 27) ((25 / 54 : ℝ) * rr) :=
  placeThird_eval _ _ _ (-5 / 3) (5 / 6 * rr) _ _ (by norm_num) (by have := rr_pos; positivity)
    (by linear_combination (-(25 / 36 : ℝ)) * rr_sq) (by linear_combination (-(5 / 54 : ℝ)) * rr_sq)
    (by ring)

theorem six_4 : placeThird v2 d2 5 6 9 = mkPt (8 / 9) ((5 / 9 : ℝ) * rr) :=
  placeThird_eval _ _ _ (-2) rr _ _ (by norm_num) rr_pos.le
    (by linear_combination (-1 : ℝ) * rr_sq) (by linear_combination (-(1 / 9 : ℝ)) * rr_sq)
    (by ring)

theorem six_5 : placeThird v2 d2 9 5 6 = mkPt (571 / 81) ((70 / 81 : ℝ) * rr) :=
  placeThird_eval _ _ _ (35 / 9) (5 / 9 * rr) _ _ (by norm_num) (by have := rr_pos; positivity)
    (by linear_combination (-(25 / 81 : ℝ)) * rr_sq) (by linear_combination (-(5 / 81 : ℝ)) * rr_sq)
    (by ring)

theorem six_6 : placeThird v2 d2 5 9 6 = mkPt (71 / 9) ((14 / 9 : ℝ) * rr) :=
  placeThird_eval _ _ _ 7 rr _ _ (by norm_num) rr_pos.le
    (by linear_combination (-1 : ℝ) * rr_sq) (by linear_combination (-(1 / 9 : ℝ)) * rr_sq)
    (by ring)

/-- **The six placements of `six_placements` at node 2 are exactly the six of `blocking_B1`.** -/
theorem six_eq_B1 :
    placeThird v2 d2 6 9 5 = b1beta69.pts 2 ∧ placeThird v2 d2 9 6 5 = b1beta96.pts 2 ∧
    placeThird v2 d2 6 5 9 = b1gamma65.pts 2 ∧ placeThird v2 d2 5 6 9 = b1gamma56.pts 2 ∧
    placeThird v2 d2 9 5 6 = b1alpha95.pts 2 ∧ placeThird v2 d2 5 9 6 = b1alpha59.pts 2 :=
  ⟨six_1, six_2, six_3, six_4, six_5, six_6⟩

/-! ## The jam -/

theorem dist_of_sq {x y : Plane} {c : ℝ} (hc : 0 ≤ c) (h : dist x y ^ 2 = c ^ 2) : dist x y = c := by
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- **NODE 2 OF LEMMA P, AS A THEOREM ABOUT DISSECTIONS.**  No congruent dissection of the
`(2,3)` base-`β` target by copies of `(6,5,9)` contains both `w1t0` and `w1t1` as tiles. -/
theorem node2_jam {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = target63.carrier)
    (hmodel : D.model.Congruent w1t0)
    (i₀ i₁ : Fin N) (h₀ : D.tile i₀ = w1t0) (h₁ : D.tile i₁ = w1t1) : False := by
  classical
  obtain ⟨hr5, hr6⟩ := rr_bounds
  set S : Finset (Fin N) := {i₀, i₁} with hS
  have hU : ∀ p, p ∈ unfilled D.toDissection S ↔
      p ∈ target63.carrier ∧ p ∉ w1t0.carrier ∧ p ∉ w1t1.carrier := by
    intro p
    rw [unfilled, Set.mem_diff, Set.mem_iUnion₂]
    simp only [hS, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hn⟩
      refine ⟨htarget ▸ hp, fun h => hn ⟨i₀, Or.inl rfl, by rw [h₀]; exact h⟩,
        fun h => hn ⟨i₁, Or.inr rfl, by rw [h₁]; exact h⟩⟩
    · rintro ⟨hp, h0, h1⟩
      refine ⟨htarget ▸ hp, ?_⟩
      rintro ⟨i, hi | hi, hpi⟩
      · subst hi; rw [h₀] at hpi; exact h0 hpi
      · subst hi; rw [h₁] at hpi; exact h1 hpi
  -- (i) lexicographic minimality of `(6,0)` on the closure of the unfilled region
  have hlex : ∀ p ∈ closure (unfilled D.toDissection S), LexLE v2 p := by
    have hsub : unfilled D.toDissection S ⊆ {p : Plane | 6 ≤ p 0} ∩ target63.carrier := by
      intro p hp
      obtain ⟨hpt, hp0, -⟩ := (hU p).mp hp
      refine ⟨?_, hpt⟩
      show 6 ≤ p 0
      by_contra hlt; push_neg at hlt
      apply hp0
      rw [← mkPt_self p]
      exact mem_w1t0_of (target63_y_nonneg hpt) (target63_left hpt) hlt.le
    have hcl : IsClosed ({p : Plane | 6 ≤ p 0} ∩ target63.carrier) :=
      (isClosed_le continuous_const
        (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous).inter
        target63.isCompact.isClosed
    intro p hp
    obtain ⟨h6, hpt⟩ := closure_minimal hsub hcl hp
    have hy := target63_y_nonneg hpt
    simp only [LexLE, v2, mkPt_zero, mkPt_one]
    rcases lt_or_eq_of_le hy with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h6⟩
  -- (ii) the counter-clockwise side of `d₀` is free
  have hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      v2 + t • (d2 + s • perp d2) ∈ unfilled D.toDissection S := by
    intro ε hε
    have hmin : min (ε / 2) (1 / 4) < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨min (ε / 2) (1 / 4), min (ε / 2) (1 / 4), by positivity, hmin, by positivity, hmin, ?_⟩
    set t := min (ε / 2) (1 / 4) with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 / 4 := min_le_right _ _
    rw [pt_ccw, hU]
    have htr : t * rr ≤ 3 / 2 := by nlinarith
    have ht2 : t ^ 2 ≤ 1 / 16 := by nlinarith
    refine ⟨mem_target63 (by positivity) ?_ ?_, ?_, ?_⟩
    · have e : 5 / 2 * rr * (6 + t * (7 / 9 - t * (rr / 9))) - 23 * (t * (rr / 9 + t * (7 / 9)))
          = 15 * rr - (11 / 18) * (t * rr) - (241 / 9) * t ^ 2 := by
        linear_combination (-(5 / 18) * t ^ 2) * rr_sq
      rw [e]; nlinarith
    · have e : 5 / 2 * rr * (46 - (6 + t * (7 / 9 - t * (rr / 9)))) - 23 * (t * (rr / 9 + t * (7 / 9)))
          = 100 * rr - (81 / 18) * (t * rr) - 9 * t ^ 2 := by
        linear_combination ((5 / 18) * t ^ 2) * rr_sq
      rw [e]; nlinarith
    · intro h
      have hf := w1t0_functional h
      simp only [mkPt_zero, mkPt_one] at hf
      have e : (5 / 3) * (t * (rr / 9 + t * (7 / 9))) - (5 / 6 * rr) * (6 + t * (7 / 9 - t * (rr / 9)) - 6)
          = t * (230 * t - 25 * rr) / 54 := by
        linear_combination (5 / 54 * t ^ 2) * rr_sq
      rw [e] at hf
      have : t * (230 * t - 25 * rr) < 0 := mul_neg_of_pos_of_neg ht0 (by linarith)
      linarith
    · intro h
      have hf := w1t1_functional h
      simp only [mkPt_zero, mkPt_one] at hf
      have e : (35 / 9) * (t * (rr / 9 + t * (7 / 9))) - (5 / 9 * rr) * (6 + t * (7 / 9 - t * (rr / 9)) - 6)
          = 5 * t ^ 2 := by
        linear_combination (5 / 81 * t ^ 2) * rr_sq
      rw [e] at hf
      nlinarith
  -- (iii) a wedge just clockwise of `d₀` is inside `w1t1`
  have hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      v2 + t • (d2 - s • perp d2) ∉ unfilled D.toDissection S := by
    refine ⟨1 / 4, by norm_num, fun t s ht htδ hs hsδ => ?_⟩
    rw [pt_cw, hU]
    rintro ⟨-, -, h1⟩
    apply h1
    have htr : t * rr ≤ 3 / 2 := by nlinarith
    refine mem_w1t1_of ?_ ?_ ?_
    · have e : (15 - (6 + t * (7 / 9 + s * (rr / 9)))) * (5 / 9 * rr) - (46 / 9) * (t * (rr / 9 - s * (7 / 9)))
          = 5 * rr - t * rr + 2 * (t * s) := by
        linear_combination (-(5 / 81) * t * s) * rr_sq
      rw [e]; nlinarith [mul_pos ht hs]
    · have e : (6 + t * (7 / 9 + s * (rr / 9)) - 6) * (5 / 9 * rr) - (35 / 9) * (t * (rr / 9 - s * (7 / 9)))
          = 5 * t * s := by
        linear_combination (5 / 81 * t * s) * rr_sq
      rw [e]; positivity
    · apply mul_nonneg ht.le; linarith
  -- (iv) placement completeness gives an unplaced tile at the forced corner
  obtain ⟨j, hj, k₀, k₁, k₂, h01, h02, h12, hk₀, ⟨c', hc', hk₁⟩, hk₂⟩ :=
    placement_completeness D.toDissection S v2 d2 d2_unit hlex hfree hblocked
  -- (v) it is one of the six, and all six escape through the left leg
  have hcong : (D.tile j).Congruent w1t0 := (D.tiles_congruent j).trans hmodel
  obtain ⟨s01, s12, s20⟩ := sides_w1t0
  have hMa : dist (w1t0.pts 0) (w1t0.pts 1) = 6 := dist_of_sq (by norm_num) (by rw [s01]; norm_num)
  have hMb : dist (w1t0.pts 1) (w1t0.pts 2) = 5 := dist_of_sq (by norm_num) (by rw [s12]; norm_num)
  have hMc : dist (w1t0.pts 0) (w1t0.pts 2) = 9 := by
    rw [dist_comm]; exact dist_of_sq (by norm_num) (by rw [s20]; norm_num)
  have hsub : (D.tile j).carrier ⊆ target63.carrier :=
    htarget ▸ Erdos634.BaseSelection.tile_subset_target D.toDissection j
  have hmem : (D.tile j).pts k₂ ∈ target63.carrier :=
    hsub (subset_convexHull ℝ _ (Set.mem_range_self k₂))
  rcases six_placements hcong hMa hMb hMc d2_unit h01 h02 h12 hk₀ hc' hk₁ hk₂ with
    ⟨-, hw⟩ | ⟨-, hw⟩ | ⟨-, hw⟩ | ⟨-, hw⟩ | ⟨-, hw⟩ | ⟨-, hw⟩
  · rw [hw, six_1] at hmem; exact not_mem_target63_of_left (by linarith [rr_pos]) hmem
  · rw [hw, six_2] at hmem; exact not_mem_target63_of_left (by linarith [rr_pos]) hmem
  · rw [hw, six_3] at hmem; exact not_mem_target63_of_left (by linarith [rr_pos]) hmem
  · rw [hw, six_4] at hmem; exact not_mem_target63_of_left (by linarith [rr_pos]) hmem
  · rw [hw, six_5] at hmem; exact not_mem_target63_of_left (by linarith [rr_pos]) hmem
  · rw [hw, six_6] at hmem; exact not_mem_target63_of_left (by linarith [rr_pos]) hmem

/-- **Non-vacuity, restated**: the hypotheses of `node2_jam` describe a configuration that exists
(`B1_witness`): two tiles congruent to `(6,5,9)` inside the target with disjoint interiors.  What
`node2_jam` adds is that no dissection *extends* it. -/
theorem node2_configuration_exists :
    w1t0.carrier ⊆ target63.carrier ∧ w1t1.carrier ⊆ target63.carrier ∧
    Disjoint (interior w1t0.carrier) (interior w1t1.carrier) :=
  ⟨B1_witness.1, B1_witness.2.1, B1_witness.2.2.1⟩

end Erdos634.LemmaPNode2

#print axioms Erdos634.LemmaPNode2.node2_jam
