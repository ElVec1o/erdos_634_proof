import Mathlib.Tactic
import Erdos634.AngleSumDissection
import Erdos634.PinLemma
import Erdos634.WallChain
import Erdos634.CongruentAngles

/-!
# The pin plumbing: the angle equation at a base junction, from the dissection layer

Erdős #634.  `PinLemma` proved the pin's forced multisets from an angle-sum *hypothesis*.  This
file discharges that hypothesis against the real machinery: for any dissection and any point of
the target's boundary that is not a target vertex — in particular any base junction interior to
the base edge — the tiles' local angles sum to exactly `π`.  This is `sum_localAngle_eq` (the
discharged `G2`) composed with `localAngle_frontier`, and nothing else.

With it, the pin argument's non-arithmetic residue shrinks to: identifying each tile's local angle
at the pin (a vertex of a tile congruent to the base tile contributes one of `α, β, γ`; a tile
with the pin interior to an edge contributes `π`; all others `0` — the definition's four cases),
and the covering data along the flanking rays (`wall_partition`).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PinPlumbing

open Erdos634.Geometry

/-- **The pin equation.**  At any boundary point of the target that is not a target vertex, the
tiles' local angles sum to exactly `π`.  A base junction is such a point. -/
theorem pin_angle_sum {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts) :
    ∑ i, (D.tile i).localAngle p = Real.pi := by
  rw [D.sum_localAngle_eq p, D.target.localAngle_frontier hp hv]

/-- **The local-angle case split**, read off the definition: at any point, a tile's local angle is
a corner angle at one of its vertices, or `2π` (interior), or `π` (edge-interior), or `0`. -/
theorem localAngle_cases (T : Tri) (p : Plane) :
    (∃ j : Fin 3, p = T.pts j ∧
        T.localAngle p = cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) ∨
    T.localAngle p = 2 * Real.pi ∨ T.localAngle p = Real.pi ∨ T.localAngle p = 0 := by
  classical
  by_cases h : ∃ j, p = T.pts j
  · left
    exact ⟨h.choose, h.choose_spec, by rw [Tri.localAngle, dif_pos h]⟩
  · by_cases h2 : ∀ j, 0 < T.basis.coord j p
    · right; left
      rw [Tri.localAngle, dif_neg h, if_pos h2]
    · by_cases h3 : ∃ k, T.basis.coord k p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j p
      · right; right; left
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_pos h3]
      · right; right; right
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_neg h3]

/-- **No tile is interior-covering at a boundary point**: a tile whose local angle at the pin is
`2π` would make the sum exceed `π` on its own.  Stated at the sum level: if some tile contributes
`2π` and the others are nonnegative, the pin equation fails. -/
theorem no_interior_tile_at_pin {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (i : Fin N) (hi : (D.tile i).localAngle p = 2 * Real.pi) : False := by
  have hsum := pin_angle_sum D hp hv
  have hle : (D.tile i).localAngle p ≤ ∑ j, (D.tile j).localAngle p :=
    Finset.single_le_sum (fun j _ => (D.tile j).localAngle_nonneg p) (Finset.mem_univ i)
  rw [hsum, hi] at hle
  nlinarith [Real.pi_pos]

/-! ## The measure-to-length bridge, right half

`Dissection.wall_partition` partitions a wall segment's `H¹`-measure among the tile edges along
it.  Mathlib's `hausdorffMeasure_segment` evaluates the right side: the measure of a segment IS
the distance between its endpoints.  So a wall run's total edge measure equals its length, as a
one-line composition.  The left half — each `edge ∩ segment` is itself a segment whose length is
one of the model lengths or a partial thereof — is the remaining conversion, fed by
`congruent_edge_lengths`. -/

/-- **A wall segment's edge measures sum to its length.** -/
theorem wall_partition_length {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (hS : segment ℝ u₁ u₂ ⊆ {y | f y = c})
    (hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂)
      = edist u₁ u₂ := by
  rw [D.wall_partition f c hf hu hS hint hwall]
  exact MeasureTheory.hausdorffMeasure_segment u₁ u₂

/-! ## The measure-to-length bridge, left half

Each term of `wall_partition` is the measure of `edge ∩ segment` — a nonempty convex compact
subset of a segment, hence itself a segment, hence of measure the distance between its endpoints.
With `congruent_edge_lengths` bounding those endpoints to the model's edge structure, the run
equation the semigroup kills consume follows. -/

/-- **A nonempty convex compact subset of a segment is a segment.**  Parametrize the carrier
segment by `lineMap`, pull back, and apply `eq_Icc_of_connected_compact` on the line. -/
theorem convex_compact_in_segment {u₁ u₂ : Plane} {K : Set Plane}
    (hK : Convex ℝ K) (hc : IsCompact K) (hne : K.Nonempty)
    (hsub : K ⊆ segment ℝ u₁ u₂) (hu : u₁ ≠ u₂) :
    ∃ v₁ v₂ : Plane, K = segment ℝ v₁ v₂ := by
  set γ : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap u₁ u₂ with hγ
  have hinj : Function.Injective γ := AffineMap.lineMap_injective ℝ hu
  have hseg : segment ℝ u₁ u₂ = γ '' Set.Icc 0 1 := by
    rw [hγ, segment_eq_image_lineMap]
  set T : Set ℝ := γ ⁻¹' K with hT
  have hTsub : T ⊆ Set.Icc 0 1 := by
    intro t ht
    have : γ t ∈ γ '' Set.Icc 0 1 := hseg ▸ hsub ht
    obtain ⟨t', ht', he⟩ := this
    rwa [← hinj he]
  have hTconv : Convex ℝ T := hK.affine_preimage γ
  have hTcl : IsClosed T := hc.isClosed.preimage AffineMap.lineMap_continuous
  have hTcomp : IsCompact T := (isCompact_Icc).of_isClosed_subset hTcl hTsub
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have : x ∈ γ '' Set.Icc 0 1 := hseg ▸ hsub hx
    obtain ⟨t, _, he⟩ := this
    exact ⟨t, by rw [hT]; simp only [Set.mem_preimage, he]; exact hx⟩
  have hTconn : IsConnected T := ⟨hTne, hTconv.isPreconnected⟩
  have hIcc := eq_Icc_of_connected_compact hTconn hTcomp
  have hKrange : K ⊆ Set.range γ := fun x hx => by
    have : x ∈ γ '' Set.Icc 0 1 := hseg ▸ hsub hx
    exact ⟨this.choose, this.choose_spec.2⟩
  have hKT : K = γ '' T := by
    rw [hT, Set.image_preimage_eq_inter_range]
    exact (Set.inter_eq_left.mpr hKrange).symm
  have hle : sInf T ≤ sSup T := by
    obtain ⟨t, ht⟩ := hTne
    rw [hIcc] at ht
    exact le_trans ht.1 ht.2
  have himg : γ '' T = segment ℝ (γ (sInf T)) (γ (sSup T)) := by
    conv_lhs => rw [hIcc]
    rw [← segment_eq_Icc hle]
    exact image_segment ℝ γ (sInf T) (sSup T)
  exact ⟨γ (sInf T), γ (sSup T), hKT.trans himg⟩

/-- **Each wall-partition term is a distance.**  The measure of `edge ∩ segment` is `edist` of two
points (or the term vanishes when the intersection is empty). -/
theorem inter_measure_is_dist {u₁ u₂ : Plane} (hu : u₁ ≠ u₂) (T : Tri) (k : Fin 3)
    (hne : (T.edge k ∩ segment ℝ u₁ u₂).Nonempty) :
    ∃ v₁ v₂ : Plane,
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        (T.edge k ∩ segment ℝ u₁ u₂) = edist v₁ v₂ := by
  have hconv : Convex ℝ (T.edge k ∩ segment ℝ u₁ u₂) := by
    rw [Tri.edge]
    exact (convex_segment _ _).inter (convex_segment u₁ u₂)
  have hsegcomp : IsCompact (segment ℝ u₁ u₂) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hcomp : IsCompact (T.edge k ∩ segment ℝ u₁ u₂) :=
    hsegcomp.of_isClosed_subset ((T.isClosed_edge k).inter hsegcomp.isClosed)
      Set.inter_subset_right
  obtain ⟨v₁, v₂, hv⟩ := convex_compact_in_segment hconv hcomp hne
    Set.inter_subset_right hu
  exact ⟨v₁, v₂, by rw [hv]; exact MeasureTheory.hausdorffMeasure_segment v₁ v₂⟩

/-! ## The run equation: whole-edge wall runs sum to `x·a + y·b + z·c`

When every chain edge lies wholly inside the wall segment, each partition term is a full edge
length; classifying by `congruent_edge_lengths` and counting gives the `x·a + y·b + z·c = L` form
the semigroup kills consume. -/

/-- **A model tile has three edge lengths**: any pair distance is one of the three, up to
symmetry. -/
theorem model_three_lengths (T : Tri) (i i' : Fin 3) (h : i ≠ i') :
    edist (T.pts i) (T.pts i') = edist (T.pts 0) (T.pts 1) ∨
    edist (T.pts i) (T.pts i') = edist (T.pts 1) (T.pts 2) ∨
    edist (T.pts i) (T.pts i') = edist (T.pts 0) (T.pts 2) := by
  fin_cases i <;> fin_cases i' <;>
    first
      | (exfalso; exact h rfl)
      | (left; rfl)
      | (right; left; rfl)
      | (right; right; rfl)
      | (left; exact edist_comm _ _)
      | (right; left; exact edist_comm _ _)
      | (right; right; exact edist_comm _ _)

/-- **Counting a three-valued sum.**  A finite sum whose terms each equal `A`, `B`, or `C` is
`x•A + y•B + z•C` for counts `x + y + z = card`. -/
theorem sum_of_three_valued {ι : Type*} (S : Finset ι) (g : ι → ENNReal) (A B C : ENNReal)
    (h : ∀ e ∈ S, g e = A ∨ g e = B ∨ g e = C) :
    ∃ x y z : ℕ, x + y + z = S.card ∧ ∑ e ∈ S, g e = x * A + y * B + z * C := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨x, y, z, hcard, hsum⟩ := ih (fun e he => h e (Finset.mem_insert_of_mem he))
    rcases h a (Finset.mem_insert_self a s) with hA | hB | hC
    · exact ⟨x + 1, y, z, by rw [Finset.card_insert_of_notMem ha]; omega,
        by rw [Finset.sum_insert ha, hsum, hA]; push_cast; ring⟩
    · exact ⟨x, y + 1, z, by rw [Finset.card_insert_of_notMem ha]; omega,
        by rw [Finset.sum_insert ha, hsum, hB]; push_cast; ring⟩
    · exact ⟨x, y, z + 1, by rw [Finset.card_insert_of_notMem ha]; omega,
        by rw [Finset.sum_insert ha, hsum, hC]; push_cast; ring⟩

/-- **The run equation.**  If every chain edge lies wholly inside the wall segment and every tile
is congruent to the model, the run length is `x·A + y·B + z·C` in the model's three edge
lengths — the form the semigroup kills consume. -/
theorem wall_run_equation {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i))
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (hS : segment ℝ u₁ u₂ ⊆ {y | f y = c})
    (hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier)
    (hwhole : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ u₁ u₂) :
    ∃ x y z : ℕ,
      (x : ENNReal) * edist (model.pts 0) (model.pts 1)
        + y * edist (model.pts 1) (model.pts 2)
        + z * edist (model.pts 0) (model.pts 2) = edist u₁ u₂ := by
  classical
  set g : Fin N × Fin 3 → ENNReal := fun e =>
    (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
      ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂) with hg
  have hval : ∀ e ∈ D.lineChain f c,
      g e = edist (model.pts 0) (model.pts 1) ∨
      g e = edist (model.pts 1) (model.pts 2) ∨
      g e = edist (model.pts 0) (model.pts 2) := by
    intro e he
    have hinter : (D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂ = (D.tile e.1).edge e.2 :=
      Set.inter_eq_left.mpr (hwhole e he)
    have hne : e.2 ≠ e.2 + 1 := by
      intro hcontra
      have hv := congrArg Fin.val hcontra
      have hlt := (e.2).isLt
      simp [Fin.val_add] at hv
      omega
    obtain ⟨i, i', hii, hd⟩ := congruent_corner_angles_aux (hcong e.1) e.2 (e.2 + 1) hne
    have hedge : g e = edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
      rw [hg]; simp only
      rw [hinter, Tri.edge]
      exact MeasureTheory.hausdorffMeasure_segment _ _
    have hde : edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = edist (model.pts i) (model.pts i') := by
      rw [edist_dist, edist_dist, hd]
    rw [hedge, hde]
    exact model_three_lengths model i i' hii
  obtain ⟨x, y, z, _, hsum⟩ := sum_of_three_valued (D.lineChain f c) g
    (edist (model.pts 0) (model.pts 1)) (edist (model.pts 1) (model.pts 2))
    (edist (model.pts 0) (model.pts 2)) hval
  refine ⟨x, y, z, ?_⟩
  rw [← hsum]
  exact wall_partition_length D f c hf hu hS hint hwall

end Erdos634.PinPlumbing