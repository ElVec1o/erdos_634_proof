import Erdos634.ChordFinsetGeometricChainBase
import Erdos634.ChordFinsetStepCombined
import Erdos634.ChordFinsetInvariant
import Erdos634.WbtwGlobalBoundHelpers
import Erdos634.ChordFinsetReachLemma

/-!
# Building the geometric chain from a list of straddlers, in order

Erdős #634. The geometric twin of `exists_injective_chain`: given a `List` of straddler indices,
*sorted* (nearest-to-`bound` first — taken directly as a hypothesis, matching the same pattern
already used for `chord_decomposition_of_chain`'s own `hinj`, rather than re-derived), the point
sequence built by prepending each straddler's oriented trace satisfies (a strengthened form of)
`chord_decomposition_of_chain`'s `hchain`, `hpts`, `hmtrace` and `hgap` hypotheses — `hmtrace` here
gives the *specific* point identity `g (2i+1) = R (L.get i)`, `g (2i+2) = S (L.get i)`, which
trivially implies `chord_decomposition_of_chain`'s own weaker segment-equality form.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **Building the geometric chain from a sorted list of straddlers.** -/
theorem exists_geometric_chain {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q : Plane} (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (R S : Fin N → Plane)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧ R k ≠ S k ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k)) :
    ∀ (L : List (Fin N)), L.Nodup → ∀ (bound : Plane), Wbtw ℝ P bound Q →
      (∀ k ∈ L, (∃ a, f ((D.tile k).pts a) < c) ∧ (∃ b, c < f ((D.tile k).pts b))) →
      (∀ k ∈ L, Wbtw ℝ P bound (R k)) →
      (∀ k ∈ L, bound ≠ R k) →
      (∀ i j, (hi : i < L.length) → (hj : j < L.length) → i ≤ j →
        Wbtw ℝ P (R (L.get ⟨i, hi⟩)) (R (L.get ⟨j, hj⟩))) →
      (L.Pairwise (fun k l => k ≠ l →
        (segment ℝ (R k) (S k) ∩ segment ℝ (R l) (S l)).Subsingleton)) →
      (L.Pairwise (fun k l => R k ≠ R l ∧ R k ≠ S l ∧ S k ≠ R l ∧ S k ≠ S l)) →
      (∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
        k ∉ L → Wbtw ℝ P (S k) bound) →
      ∃ g : ℕ → Plane, g 0 = bound ∧
        (∀ i, i + 2 ≤ 2 * L.length → Wbtw ℝ (g i) (g (i + 1)) (g (i + 2))) ∧
        (∀ i, i ≤ 2 * L.length → g i ∈ D.target.carrier ∩ {x | f x = c}) ∧
        (∀ i (h : i < L.length),
          g (2 * i + 1) = R (L.get ⟨i, h⟩) ∧ g (2 * i + 2) = S (L.get ⟨i, h⟩)) ∧
        (∀ i, i ≤ L.length → ∀ k : Fin N, ∀ y ∈ openSegment ℝ (g (2 * i)) (g (2 * i + 1)),
          y ∉ interior (D.tile k).carrier) := by
  intro L
  induction L with
  | nil =>
    intro _ bound hPb _ _ _ _ _ _ hexcl
    refine ⟨fun _ => bound, rfl,
      by intro i hi; simp only [List.length_nil] at hi; omega, ?_, ?_, ?_⟩
    · intro i hi
      simp only [List.length_nil, Nat.mul_zero] at hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      rw [hi0, hPQ]; exact mem_segment_iff_wbtw.mpr hPb
    · intro i h; exact absurd h (by simp)
    · intro i hi k y hy
      have hi0 : i = 0 := Nat.le_zero.mp hi
      rw [hi0] at hy
      simp only at hy
      rw [openSegment_same, Set.mem_singleton_iff] at hy
      rw [hy]
      intro hyint
      have hbfc : f bound = c := by
        have hbmem : bound ∈ D.target.carrier ∩ {x | f x = c} := by
          rw [hPQ]; exact mem_segment_iff_wbtw.mpr hPb
        exact hbmem.2
      exact not_interior_of_all_excluded D f hf c R S hglobal
        (fun k hka hkb => hexcl k hka hkb (by simp)) hbfc k hyint
  | cons m L' ih =>
    intro hnodup bound hPb hmem hle hbne hsorted hpairwise hptdist hexcl
    have hmemm : m ∈ m :: L' := List.mem_cons_self ..
    obtain ⟨hgom, hnem, hmtrace⟩ := hglobal m (hmem m hmemm).1 (hmem m hmemm).2
    have hle_m : Wbtw ℝ P bound (R m) := hle m hmemm
    rw [List.pairwise_cons] at hpairwise
    obtain ⟨hcross, hpairwise'⟩ := hpairwise
    rw [List.pairwise_cons] at hptdist
    obtain ⟨hptcross, hptdist'⟩ := hptdist
    have hbne' : ∀ k ∈ L', S m ≠ R k := fun k hk => (hptcross k hk).2.2.1
    rw [List.nodup_cons] at hnodup
    obtain ⟨hmnotin, hnodup'⟩ := hnodup
    have hmem' : ∀ k ∈ L', (∃ a, f ((D.tile k).pts a) < c) ∧ (∃ b, c < f ((D.tile k).pts b)) :=
      fun k hk => hmem k (List.mem_cons_of_mem m hk)
    have hmnek : ∀ k ∈ L', m ≠ k := fun k hk h => hmnotin (h ▸ hk)
    have hle' : ∀ k ∈ L', Wbtw ℝ P (S m) (R k) := by
      intro k hk
      obtain ⟨hgoK, hneK, hktrace⟩ := hglobal k (hmem' k hk).1 (hmem' k hk).2
      have hmRQ := wbtw_near_endpoint_to_Q D f c hPQ R S m hmtrace
      have hmSQ := wbtw_far_endpoint_to_Q D f c hPQ R S m hmtrace
      have hkRQ := wbtw_near_endpoint_to_Q D f c hPQ R S k hktrace
      have hkSQ := wbtw_far_endpoint_to_Q D f c hPQ R S k hktrace
      have hmink : Wbtw ℝ P (R m) (R k) := by
        obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hk
        have hj' : j + 1 < (m :: L').length := by simpa using hj
        have hget : (m :: L').get ⟨j + 1, hj'⟩ = k := by simpa using hjeq
        have hi0 : (0 : ℕ) < (m :: L').length := by simp
        have hgetm : (m :: L').get ⟨0, hi0⟩ = m := rfl
        have := hsorted 0 (j + 1) hi0 hj' (by omega)
        rwa [hgetm, hget] at this
      exact far_precedes_of_minimal hmRQ hmSQ hkRQ hkSQ hnem hneK hgom hgoK
        (hcross k hk (hmnek k hk)) hmink
    have hexcl' : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
        k ∉ L' → Wbtw ℝ P (S k) (S m) := by
      intro k hka hkb hknotin
      by_cases hkm : k = m
      · subst hkm; exact excl_new_self
      · exact excl_carries_forward
          (hexcl k hka hkb (fun h => (List.mem_cons.mp h).elim hkm hknotin)) hle_m hgom
    have hsorted' : ∀ i j, (hi : i < L'.length) → (hj : j < L'.length) → i ≤ j →
        Wbtw ℝ P (R (L'.get ⟨i, hi⟩)) (R (L'.get ⟨j, hj⟩)) := by
      intro i j hi hj hij
      have hi' : i + 1 < (m :: L').length := by simpa using hi
      have hj' : j + 1 < (m :: L').length := by simpa using hj
      have hgeti : (m :: L').get ⟨i + 1, hi'⟩ = L'.get ⟨i, hi⟩ := by simp
      have hgetj : (m :: L').get ⟨j + 1, hj'⟩ = L'.get ⟨j, hj⟩ := by simp
      have := hsorted (i + 1) (j + 1) hi' hj' (by omega)
      rwa [hgeti, hgetj] at this
    have hmSQ : Wbtw ℝ P (S m) Q := wbtw_far_endpoint_to_Q D f c hPQ R S m hmtrace
    obtain ⟨g', hg'0, hg'chain, hg'pts, hg'match, hg'gap⟩ :=
      ih hnodup' (S m) hmSQ hmem' hle' hbne' hsorted' hpairwise' hptdist' hexcl'
    have hgo' : ∀ k ∈ L', Wbtw ℝ P (R k) (S k) :=
      fun k hk => (hglobal k (hmem' k hk).1 (hmem' k hk).2).1
    have hreach : ∀ i, i ≤ 2 * L'.length → Wbtw ℝ P (S m) (g' i) :=
      reach_of_le_all hg'0 hg'match hgo' hle'
    set g : ℕ → Plane := fun i => if i = 0 then bound else if i = 1 then R m else g' (i - 2)
      with hgdef
    have hg0 : g 0 = bound := by simp [hgdef]
    have hg1 : g 1 = R m := by simp [hgdef]
    have hgshift : ∀ i, g (i + 2) = g' i := by intro i; simp [hgdef]
    refine ⟨g, hg0, ?_, ?_, ?_, ?_⟩
    · -- hchain
      intro i hi
      rcases Nat.lt_or_ge i 2 with hi2 | hi2
      · interval_cases i
        · rw [hg0, hg1, hgshift 0, hg'0]
          exact wbtw_middle_of_wbtw_wbtw hle_m hgom
        · rw [hg1, hgshift 0, hgshift 1, hg'0]
          refine wbtw_middle_of_wbtw_wbtw hgom (hreach 1 ?_)
          simp only [List.length_cons] at hi
          omega
      · obtain ⟨n, hn⟩ : ∃ n, i = n + 2 := ⟨i - 2, by omega⟩
        rw [hn, hgshift n, show n + 2 + 1 = (n + 1) + 2 from by ring, hgshift (n + 1),
          show n + 2 + 2 = (n + 2) + 2 from rfl, hgshift (n + 2)]
        apply hg'chain n
        simp only [List.length_cons] at hi
        omega
    · -- hpts
      intro i hi
      rcases Nat.lt_or_ge i 2 with hi2 | hi2
      · interval_cases i
        · rw [hg0, hPQ]; exact mem_segment_iff_wbtw.mpr hPb
        · rw [hg1, hPQ]
          exact mem_segment_iff_wbtw.mpr (wbtw_near_endpoint_to_Q D f c hPQ R S m hmtrace)
      · obtain ⟨n, hn⟩ : ∃ n, i = n + 2 := ⟨i - 2, by omega⟩
        rw [hn, hgshift n]
        apply hg'pts n
        simp only [List.length_cons] at hi
        omega
    · -- hmtrace (point identity)
      intro i h
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        refine ⟨hg1, ?_⟩
        show g (0 + 2) = S ((m :: L').get ⟨0, h⟩)
        rw [hgshift 0, hg'0]
        rfl
      · obtain ⟨n, hn⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
        subst hn
        simp only [List.length_cons] at h
        have hnlt : n < L'.length := by omega
        have hget : (m :: L').get ⟨n + 1, h⟩ = L'.get ⟨n, hnlt⟩ := by simp
        rw [hget, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring,
          show 2 * (n + 1) + 2 = (2 * n + 2) + 2 from by ring,
          hgshift (2 * n + 1), hgshift (2 * n + 2)]
        exact hg'match n hnlt
    · -- hgap
      intro i hi k y hy
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · rw [hi0, hg0, hg1] at hy
        refine gap_free_of_finset_step' D f hf c hPQ R S (m :: L').toFinset (hbne m hmemm) hgom
          (wbtw_middle_of_wbtw_wbtw hle_m hgom) hle_m hmtrace
          (fun k' hka hkb => ⟨(hglobal k' hka hkb).1, (hglobal k' hka hkb).2.2⟩) ?_ ?_ k y hy
        · intro k' hk' hka hkb
          by_cases hkm' : k' = m
          · subst hkm'; exact le_refl _
          · have hRmRk' : Wbtw ℝ P (R m) (R k') :=
              wbtw_of_wbtw_wbtw hgom
                (hle' k' ((List.mem_cons.mp (List.mem_toFinset.mp hk')).resolve_left hkm'))
            have heq : dist P (R m) + dist (R m) (R k') = dist P (R k') :=
              dist_add_dist_eq_iff.mpr hRmRk'
            linarith [dist_nonneg (x := R m) (y := R k')]
        · intro k' hka hkb hk'
          exact hexcl k' hka hkb (fun h => hk' (List.mem_toFinset.mpr h))
      · obtain ⟨n, hn⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
        have e1 : g (2 * i) = g' (2 * n) := by
          rw [hn, show 2 * (n + 1) = 2 * n + 2 from by ring]; exact hgshift (2 * n)
        have e2 : g (2 * i + 1) = g' (2 * n + 1) := by
          rw [hn, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring]; exact hgshift (2 * n + 1)
        rw [e1, e2] at hy
        have hgapstep : n ≤ L'.length := by
          rw [hn] at hi
          simp only [List.length_cons] at hi
          omega
        exact hg'gap n hgapstep k y hy

end Erdos634.ChordTraceReal
