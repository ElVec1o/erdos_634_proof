import Erdos634.ChordFinsetGeometricChain
import Erdos634.FinsetSortedList
import Erdos634.WbtwDistCoord

/-!
# The top-level wiring: from a straddler `Finset` to the geometric chain

Erdős #634. Combines `exists_sorted_list_of_finset` (sort the straddler set by `dist P (R ·)`) with
`exists_geometric_chain` (build the point sequence from a sorted list), discharging
`exists_geometric_chain`'s own hypotheses from the sort's guarantees plus the straddler set's own
general-position facts.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **From a straddler `Finset` to the geometric chain.** -/
theorem exists_geometric_chain_of_finset {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q : Plane} (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (R S : Fin N → Plane)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧ R k ≠ S k ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k))
    (T : Finset (Fin N)) (bound : Plane) (hPb : Wbtw ℝ P bound Q)
    (hmem : ∀ k ∈ T, (∃ a, f ((D.tile k).pts a) < c) ∧ (∃ b, c < f ((D.tile k).pts b)))
    (hle : ∀ k ∈ T, Wbtw ℝ P bound (R k)) (hbne : ∀ k ∈ T, bound ≠ R k)
    (hcross : ∀ k ∈ T, ∀ l ∈ T, k ≠ l →
      (segment ℝ (R k) (S k) ∩ segment ℝ (R l) (S l)).Subsingleton)
    (hptcross : ∀ k ∈ T, ∀ l ∈ T, k ≠ l →
      R k ≠ R l ∧ R k ≠ S l ∧ S k ≠ R l ∧ S k ≠ S l)
    (hexcl : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      k ∉ T → Wbtw ℝ P (S k) bound) :
    ∃ g : ℕ → Plane, g 0 = bound ∧
      (∀ i, i + 2 ≤ 2 * T.card → Wbtw ℝ (g i) (g (i + 1)) (g (i + 2))) ∧
      (∀ i, i ≤ 2 * T.card → g i ∈ D.target.carrier ∩ {x | f x = c}) ∧
      (∀ i, i < T.card → ∃ t : Fin N,
        (D.tile t).carrier ∩ {x | f x = c} = segment ℝ (g (2 * i + 1)) (g (2 * i + 2))) ∧
      (∀ i, i ≤ T.card → ∀ k : Fin N, ∀ y ∈ openSegment ℝ (g (2 * i)) (g (2 * i + 1)),
        y ∉ interior (D.tile k).carrier) := by
  obtain ⟨L, hLset, hLnodup, hLlen, hLsorted⟩ :=
    exists_sorted_list_of_finset (fun k => dist P (R k)) T
  have hLmem : ∀ k ∈ L, k ∈ T := fun k hk => hLset ▸ List.mem_toFinset.mpr hk
  obtain ⟨g, hg0, hgchain, hgpts, hgmatch, hggap⟩ :=
    exists_geometric_chain D f hf c hPQ R S hglobal L hLnodup bound hPb
      (fun k hk => hmem k (hLmem k hk)) (fun k hk => hle k (hLmem k hk))
      (fun k hk => hbne k (hLmem k hk))
      (fun i j hi hj hij => by
        have hik : L.get ⟨i, hi⟩ ∈ T := hLmem _ (List.get_mem L ⟨i, hi⟩)
        have hjk : L.get ⟨j, hj⟩ ∈ T := hLmem _ (List.get_mem L ⟨j, hj⟩)
        have hiQ : Wbtw ℝ P (R (L.get ⟨i, hi⟩)) Q :=
          wbtw_near_endpoint_to_Q D f c hPQ R S _ (hglobal _ (hmem _ hik).1 (hmem _ hik).2).2.2
        have hjQ : Wbtw ℝ P (R (L.get ⟨j, hj⟩)) Q :=
          wbtw_near_endpoint_to_Q D f c hPQ R S _ (hglobal _ (hmem _ hjk).1 (hmem _ hjk).2).2.2
        exact (wbtw_iff_dist_le_of_wbtw hiQ hjQ).mpr (hLsorted i j hi hj hij))
      (List.pairwise_iff_get.mpr (fun i j hij => fun h => hcross _ (hLmem _ (List.get_mem L i))
        _ (hLmem _ (List.get_mem L j)) (fun heq => hij.ne (by
          have := List.Nodup.get_inj_iff hLnodup (i := i) (j := j); exact this.mp heq))))
      (List.pairwise_iff_get.mpr (fun i j hij => hptcross _ (hLmem _ (List.get_mem L i))
        _ (hLmem _ (List.get_mem L j)) (fun heq => hij.ne (by
          have := List.Nodup.get_inj_iff hLnodup (i := i) (j := j); exact this.mp heq))))
      (fun k hka hkb hkL => hexcl k hka hkb
        (fun hT => hkL (List.mem_toFinset.mp (hLset.symm ▸ hT))))
  refine ⟨g, hg0, by rwa [hLlen] at hgchain, by rwa [hLlen] at hgpts, ?_, ?_⟩
  · intro i hi
    have hilt : i < L.length := by omega
    set k := L.get ⟨i, hilt⟩ with hk
    have hkT : k ∈ T := hLmem k (List.get_mem L ⟨i, hilt⟩)
    have htrace := (hglobal k (hmem k hkT).1 (hmem k hkT).2).2.2
    refine ⟨k, ?_⟩
    rw [(hgmatch i hilt).1, (hgmatch i hilt).2]
    exact htrace
  · rwa [hLlen] at hggap

end Erdos634.ChordTraceReal
