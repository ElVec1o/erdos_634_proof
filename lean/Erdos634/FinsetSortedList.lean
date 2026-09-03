import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

/-!
# Sorting a `Finset` into a `List`, by a real-valued key

Erdős #634. The pure order-theoretic fact `exists_geometric_chain` needs a `List` for: any
`Finset (Fin N)` can be sorted into a `List` (matching the `Finset` as a set, `Nodup`, same
length) whose elements are non-decreasing in an arbitrary real-valued key — by strong induction on
the `Finset`, repeatedly extracting the minimal remaining element via `Finset.exists_min_image` and
prepending it. No geometry: this is exactly the mechanical step
`ChordFinsetChainInj`/`ChordFinsetGeometricChain`'s own `List`-based machinery has been waiting for.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ChordTraceReal

/-- **Sorting a `Finset` into a `List`, by a real-valued key.** -/
theorem exists_sorted_list_of_finset {N : ℕ} (key : Fin N → ℝ) :
    ∀ T : Finset (Fin N), ∃ L : List (Fin N),
      L.toFinset = T ∧ L.Nodup ∧ L.length = T.card ∧
      (∀ i j, (hi : i < L.length) → (hj : j < L.length) → i ≤ j →
        key (L.get ⟨i, hi⟩) ≤ key (L.get ⟨j, hj⟩)) := by
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · exact ⟨[], by simp, by simp, by simp, by simp⟩
    · obtain ⟨m, hmT, hmmin⟩ := T.exists_min_image key hTne
      obtain ⟨L', hL'set, hL'nodup, hL'len, hL'sorted⟩ := ih (T.erase m) (Finset.erase_ssubset hmT)
      refine ⟨m :: L', ?_, ?_, ?_, ?_⟩
      · rw [List.toFinset_cons, hL'set, Finset.insert_erase hmT]
      · rw [List.nodup_cons]
        refine ⟨?_, hL'nodup⟩
        intro hmL'
        have : m ∈ T.erase m := hL'set ▸ List.mem_toFinset.mpr hmL'
        exact (Finset.mem_erase.mp this).1 rfl
      · rw [List.length_cons, hL'len, Finset.card_erase_of_mem hmT]
        have : 0 < T.card := Finset.card_pos.mpr hTne
        omega
      · intro i j hi hj hij
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · subst hi0
          have hgetm : (m :: L').get ⟨0, hi⟩ = m := rfl
          rw [hgetm]
          rcases Nat.eq_zero_or_pos j with hj0 | hjpos
          · subst hj0; rw [hgetm]
          · obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            have hj'lt : j' < L'.length := by
              simp only [List.length_cons] at hj; omega
            have hget : (m :: L').get ⟨j, hj⟩ = L'.get ⟨j', hj'lt⟩ := by simp [hj']
            rw [hget]
            have hmemL' : L'.get ⟨j', hj'lt⟩ ∈ T.erase m :=
              hL'set ▸ List.mem_toFinset.mpr (List.get_mem L' ⟨j', hj'lt⟩)
            exact hmmin _ (Finset.mem_of_mem_erase hmemL')
        · obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          have hi'lt : i' < L'.length := by simp only [List.length_cons] at hi; omega
          have hj'lt : j' < L'.length := by simp only [List.length_cons] at hj; omega
          have hgeti : (m :: L').get ⟨i, hi⟩ = L'.get ⟨i', hi'lt⟩ := by simp [hi']
          have hgetj : (m :: L').get ⟨j, hj⟩ = L'.get ⟨j', hj'lt⟩ := by simp [hj']
          rw [hgeti, hgetj]
          exact hL'sorted i' j' hi'lt hj'lt (by omega)

end Erdos634.ChordTraceReal
