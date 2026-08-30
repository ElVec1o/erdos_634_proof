import Mathlib
import Erdos634.ShadowCover

/-!
# The chain, enumerated in order

Erdős #634, bridge (c), the ordering.  `ShadowCover` covers the base's shadow by the wall edges'
shadows, as a union over a *set*.  `ChainInstance.consecutive_edges_meet` wants an *enumeration*
sorted by `edgePos`.  Sorting supplies it: this file produces, for any list of edges, an
enumeration monotone in the key and hitting every member, which is all the ordering the chain
needs.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ChainEnum

open List

/-- **Sorting gives a monotone enumeration.**  For any list and any real key there is an
enumeration of its entries, of the same length, nondecreasing in the key, and hitting every entry
of the list. -/
theorem exists_sorted_enum {ι : Type*} [Inhabited ι] (l : List ι) (pos : ι → ℝ) :
    ∃ E : ℕ → ι,
      (∀ i j, i ≤ j → j < l.length → pos (E i) ≤ pos (E j)) ∧
      (∀ i < l.length, E i ∈ l) ∧
      (∀ x ∈ l, ∃ i < l.length, E i = x) := by
  classical
  set L := l.mergeSort (fun a b => decide (pos a ≤ pos b)) with hL
  have hperm : L.Perm l := List.mergeSort_perm l _
  have hlen : L.length = l.length := hperm.length_eq
  have hp : List.Pairwise (fun a b => (decide (pos a ≤ pos b)) = true) L :=
    List.sorted_mergeSort (by intro a b c hab hbc; simp_all; linarith)
      (by intro a b; simp; rcases le_total (pos a) (pos b) with h | h <;> simp [h]) l
  have hs : L.Pairwise (fun a b => pos a ≤ pos b) := hp.imp (by intro a b h; simpa using h)
  refine ⟨fun i => L.getD i default, ?_, ?_, ?_⟩
  · intro i j hij hj
    simp only
    rw [← hlen] at hj
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_refl _
    · have hi : i < L.length := lt_trans hlt hj
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      exact List.pairwise_iff_getElem.mp hs i j hi hj hlt
  · intro i hi
    simp only
    rw [← hlen] at hi
    rw [List.getD_eq_getElem _ _ hi]
    exact hperm.mem_iff.mp (List.getElem_mem hi)
  · intro x hx
    obtain ⟨i, hi, hix⟩ : ∃ i, ∃ h : i < L.length, L[i] = x := by
      have : x ∈ L := hperm.mem_iff.mpr hx
      obtain ⟨i, hi, h⟩ := List.getElem_of_mem this
      exact ⟨i, hi, h⟩
    refine ⟨i, by rwa [hlen] at hi, ?_⟩
    simp only
    rw [List.getD_eq_getElem _ _ hi]; exact hix

end Erdos634.ChainEnum
