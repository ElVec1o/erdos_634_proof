import Erdos634.WbtwChain

/-!
# The reach lemma `exists_geometric_chain`'s final assembly needs

Erdős #634. The one new fact identified in `PAPER_MAP.md` as missing for
`exists_geometric_chain`'s successor case: given a sequence `g'` built from a list `L'` (via
`exists_injective_chain`/`exists_geometric_chain`'s own shape), and that a fixed point `bound'`
weakly precedes every element of `L'`'s own near endpoint, `bound'` weakly precedes *every* point of
`g'`'s own range, not just the near endpoints. Proved by cases on whether the index is even or odd,
using `wbtw_of_wbtw_wbtw` to reach the far endpoint from the near one.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry

namespace Erdos634.ChordTraceReal

/-- **The reach lemma.** -/
theorem reach_of_le_all {N : ℕ} {P bound' : Plane} {R S : Fin N → Plane} {L' : List (Fin N)}
    {g' : ℕ → Plane}
    (hg'0 : g' 0 = bound')
    (hg'match : ∀ i (h : i < L'.length),
      g' (2 * i + 1) = R (L'.get ⟨i, h⟩) ∧ g' (2 * i + 2) = S (L'.get ⟨i, h⟩))
    (hgo : ∀ k ∈ L', Wbtw ℝ P (R k) (S k))
    (hle' : ∀ k ∈ L', Wbtw ℝ P bound' (R k)) :
    ∀ i, i ≤ 2 * L'.length → Wbtw ℝ P bound' (g' i) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · rw [h0, hg'0]; exact wbtw_self_right ℝ P bound'
  · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
    · have heq : i = 2 * k + 1 := by omega
      have hklt : k < L'.length := by omega
      rw [heq, (hg'match k hklt).1]
      exact hle' (L'.get ⟨k, hklt⟩) (List.get_mem L' ⟨k, hklt⟩)
    · have heq : i = 2 * k + 2 := by omega
      have hklt : k < L'.length := by omega
      rw [heq, (hg'match k hklt).2]
      exact wbtw_of_wbtw_wbtw (hle' (L'.get ⟨k, hklt⟩) (List.get_mem L' ⟨k, hklt⟩))
        (hgo (L'.get ⟨k, hklt⟩) (List.get_mem L' ⟨k, hklt⟩))

end Erdos634.ChordTraceReal
