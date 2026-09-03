import Erdos634.ChordFinsetPrependInj

/-!
# Building an injective chain from a list of pairwise-nondegenerate pairs

Erdős #634. The pure combinatorial fact `exists_chain_of_finset` needs beyond
`injective_prepend_two`: given a `List` of point-pairs, each internally nondegenerate, pairwise
cross-distinct from each other, and distinct from a fixed bound point, the point sequence built by
concatenating `bound :: pair₁.1 :: pair₁.2 :: pair₂.1 :: pair₂.2 :: ⋯` is injective on its own
range. Proved by induction on the list, using `injective_prepend_two` once per element.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ChordTraceReal

variable {Plane : Type*}

/-- **Building an injective chain from a list of pairwise-nondegenerate pairs.** -/
theorem exists_injective_chain :
    ∀ (L : List (Plane × Plane)) (bound : Plane),
      (∀ pr ∈ L, pr.1 ≠ pr.2) →
      (∀ pr ∈ L, bound ≠ pr.1 ∧ bound ≠ pr.2) →
      (L.Pairwise (fun pr1 pr2 => pr1.1 ≠ pr2.1 ∧ pr1.1 ≠ pr2.2 ∧ pr1.2 ≠ pr2.1 ∧ pr1.2 ≠ pr2.2)) →
      ∃ g : ℕ → Plane, g 0 = bound ∧
        (∀ a b, a ≤ 2 * L.length → b ≤ 2 * L.length → a ≠ b → g a ≠ g b) ∧
        ∀ i (h : i < L.length), g (2 * i + 1) = (L.get ⟨i, h⟩).1 ∧
          g (2 * i + 2) = (L.get ⟨i, h⟩).2 := by
  intro L
  induction L with
  | nil =>
    intro bound _ _ _
    refine ⟨fun _ => bound, rfl, ?_, ?_⟩
    · intro a b ha hb hab
      simp only [List.length_nil, Nat.mul_zero] at ha hb
      omega
    · intro i h
      exact absurd h (by simp)
  | cons pr L' ih =>
    intro bound hself hbound hpairwise
    obtain ⟨hpself, hL'self⟩ : pr.1 ≠ pr.2 ∧ ∀ p' ∈ L', p'.1 ≠ p'.2 :=
      ⟨hself pr (List.mem_cons_self ..), fun p' hp' => hself p' (List.mem_cons_of_mem pr hp')⟩
    rw [List.pairwise_cons] at hpairwise
    obtain ⟨hcross, hpairwise'⟩ := hpairwise
    obtain ⟨g', hg'0, hg'inj, hg'match⟩ := ih pr.2
      hL'self
      (fun p' hp' => ⟨(hcross p' hp').2.2.1, (hcross p' hp').2.2.2⟩)
      hpairwise'
    have hp_old : ∀ i, i ≤ 2 * L'.length → bound ≠ g' i := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0, hg'0]; exact (hbound pr (List.mem_cons_self ..)).2
      · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
        · have hjlt : k < L'.length := by omega
          have hmatch := (hg'match k hjlt).1
          have heq : i = 2 * k + 1 := by omega
          rw [heq, hmatch]
          exact (hbound (L'.get ⟨k, hjlt⟩)
            (List.mem_cons_of_mem pr (List.get_mem L' ⟨k, hjlt⟩))).1
        · have hjlt : k < L'.length := by omega
          have hmatch := (hg'match k hjlt).2
          have heq : i = 2 * k + 2 := by omega
          rw [heq, hmatch]
          exact (hbound (L'.get ⟨k, hjlt⟩)
            (List.mem_cons_of_mem pr (List.get_mem L' ⟨k, hjlt⟩))).2
    have hr_old : ∀ i, i ≤ 2 * L'.length → pr.1 ≠ g' i := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0, hg'0]; exact hpself
      · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
        · have hjlt : k < L'.length := by omega
          have hmatch := (hg'match k hjlt).1
          have heq : i = 2 * k + 1 := by omega
          rw [heq, hmatch]
          exact (hcross (L'.get ⟨k, hjlt⟩) (List.get_mem L' ⟨k, hjlt⟩)).1
        · have hjlt : k < L'.length := by omega
          have hmatch := (hg'match k hjlt).2
          have heq : i = 2 * k + 2 := by omega
          rw [heq, hmatch]
          exact (hcross (L'.get ⟨k, hjlt⟩) (List.get_mem L' ⟨k, hjlt⟩)).2.1
    refine ⟨fun i => if i = 0 then bound else if i = 1 then pr.1 else g' (i - 2), rfl, ?_, ?_⟩
    · simpa [List.length_cons, show 2 * (L'.length + 1) = 2 * L'.length + 2 from by ring] using
        injective_prepend_two hg'inj (hbound pr (List.mem_cons_self ..)).1 hp_old hr_old
    · intro i h
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp [hg'0]
      · obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hklt : k < L'.length := by simpa [hk, List.length_cons] using h
        have hgetk : (pr :: L').get ⟨i, h⟩ = L'.get ⟨k, hklt⟩ := by
          simp [hk]
        rw [hgetk]
        have e1 : 2 * i + 1 ≠ 0 := by omega
        have e2 : 2 * i + 1 ≠ 1 := by omega
        have e3 : 2 * i + 2 ≠ 0 := by omega
        have e4 : 2 * i + 2 ≠ 1 := by omega
        simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4]
        constructor
        · have : 2 * i + 1 - 2 = 2 * k + 1 := by omega
          rw [this]; exact (hg'match k hklt).1
        · have : 2 * i + 2 - 2 = 2 * k + 2 := by omega
          rw [this]; exact (hg'match k hklt).2

end Erdos634.ChordTraceReal
