import Mathlib.Tactic

/-!
# No `BG → GB` anywhere *is* monotonicity

`MarchRun.junction_cases` shows that at every straight-edge junction of a boundary run the pair of
orientations is not `(γ, γ)` — that is, a `BG` tile is never immediately followed by a `GB` one.
This file records the combinatorial step that turns that local fact into
`prop:orientmono`'s global conclusion, and it is short: a word in which `BG` is never followed by
`GB` **is** `GB^j BG^(L-j)`.

Write the orientation of the `i`-th tile as a `Bool`, `true` for `BG`.  "No `BG` then `GB`" says
`w i = true → w (i+1) = true`, so `w` is monotone along the run; a monotone `Bool` word is a block of
`false`s then a block of `true`s, and has at most one transition.  That is exactly
"at most one junction of the run carries the figure `{3α,2β}`, and it is the transition".

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchMonotone

variable {L : ℕ} (w : ℕ → Bool)

/-- **Local ⟹ global.**  If `BG` is never immediately followed by `GB`, then once the word is `BG`
it stays `BG`. -/
theorem mono_of_no_step (h : ∀ i, i + 1 < L → w i = true → w (i + 1) = true) :
    ∀ i j, i ≤ j → j < L → w i = true → w j = true := by
  intro i j hij hjL hi
  induction j with
  | zero =>
    have : i = 0 := by omega
    exact this ▸ hi
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · have hik : i ≤ k := by omega
      exact h k (by omega) (ih hik (by omega))
    · have hik : i = k + 1 := by omega
      exact hik ▸ hi

/-- **The word is `GB^j BG^(L-j)`.**  Take `j` to be the first index carrying `BG`, or `L` if there
is none: every index below `j` is `GB`, and every index from `j` on is `BG` by monotonicity. -/
theorem block_form (h : ∀ i, i + 1 < L → w i = true → w (i + 1) = true) :
    ∃ j : ℕ, (∀ i, i < j → i < L → w i = false) ∧ (∀ i, j ≤ i → i < L → w i = true) := by
  classical
  by_cases hex : ∃ i, i < L ∧ w i = true
  · refine ⟨Nat.find hex, ?_, ?_⟩
    · intro i hij hiL
      by_contra hc
      have ht : w i = true := by
        cases hw : w i with
        | false => exact absurd hw hc
        | true => rfl
      have hle : Nat.find hex ≤ i := Nat.find_le (⟨hiL, ht⟩ : i < L ∧ w i = true)
      omega
    · intro i hji hiL
      obtain ⟨hjL, hjt⟩ := Nat.find_spec hex
      exact mono_of_no_step w h _ _ hji hiL hjt
  · refine ⟨L, ?_, ?_⟩
    · intro i _ hiL
      cases hw : w i with
      | false => rfl
      | true => exact absurd (⟨i, hiL, hw⟩ : ∃ i, i < L ∧ w i = true) hex
    · intro i hji hiL; omega

/-- **At most one transition.**  In block form the only index where the orientation changes is `j`
itself, so the run carries at most one `BG → GB`-free transition point. -/
theorem at_most_one_transition
    (h : ∀ i, i + 1 < L → w i = true → w (i + 1) = true) :
    ∃ j : ℕ, ∀ i, i + 1 < L → w i ≠ w (i + 1) → i + 1 = j := by
  obtain ⟨j, hlow, hhigh⟩ := block_form w h
  refine ⟨j, ?_⟩
  intro i hi hne
  by_contra hij
  rcases Nat.lt_or_ge i j with hlt | hge
  · rcases Nat.lt_or_ge (i + 1) j with hlt2 | hge2
    · exact hne ((hlow i hlt (by omega)).trans (hlow (i+1) hlt2 (by omega)).symm)
    · omega
  · exact hne ((hhigh i hge (by omega)).trans (hhigh (i+1) (by omega) (by omega)).symm)

end Erdos634.MarchMonotone
