import Mathlib.Tactic
import Erdos634.V1Gaps
import Erdos634.MarchJunctions

/-!
# The `V₁` repair's assembly: the boundary kill and the `e = 2` count

Erdős #634, the `e ≥ 2` column `(0,e,2e)`.  `V1Gaps` holds the three arithmetic kills of the
repair (`N1`, `N2`, `N3`).  This file formalises the two *combinatorial* steps that turn them
into the claimed consequence, and — equally important — records exactly where that consequence
stops.

* `two_gamma_boundary_kill` — the reflected-partner case dies at the far tip `W`: `W` is a
  boundary point, so its angle budget is `π`, while the two tiles meeting there present
  `γ` each, and `2γ = π + α > π`.
* `e2_counting_kill` — at `e = 2` the column word has `3e = 6` letters of which only `2e = 4`
  are `c`; the west chain forces the first three and its mirror the last three, hence all six,
  contradicting the letter count.
* `e3_count_survives` — the same forcing at `e = 3` leaves the word `c³b³c³` consistent: six
  forced `c`s among nine letters with six available.  **The counting kill is special to `e = 2`**,
  and the file says so rather than letting the reader assume it generalises.

The geometric hypotheses these consume — that the west chain forces three `c`s and that the
mirror argument transports — are the repair's proof-sketch content and are *hypotheses* here,
not conclusions smuggled in: `e2_counting_kill` takes the forcing as input and derives only the
count.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.V1Assembly

/-- **The far-tip kill.**  At the boundary point `W` the budget is `π`; two `γ`-corners there
sum to `2γ = π + α`, which exceeds it. -/
theorem two_gamma_boundary_kill (a b g p : ℝ) (ha : 0 < a)
    (hg : g = 2 * a + b) (hp : p = 3 * a + 2 * b) (hfit : 2 * g ≤ p) : False := by
  rw [hg, hp] at hfit; linarith

/-- **The `e = 2` count.**  Six letters, four of them `c`; if all six are forced to `c` the count
is contradicted. -/
theorem e2_counting_kill (w : Fin 6 → Bool)
    (hcount : (Finset.univ.filter fun i => w i = true).card = 4)
    (hforced : ∀ i : Fin 6, w i = true) : False := by
  have : (Finset.univ.filter fun i => w i = true) = Finset.univ := by
    ext i; simp [hforced i]
  rw [this] at hcount
  simp at hcount

/-- **Why it is special to `e = 2`.**  At `e = 3` the word has nine letters and six `c`s; the same
three-from-each-end forcing leaves the middle three free, and `c³b³c³` meets every count.  So no
contradiction arises, and the `V₂` step — whose anchors are interior, not boundary — is the
genuine residue. -/
theorem e3_count_survives :
    ∃ w : Fin 9 → Bool,
      (Finset.univ.filter fun i => w i = true).card = 6 ∧
      (∀ i : Fin 9, i.val < 3 → w i = true) ∧
      (∀ i : Fin 9, 6 ≤ i.val → w i = true) := by
  refine ⟨fun i => decide (i.val < 3 ∨ 6 ≤ i.val), ?_, ?_, ?_⟩
  · decide
  · intro i hi; simp [hi]
  · intro i hi; simp [hi]

/-- **The letter budget, stated in general.**  The column `(0,e,2e)` has `3e` letters, `e` of them
`b` and `2e` of them `c`.  Forcing `k` letters at each end to be `c` is consistent only while
`2k ≤ 2e`; at `e = 2, k = 3` it fails, at `e = 3, k = 3` it is tight. -/
theorem letter_budget (e k : ℕ) (he : 1 ≤ e) (hforce : 2 * k ≤ 2 * e) : k ≤ e := by omega

/-- At `e = 2` with `k = 3` the budget is violated. -/
theorem e2_budget_violated : ¬ (2 * 3 ≤ 2 * 2) := by omega

/-- At `e = 3` with `k = 3` the budget is exactly met — no contradiction. -/
theorem e3_budget_tight : 2 * 3 ≤ 2 * 3 := by omega

end Erdos634.V1Assembly
