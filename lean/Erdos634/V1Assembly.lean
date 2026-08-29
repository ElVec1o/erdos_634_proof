import Mathlib.Tactic
import Erdos634.V1Gaps

/-!
# The `V₁` repair's combinatorial endgame at `e = 2`

Erdős #634, the `e ≥ 2` column `(0,e,2e)`.  `V1Gaps` holds the repair's three arithmetic kills
(`N1`, `N2`, `N3`).  This file records the *letter count* that turns the repair into the `e = 2`
conclusion, in the sharper form adversarial review supplied.

**What the count actually is.**  The column `(0,e,2e)` at `e = 2` has six letters: two `b`s and
four `c`s, no `a`s.  `prop:cornerpara` — already two-sided and needing no separation — pins the
first two and last two base positions to `{a,c}`, and with no `a` available those four positions
take all four `c`s.  The word is therefore `c c b b c c`, and positions three and four are `b`.
The `V₁` repair forces position three to be `c`: a fifth `c` where only four exist.

Two honest notes, both from review:

* **The mirror is redundant at `e = 2`.**  The earlier presentation derived three forced `c`s from
  the west chain and three more by reflection.  That is unnecessary — `cornerpara` alone places
  all four `c`s — so the reflection question, which is delicate, does not gate the `e = 2` result.
  It does gate `e = 3`, where the same forcing leaves `c³b³c³` consistent.
* **No range in `f` is gained.**  Both `f > 2e` and the separation hypothesis give `f ≥ 5` at
  `e = 2`.  What the repair buys is not new members but the *removal of Hypothesis walls* from the
  dichotomy step there.

**This file is bookkeeping, not evidence.**  Its content is the letter count; every geometric step
of the repair sits on the far side of the unbuilt bridges named in the companion's
`rem:pingaps`, and nothing here should be cited as formalizing them.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.V1Assembly

/-- **The far-tip kill.**  At the boundary point `W` the budget is `π`, while the two tiles
meeting there present `γ` each: `2γ = π + α > π`. -/
theorem two_gamma_boundary_kill (a b g p : ℝ) (ha : 0 < a)
    (hg : g = 2 * a + b) (hp : p = 3 * a + 2 * b) (hfit : 2 * g ≤ p) : False := by
  rw [hg, hp] at hfit; linarith

/-- **The `e = 2` contradiction, faithfully.**  `w i = true` reads "position `i` carries `c`".
The word has exactly four `c`s; `cornerpara` places them at positions `0,1,4,5`; the repair forces
position `2` as well.  Five `c`s among four. -/
theorem e2_word_contradiction (w : Fin 6 → Bool)
    (hcount : (Finset.univ.filter fun i => w i = true).card = 4)
    (hcorner : w 0 = true ∧ w 1 = true ∧ w 4 = true ∧ w 5 = true)
    (hrepair : w 2 = true) : False := by
  obtain ⟨h0, h1, h4, h5⟩ := hcorner
  have hsub : ({0, 1, 2, 4, 5} : Finset (Fin 6)) ⊆
      Finset.univ.filter fun i => w i = true := by
    intro i hi
    fin_cases hi <;> simp [h0, h1, h4, h5, hrepair]
  have hcard : ({0, 1, 2, 4, 5} : Finset (Fin 6)).card = 5 := by decide
  have := Finset.card_le_card hsub
  rw [hcard, hcount] at this
  omega

/-- **Why `e = 3` survives the same forcing.**  Nine letters, six `c`s; `cornerpara` places four
and the repair a fifth and sixth, leaving the middle three `b`s untouched — `c³b³c³` meets every
count, so no contradiction arises and the `V₂` step, whose anchors are interior rather than
boundary, is the genuine residue. -/
theorem e3_count_survives :
    ∃ w : Fin 9 → Bool,
      (Finset.univ.filter fun i => w i = true).card = 6 ∧
      (∀ i : Fin 9, i.val < 3 → w i = true) ∧
      (∀ i : Fin 9, 6 ≤ i.val → w i = true) := by
  refine ⟨fun i => decide (i.val < 3 ∨ 6 ≤ i.val), by decide, ?_, ?_⟩
  · intro i hi; simp [hi]
  · intro i hi; simp [hi]

/-! ## Why the repair is `k = 1` only, and what `V₂` therefore needs

The `V₁` repair works because the chord tip `W₁ = 2a\,u` lies on the target's equal side, so
nothing continues past it.  The tip at step `k` is `W_k = ((k-1)c, 0) + 2a\,u`, and it lies on the
equal side's ray exactly when `k = 1`: the offset `((k-1)c, 0)` is horizontal while `u` is not, so
it can only be absorbed when it vanishes.  Verified numerically at five members — `W₁` at distance
exactly `0` from the side, `W₂` interior by about a tile diameter — and proved here in the form
that matters, that the offset must vanish.

**Consequence for `V₂`.**  No refinement of the boundary argument can reach it: the blocker at
`V₂` would have to be the tiles already forced by the `V₁` analysis, not the target's edge.  That
is the locating problem again, in its per-configuration form, and it is the honest statement of
what the `e = 3` step needs. -/

/-- **The chord tip leaves the side ray unless `k = 1`.**  If `((k-1)c, 0) + 2a·u = t·u` with `u`
not horizontal and `c ≠ 0`, then `k = 1`. -/
theorem chord_tip_on_ray_iff (k : ℕ) (c a t u₁ u₂ : ℝ) (hc : c ≠ 0) (hu : u₂ ≠ 0)
    (h1 : ((k : ℝ) - 1) * c + 2 * a * u₁ = t * u₁)
    (h2 : 2 * a * u₂ = t * u₂) : (k : ℝ) = 1 := by
  have ht : t = 2 * a := by
    have := mul_right_cancel₀ hu (by linarith : 2 * a * u₂ = t * u₂)
    linarith
  rw [ht] at h1
  have : ((k : ℝ) - 1) * c = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hc

end Erdos634.V1Assembly
