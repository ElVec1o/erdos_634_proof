import Erdos634.MidTriangleComposed

/-!
# The golden regime split, and where Beeson's Theorem 2 is unavailable

Erdős #634, base-β family, tile `(a,b,c) = (ef, f²−e², f²)`.  Three independent blind room sessions
converged on the same finding, re-verified here:

> **Beeson's Theorem 2 (arXiv:1206.2229v3 §6.1) hypothesis (i) — "none of `ABC`'s angles is greater
> than `γ`" — FAILS on a positive-density subfamily, including the smallest open base-β prime.**

The target's angles are `β, β, 3α`, so (i) requires `3α ≤ γ = 2α+β`, i.e. `α ≤ β`, i.e. `a ≤ b`,
i.e. **`f² − ef − e² ≥ 0`** — the golden condition `f/e ≥ φ`.  Below it the tile's side order is
`b < a < c`, not `a < b < c`, and the whole `e = 1` toolkit was built inside the other regime.

Among the 13 base-β primes below 250 this fails for exactly

> **`N = 23 (2,3)`, `59 (4,5)`, `83 (5,6)`, `167 (5,8)`, `179 (8,9)`** — all `e ≥ 2`,
> **including `N = 83`, the smallest open one.**

**CORRECTION (round 2 of the room, verified).**  An earlier version of this file concluded from the
above that "no amount of work on Beeson's Theorem 2 can reach those targets".  **That was wrong.**
Hypothesis (i) as *written* does fail for them — the arithmetic below is correct — but Theorem 2's
*proof* never uses it.  A line-by-line reading (`b1206.txt:1281, :1290, :1294, :1358`) finds a bound
on a target angle in exactly four places, all four at the vertex the proof itself **defines** to be
the smaller of the two non-`B` vertices (:1246 "rename `A` and `C` … so that angle `A` is less than
or equal to angle `C`"); "angle at C" occurs only in that renaming sentence.  And the fact those uses
need is **free**:

> `gamma_clause_redundant`: given `∠B = β` and the angle sum, the two non-`B` angles cannot *both*
> be `≥ γ` — otherwise `π − β ≥ 2γ`, i.e. `0 ≥ α + β`.

So Theorem 2 holds with (i) weakened to **"`ABC` is not similar to the tile"**, with no angle clause
at all, and it **does** apply to all 13 base-β primes, thick members included.

What survives of the original finding: the arithmetic (`fails_83` etc. are correct as stated), and
the audit warning below.  What does not: the conclusion that a Theorem-2-free route is *mandatory*.
It is not.  (This does not by itself advance any target — Theorem 2 supplies only the *existence* of
an essential segment, and at `(5,6)` all four directions survive the length bound by ≥20%.)

**Audit warning.** Corpus lemmas that assume `a < b` (the `MarchFlank`/`TilePlacement` side–angle
orderings) are inapplicable to these five members.  `c` is longest in every regime, so bounds resting
only on `c` being the maximum stay safe.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RegimeSplit

/-! ## The golden condition, and the side order -/

/-- **`a ≤ b ⟺ f² − ef − e² ≥ 0`.**  (`GoldenForm.quartic_neg_iff_golden` records the related
quartic; this is the direct side comparison.) -/
theorem a_le_b_iff (e f : ℤ) : e * f ≤ f ^ 2 - e ^ 2 ↔ 0 ≤ f ^ 2 - e * f - e ^ 2 := by
  constructor <;> intro h <;> linarith

/-- **Below the golden ratio the side order inverts: `b < a`.** -/
theorem b_lt_a_of_golden_fails {e f : ℤ} (h : f ^ 2 - e * f - e ^ 2 < 0) :
    f ^ 2 - e ^ 2 < e * f := by linarith

/-- **The angle clause of hypothesis (i) is redundant.**  If the two non-`B` angles were both `≥ γ`,
then `π − β = ∠A + ∠C ≥ 2γ`, which with `γ = 2α+β` and `3α+2β = π` gives `0 ≥ α + β`.  So the smaller
of them is always `< γ` — which is all Theorem 2's proof ever uses. -/
theorem gamma_clause_redundant {α β γ x y : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hsum : x + y = Real.pi - β) : ¬ (γ ≤ x ∧ γ ≤ y) := by
  rintro ⟨hx, hy⟩
  rw [hγ] at hx hy
  linarith

/-- **`c` is the longest side in every regime** (`0 < e < f`), so bounds resting only on `c` being
maximal are safe on both sides of the split. -/
theorem c_longest {e f : ℤ} (he : 0 < e) (hef : e < f) :
    e * f < f ^ 2 ∧ f ^ 2 - e ^ 2 < f ^ 2 := by
  constructor <;> nlinarith

/-! ## Hypothesis (i) of Beeson's Theorem 2 -/

/-- **Hypothesis (i) reduces to the golden condition.**  The target's apex is `3α`; `3α ≤ γ = 2α+β`
iff `α ≤ β`, which (by the side–angle order) is `a ≤ b`. -/
theorem hyp_i_iff_alpha_le_beta {α β γ : ℝ} (hγ : γ = 2 * α + β) :
    3 * α ≤ γ ↔ α ≤ β := by rw [hγ]; constructor <;> intro h <;> linarith

/-! ## The five failing targets, concretely -/

/-- **`N = 23`, `(e,f) = (2,3)`: hypothesis (i) fails.**  `a = 6 > 5 = b`. -/
theorem fails_23 : (3:ℤ) ^ 2 - 2 * 3 - 2 ^ 2 < 0 := by decide

/-- **`N = 59`, `(e,f) = (4,5)`: hypothesis (i) fails.**  `a = 20 > 9 = b`. -/
theorem fails_59 : (5:ℤ) ^ 2 - 4 * 5 - 4 ^ 2 < 0 := by decide

/-- **`N = 83`, `(e,f) = (5,6)`: hypothesis (i) fails — the smallest open base-β prime.**
`a = 30 > 11 = b`. -/
theorem fails_83 : (6:ℤ) ^ 2 - 5 * 6 - 5 ^ 2 < 0 := by decide

/-- **`N = 167`, `(e,f) = (5,8)`: hypothesis (i) fails.**  `a = 40 > 39 = b` — by one. -/
theorem fails_167 : (8:ℤ) ^ 2 - 5 * 8 - 5 ^ 2 < 0 := by decide

/-- **`N = 179`, `(e,f) = (8,9)`: hypothesis (i) fails.**  `a = 72 > 17 = b`. -/
theorem fails_179 : (9:ℤ) ^ 2 - 8 * 9 - 8 ^ 2 < 0 := by decide

/-- **The `e = 1` members all satisfy it**, which is why the failure was invisible: `a = f` and
`b = f² − 1`, so `a ≤ b` for every `f ≥ 2`. -/
theorem holds_at_e_one {f : ℤ} (hf : 2 ≤ f) : 0 ≤ f ^ 2 - 1 * f - 1 ^ 2 := by nlinarith

/-! ## The essential-segment floor is always attained -/

/-- **`K·b = (f−e)(a+c)` for every `(e,f)`.**  So the floor `Kb` is realised by a legal relation in
every member, and `Lemma 23′` can never be strengthened to a strict inequality.  (Same fact as
`RunForcing.minimal_essential_relation`, in the room's factored form.) -/
theorem floor_attained (e f : ℤ) :
    f * (f ^ 2 - e ^ 2) = (f - e) * (e * f + f ^ 2) := by ring

end Erdos634.RegimeSplit
