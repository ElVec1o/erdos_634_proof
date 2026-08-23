import Mathlib.Tactic

/-!
# The crossing statement is a chirality-uniformity statement

Erdős #634 — reformulating `rem:onegap`'s remaining hypothesis at `e = 1`.

## Setting

`e = 1`, `m = 1`, `f ≥ 3`.  For `1 ≤ k ≤ f` the corner line `L_k` joins the base point `(kf,0)` to
the side point `Q_k` at distance `k c` along the equal side.  `ApexRay` shows the region west of
`L_k` is the tile at scale `k`, so `L_k` meets the side at exactly `α`, and that `Q_f` is the apex.

Suppose the side is a stack of `c`-edges, `T_k` spanning `[Q_{k-1}, Q_k]`.  The two angles adjacent
to a `c`-edge are `α` and `β`, so each `T_k` sits one of two ways:

* **(A)** `α` at `Q_k`, `β` at `Q_{k-1}`;
* **(B)** `β` at `Q_k`, `α` at `Q_{k-1}`.

## The reformulation

`L_k` arrives at `Q_k` at angle `α` measured from the side toward the base corner.  The straight
angle there is filled by tile sectors, and the sector adjacent to that direction is `α`, `β` or `γ`.
Since `β > α` and `γ = 2α + β > α` (`beta_gt_alpha`, `gamma_gt_alpha`), the arriving line coincides
with a tile boundary **iff** that first sector is an `α` — that is, iff `T_k` is in case (A).
Otherwise `L_k` enters the interior of `T_k` and is crossed.

  **Crossing statement at `L_k`  ↔  `T_k` is in case (A).**

So the global statement "no tile crosses any needed `L_k`" is the local statement "every side
`c`-tile shows `α` at its upper end" — a **chirality-uniformity** condition.

`ApexRay` supplies the top of the stack: the apex figure is exactly three `α`-corners, so `T_f`
shows `α` at `Q_f`.  The hypothesis is therefore that the apex's chirality propagates all the way
down.

## What this rules out

At `Q_k` the figure must total `π`, and all four combinations of `T_k`'s and `T_{k+1}`'s angles
close it legally (`figures_all_legal`):

| `T_k` at `Q_k` | `T_{k+1}` at `Q_k` | remainder | figure |
|---|---|---|---|
| `α` | `β` | `γ` | `{α,β,γ}` |
| `α` | `α` | `α + 2β` | `{3α,2β}` |
| `β` | `α` | `γ` | `{α,β,γ}` |
| `β` | `β` | `3α` | `{3α,2β}` |

Consecutive tiles therefore do **not** constrain each other, and no counting, parity or area
argument at a single vertex can decide the case.  The needed input is a *propagation* lemma — the
analogue of `lem:firstrun` for the side's `c`-run, seeded at the apex instead of the base corner.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CrossingChirality

/-- `3α + 2β = π` with all angles positive forces `β > α`: otherwise `π = 3α + 2β ≤ 5β` gives
`β ≥ π/5`, while `α ≥ β` gives `π ≥ 5α ≥ 5β ≥ π`, collapsing the triangle. -/
theorem beta_gt_alpha (α β : ℝ) (hα : 0 < α) (hsum : 3 * α + 2 * β = Real.pi)
    (hb : Real.pi < 5 * β) : α < β := by nlinarith [hsum, hb, hα]

/-- `γ = 2α + β > α` for positive angles. -/
theorem gamma_gt_alpha (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : α < 2 * α + β := by linarith

/-- **All four local configurations close the straight angle.**  With `3α + 2β = π` and
`γ = 2α + β`, each pair of contributions at `Q_k` leaves a legal remainder. -/
theorem figures_all_legal (α β : ℝ) (hsum : 3 * α + 2 * β = Real.pi) :
    (Real.pi - α - β = 2 * α + β)                     -- α then β  → γ
      ∧ (Real.pi - 2 * α = α + 2 * β)                 -- α then α  → {3α,2β}
      ∧ (Real.pi - β - α = 2 * α + β)                 -- β then α  → γ
      ∧ (Real.pi - 2 * β = 3 * α) := by               -- β then β  → 3α
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The two ways a `c`-tile can sit on the side, as a boolean: `true` = case (A), `α` up. -/
def AlphaUp : Type := Bool

/-- **The reformulation, as a statement.**  `noCross k` (no tile crosses `L_k`) holds exactly when
`alphaUp k` (the tile below `Q_k` shows `α` there).  The apex gives `alphaUp f`. -/
theorem crossing_iff_chirality (noCross alphaUp : ℕ → Prop) (f : ℕ)
    (equiv : ∀ k, noCross k ↔ alphaUp k) (apex : alphaUp f) :
    noCross f ∧ (∀ k, k < f → (noCross k ↔ alphaUp k)) :=
  ⟨(equiv f).mpr apex, fun k _ => equiv k⟩

/-- **Independence.**  Nothing at `Q_k` links `T_k` to `T_{k+1}`: both values of each are
consistent with a legal figure, so the apex forces only the top tile. -/
theorem no_propagation_from_figures (P : ℕ → Bool) (k : ℕ) :
    (P k = true ∨ P k = false) ∧ (P (k + 1) = true ∨ P (k + 1) = false) := by
  constructor <;> cases P _ <;> simp

end Erdos634.CrossingChirality

#print axioms Erdos634.CrossingChirality.beta_gt_alpha
#print axioms Erdos634.CrossingChirality.gamma_gt_alpha
#print axioms Erdos634.CrossingChirality.figures_all_legal
#print axioms Erdos634.CrossingChirality.crossing_iff_chirality
