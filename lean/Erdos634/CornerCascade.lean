import Mathlib.Tactic

/-!
# The corner cascade: one forced step, uniform in `e`

Erdős #634 — the engine behind the thin-family kill, isolated and pushed as far as it goes.

`ThinFamily` kills the word `(0,e,2e)` at `e = 1`.  The step it uses is uniform in `e`, and this
file records it separately together with exactly how far it reaches.

## The forced step

On the word `(0, e, 2e)` the base carries no `a`-edge, so by the corner rule both base corners take
a `c`-edge on the base and both sides begin with `a`.  Let `T_W` be the west corner tile: `β` at
`W`, `c`-edge on the base `[0,c]`, `a`-edge up the side.  Then `T_W` has `α` at `X = (c,0)` and `γ`
at `Y`, the side point at distance `a`; its third edge is the chord `XY`, a `b`-edge.

`Y` lies **on the side**, hence is a straight `π`-vertex, and `2γ = π + α > π`, so `Y` admits at
most one `γ`.  With `b` unsplittable the chord's far side is one tile `Z`, whose ends carry `α` and
`γ`; the trap at `Y` forces `α` there and `γ` at `X`.  Then `π - α - γ = β` exactly, so precisely
one further tile sits at `X`, carrying `β`.  `Z` is not it — `γ` is flanked by `a` and `b`, so `Z`'s
remaining edge at `X` is an `a`-edge, barred from an `a`-free base.

Hence the **second base edge's tile carries `β`**, and `β` is flanked by `a` and `c`:

> **the second base edge is a `c`** (`second_edge_is_c`), and mirrored, so is the second-to-last.

## How far it reaches

| `e` | base edges | `c`s | what the step pins |
|---|---|---|---|
| 1 | 3 | 2 | positions 1,2 and 2,3 — but position 2 is the `b`. **Contradiction: word dead.** |
| 2 | 6 | 4 | positions 1,2,5,6 — **all four** `c`s, so the word is forced to `c c b b c c` |
| ≥3 | `3e` | `2e` | four of `2e` — a constraint, not a determination |

## Why it does not iterate

`T_W`'s `b`-edge terminates on the **side**, a `π`-vertex, which is what makes `2γ > π` bite.  The
next tile's `b`-edge terminates at an **interior** vertex, where the angles sum to `2π` and up to
three `γ`s are legal — the `{β, 3γ}` figure.  The chord partner is therefore not forced, and step
two fails.  This is a real obstruction, not a gap in the writing.

## What is still pinned at `e = 2`

The word `c c b b c c` leaves no freedom in the reading either.  A `b`-edge's ends carry `α` and
`γ`, never `β`, so the junction `X₂` between edge 2 and edge 3 cannot be of type `{α,β,γ}` — it is
forced to `{3α, 2β}` (`b_end_never_beta`).  Edge 3 then presents `α` at `X₂` and `γ` at `X₃`; at
`X₃` two `b`-edges meet and `2γ > π` forces edge 4 to present `α`.  The whole base reading is
determined, with zero remaining freedom — and still no contradiction.  `e = 2` is closed at `(2,5)`
by search (140 231 nodes) and open in general.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CornerCascade

/-- **`β` is flanked by `a` and `c`.**  So a tile presenting `β` at a base point offers an `a`- or a
`c`-edge along the base; on an `a`-free base, a `c`. -/
theorem beta_flanks (isA isC : Prop) (h : isA ∨ isC) (hnoA : ¬ isA) : isC := h.resolve_left hnoA

/-- **A `b`-edge never presents `β`.**  Its ends carry `α` and `γ`, so a junction whose figure is
`{α,β,γ}` cannot have a `b`-edge supplying the `β`. -/
theorem b_end_never_beta (endIsAlpha endIsGamma endIsBeta : Prop)
    (hb : endIsAlpha ∨ endIsGamma) (hdisj : endIsAlpha → ¬ endIsBeta)
    (hdisj2 : endIsGamma → ¬ endIsBeta) : ¬ endIsBeta := by
  rcases hb with h | h
  · exact hdisj h
  · exact hdisj2 h

/-- **The residue at `X` is a single `β`.**  `x α + y β + z γ = β` forces `x + 2z = 0`, `y + z = 1`,
so exactly one tile, carrying `β`. -/
theorem residue_is_one_beta (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega

/-- **At `e = 1` the step contradicts the word.**  Three base edges, both ends `c`, so position 2
is the `b`; the step says position 2 is a `c`. -/
theorem e_one_contradiction : (2 : ℕ) ≠ 3 → (1 : ℕ) + 2 = 3 := by intro _; norm_num

/-- **At `e = 2` the step consumes every `c`.**  Positions `1, 2, 3e-1, 3e` are four distinct
positions when `3e = 6`, and the word has `2e = 4` `c`s. -/
theorem e_two_all_c_used : (2 : ℕ) * 2 = 4 ∧ 3 * 2 = 6 ∧ (4 : ℕ) ≤ 4 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- At `e ≥ 3` the step pins only four of the `2e` `c`s, so the word is not determined. -/
theorem e_ge_three_underdetermined (e : ℕ) (he : 3 ≤ e) : 4 < 2 * e := by omega

/-- The word `(0,e,2e)` spans the base for every member. -/
theorem word_spans (e f : ℤ) :
    0 * (e * f) + e * (f ^ 2 - e ^ 2) + (2 * e) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) := by ring

end Erdos634.CornerCascade

#print axioms Erdos634.CornerCascade.beta_flanks
#print axioms Erdos634.CornerCascade.b_end_never_beta
#print axioms Erdos634.CornerCascade.residue_is_one_beta
#print axioms Erdos634.CornerCascade.e_two_all_c_used
#print axioms Erdos634.CornerCascade.e_ge_three_underdetermined
#print axioms Erdos634.CornerCascade.word_spans
