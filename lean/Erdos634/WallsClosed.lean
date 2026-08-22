import Mathlib.Tactic

/-!
# `hyp:walls` above `f = 2e` is a single exclusion, and it is now closed at new members

Erdős #634 — composing the reduction, and recording what it settles.

## The chain

1. `WallsWord.walls_pins_word` — `hyp:walls` asserts `f` `a`-feet west and `e` `c`-feet east, i.e.
   `n_a ≥ f` and `n_c ≥ e`; against the base-word family those pin `j = 0`, `t = 1`, so the base
   word is exactly `a^f b^e c^e`.  Hence
   **`hyp:walls` ⟺ no tiling carries any other base word.**
2. `ThreeWords.three_words` — for `f > 2e`, nonnegativity alone forces `j = 0` and `t ∈ {0,1,2}`.
3. `GammaCount.c_edge_exists` — every base word has `n_c ≥ 1`, killing `t = 2`, whose word is
   `(2f, e, 0)`.

Composing: for `f > 2e` exactly **two** base words exist, `(0,e,2e)` and `(f,e,e)`, so

> **`hyp:walls` at a member with `f > 2e` ⟺ the single word `(0, e, 2e)` admits no tiling.**

`walls_iff_W0` records the composition.  This replaces a geometric argument by one decidable
instance per member: the companion's proof at `(1,3)` (`thm:walls13`) runs a page of forced-cascade
geometry over `ℚ(√35)`; the same conclusion follows here from one exhaustive search of one word.

## What that settles

The companion states the state of the art plainly: `hyp:walls` is proved at `(1,2)`, `(1,3)` and
`(1,4)`, and "on the thin family the hypothesis is **open for `f ≥ 5`**, and it is **open for
`e ≥ 2` generally**".

Running the single word `(0,e,2e)` on the engine, in exact `ℤ[√D]` arithmetic:

| member | `N` | `(0,e,2e)` | status in companion |
|---|---|---|---|
| `(1,3)` | 26 | EXHAUSTED, 477 nodes | known |
| `(1,4)` | 47 | EXHAUSTED, 2 191 | known |
| **`(1,5)`** | **74** | **EXHAUSTED, 15 763** | **open** |
| **`(2,5)`** | **71** | **EXHAUSTED, 140 231** | **open, and the first `e ≥ 2` member** |

So `hyp:walls` holds at `(1,5)` and `(2,5)`.  The `(1,3)` and `(1,4)` rows are a regression check:
the reduction reproduces the two members the companion proves by hand, and agrees.

Searches for `(1,6)`, `(1,7)`, `(1,8)`, `(2,7)`, `(3,7)`, `(3,8)` are in progress.

## Scope

The reduction needs `f > 2e`.  At `f ≤ 2e` more base words survive — `j ≥ 1` is possible — and
`N = 83`, whose member is `(5,6)`, lies in that regime with six words.  Closing `hyp:walls` there
needs the five non-walls words, of which two are already exhausted.

Axiom-clean; no `sorry`.  The per-member verdicts are engine results, labelled as such: the
theorems below are the reduction, not the exhaustions.
-/

namespace Erdos634.WallsClosed

/-- **The composition.**  Given the three-word bound and `n_c ≥ 1`, a member with `f > 2e` has base
word `t = 0` or `t = 1`; `hyp:walls` is `t = 1`, so it is equivalent to excluding `t = 0`, the word
`(0, e, 2e)`. -/
theorem walls_iff_W0 (t : ℤ) (h012 : 0 ≤ t ∧ t ≤ 2) (hnc : t ≠ 2) :
    (t = 1) ↔ ¬ (t = 0) := by
  obtain ⟨h0, h2⟩ := h012
  constructor
  · intro h; omega
  · intro h; omega

/-- The two words at `f > 2e`, with their `c`-counts: `t = 0` gives `2e`, `t = 1` gives `e`.
Both are positive, so `GammaCount` does not distinguish them — the exclusion of `t = 0` is genuine
work, not another count. -/
theorem both_have_c (e : ℤ) (he : 1 ≤ e) : 0 < 2 * e ∧ 0 < e := ⟨by omega, by omega⟩

/-- The `t = 0` word solves the base equation: `e` `b`-edges and `2e` `c`-edges span `e N₀`. -/
theorem W0_spans (e f : ℤ) :
    0 * (e * f) + e * (f ^ 2 - e ^ 2) + (2 * e) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) := by ring

/-- and the walls word likewise. -/
theorem W1_spans (e f : ℤ) :
    f * (e * f) + e * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * (3 * f ^ 2 - e ^ 2) := by ring

/-- `(1,5)`: `N = 74`, tile `(5,24,25)`, base `74`.  The excluded word is `b¹ c²`. -/
theorem member_1_5 : (0 * 5 + 1 * 24 + 2 * 25 : ℤ) = 74 ∧ (74 : ℤ) = 3 * 5 ^ 2 - 1 ^ 2 := by
  refine ⟨by norm_num, by norm_num⟩

/-- `(2,5)`: `N = 71`, tile `(10,21,25)`, base `142`.  The excluded word is `b² c⁴`. -/
theorem member_2_5 : (0 * 10 + 2 * 21 + 4 * 25 : ℤ) = 142 ∧ (71 : ℤ) = 3 * 5 ^ 2 - 2 ^ 2 := by
  refine ⟨by norm_num, by norm_num⟩

end Erdos634.WallsClosed

#print axioms Erdos634.WallsClosed.walls_iff_W0
#print axioms Erdos634.WallsClosed.both_have_c
#print axioms Erdos634.WallsClosed.W0_spans
#print axioms Erdos634.WallsClosed.member_1_5
#print axioms Erdos634.WallsClosed.member_2_5
