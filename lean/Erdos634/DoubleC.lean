import Mathlib.Tactic
import Erdos634.Frontier

/-!
# `prop:doublec` assembled: the double-`c` kill at every initial block length

Erdős #634 — Route 2 of the `e = 1` subfamily.

The companion's `prop:doublec` states that at `e = 1`, `m = 1`, `f ≥ 3`, an equal side carrying an
`a`-edge and having initial `c`-block of length `j ≥ 2` is impossible.  Its four parts are each
already formalized:

| part | statement | Lean |
|---|---|---|
| (i) | the chord from `j c·u` to `(jf,0)` has length `jb`, cut into `j` segments of length `b` | `Frontier.chord_jb`, `Frontier.chord_jb_segment` |
| (ii) | that chord partitions only as `j` `b`-edges | `OrderForcing.partition_jb_gen` |
| (iii) | the `β`-slot lays `a` or `c`; each leaves a run outside the semigroup | `Frontier.gap_jb_minus_multiple`, `OrderForcing.through_edge_exclusive` |
| (iv) | the `α`-slot cannot lay a `c`-edge along the chord | `Frontier.overshoot_c_sub_b` |

What was missing is the **assembly**: no theorem stated `prop:doublec` itself.  This file supplies
it.

## The enumeration is not needed

`Frontier`'s route-2 note records that the `f = 4` argument ran its case split on the single word
`c c aᶠ c`, and that "Route 2 closes in general only once the same split is run over that whole
family — the ingredients are in hand, the enumeration is not."

That is too pessimistic.  `prop:doublec` is **uniform in `j`**: its proof of (iii) turns on
`gap_jb_minus_multiple`, which holds for every `1 ≤ j < f` and every run length divisible by `f`,
and its (iv) is the overshoot `c - b = e² > 0`, independent of `f` and of `j`.  The companion says
as much in the proof — `lem:wallclimb` "applies at every block length", and "Nothing here depends on
`f`, nor on `e` beyond `e² > 0`".  So the whole family `2 ≤ j ≤ f-1` dies at once and no per-word
split is required.

## What is assumed

The geometric content enters as named hypotheses, following `ChordInterface`: the corpus keeps its
zero-`sorry` property and the outstanding obligations are named rather than hidden.  `DoubleC`
bundles exactly the facts (i)-(iv) supply, and `doublec_impossible` shows they are contradictory.
The arithmetic is discharged, not assumed.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.DoubleC

open Erdos634.Frontier

/-- The double-`c` configuration at `e = 1`: an equal side carrying an `a`-edge whose initial
`c`-block has length `j ≥ 2`.

`run` is the length left on the far side of the chord after the `β`-slot tile lays its first edge.
By `prop:doublec`(iii) that edge is an `a` or a `c` — never a `b`, since `β` is opposite `b` — and a
through-edge then forces the whole remaining segment to be a single edge, so the far side must
partition `run`.  `hrun` records the two cases and `hcov` records that the far side is in fact
covered by tile edges. -/
structure Config (f j run : ℕ) : Prop where
  /-- the thin family, `f ≥ 3` (`f = 2` is degenerate, `thm:e1reduce`) -/
  hf : 3 ≤ f
  /-- initial `c`-block of length at least `2` — this is what "double `c`" means -/
  hj2 : 2 ≤ j
  /-- `prop:doublec`(i): the side begins and ends with a `c`-edge, so `j ≤ n_c ≤ f - 1` -/
  hjf : j < f
  /-- `prop:doublec`(iii): the `β`-slot lays `a` (direct) or `c` (mirrored) -/
  hrun : run + sideA 1 f = j * sideB 1 f ∨ run + sideC 1 f = j * sideB 1 f
  /-- the far side of the chord is covered by whole tile edges -/
  hcov : inSemi 1 f run

/-- **`prop:doublec`.**  The double-`c` configuration is impossible, at every initial block length
`j` with `2 ≤ j < f`, for every `f ≥ 3`. -/
theorem doublec_impossible {f j run : ℕ} (C : Config f j run) : False := by
  have h1 : 1 ≤ j := le_trans (by norm_num) C.hj2
  refine double_c_kill_general C.hf h1 C.hjf ?_ C.hcov
  have ha : sideA 1 f = f := by simp [sideA]
  have hb : sideB 1 f = f * f - 1 := by simp [sideB]
  have hc : sideC 1 f = f * f := by simp [sideC]
  rcases C.hrun with h | h
  · rw [ha, hb] at h; exact Or.inl h
  · rw [hc, hb] at h; exact Or.inr h

/-- **Uniformity in the block length.**  The hypotheses of `Config` constrain `j` only by
`2 ≤ j < f`; nothing in `doublec_impossible` mentions the base word, the side word beyond its
initial block, or any particular value of `j`.  So one theorem covers the whole family, and the
per-word enumeration is unnecessary. -/
theorem uniform_in_j (f : ℕ) :
    ∀ j, 2 ≤ j → j < f → ∀ run, Config f j run → False :=
  fun _ _ _ _ C => doublec_impossible C

/-- The count of block lengths covered: `j` ranges over `2, …, f-1`, i.e. `f - 2` values, all
killed by the single theorem above.  At `f = 4` that is the one value `j = 2` — the `c c a⁴ c` word
of the `(1,4)` argument — and at `f = 8` it is `j = 2,…,7`. -/
theorem block_lengths_covered (f : ℕ) :
    (Finset.Ico 2 f).card = f - 2 := by
  simp [Nat.card_Ico]

end Erdos634.DoubleC

#print axioms Erdos634.DoubleC.doublec_impossible
#print axioms Erdos634.DoubleC.uniform_in_j
#print axioms Erdos634.DoubleC.block_lengths_covered
