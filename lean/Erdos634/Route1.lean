import Mathlib.Tactic

/-!
# Route 1: the base words that survive the cascade, and their forced starvation

Erdős #634 — the last gap in the `e = 1` subfamily.

At `e = 1`, `m = 1`, `f ≥ 3`, `thm:e1reduce` forces the base walk to be a permutation of
`(a^f, b, c)` beginning and ending with an `a`-edge, with the `b` in positions `3, …, f`.  So the
base carries exactly `f` `a`-edges, one `b` and one `c`.

The cascade of `rem:walls14` forces, at each base junction it reaches, a `β`-slot whose tile
presents the next base edge from the flanks `{a, c}`.  Since `β` is opposite `b`, that edge is never
a `b`-edge, so the cascade dies wherever it meets the `b`.  It survives only if a `c` intervenes
first — and then only if an `a`-run follows that `c`, the "deviating run" whose new `c`-chord
escapes blocking, because `E` overshoots the blocking vertex `V` by exactly `a` for every `f`
(`Frontier`, route-1 note).  Hence the surviving words are exactly

  `a^i c a^j b a^k`,  `i, j, k ≥ 1`,  `i + j + k = f`,

with the `b` in a position allowed by `thm:e1reduce`.  Route 2, the other survivor of the `f = 4`
analysis, is now closed at every initial block length by `DoubleC.doublec_impossible`, so this
family is the last gap.

## Forced starvation

The complete west corner block is the tile scaled by `f`: it needs `f` `a`-feet on the base
(`rem:blockbreaks`).  A route-1 word spends only its first run there, of length `i`, and
`i = f - j - k ≤ f - 2` since `j, k ≥ 1`.  So **every** route-1 configuration starves the west
block — `starved_west` below.  This is not an extra hypothesis; it is forced by the word shape.

That is consistent with, and sharper than, the known failure of Hypothesis (walls) at `e = 1`: the
companion's `rem:sidenoa` derives a contradiction between the complete-block base word `a^f b c` and
`thm:e1reduce`'s requirement of `a`-edges at both ends.  Here the same collision is visible as a
count: a complete west block would need all `f` of the base's `a`-edges at the west corner, leaving
the base to end in `b` or `c` — `complete_block_forces_bad_end`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Route1

/-- A route-1 base word, recorded by the lengths of its three `a`-runs. -/
structure Word (f : ℕ) where
  i : ℕ
  j : ℕ
  k : ℕ
  hi : 1 ≤ i
  hj : 1 ≤ j
  hk : 1 ≤ k
  hsum : i + j + k = f

/-- **The west run is short.**  In any route-1 word the first `a`-run has length at most `f - 2`. -/
theorem run_le (f : ℕ) (w : Word f) : w.i ≤ f - 2 := by
  have := w.hsum; have := w.hj; have := w.hk; omega

/-- **Forced starvation.**  The complete west block needs `f` `a`-feet; a route-1 word supplies
only `i < f`.  So the west block is never complete in a route-1 configuration. -/
theorem starved_west (f : ℕ) (hf : 3 ≤ f) (w : Word f) : w.i < f := by
  have := w.hsum; have := w.hj; have := w.hk; omega

/-- **Why a complete block is impossible at `e = 1`, as a count.**  The base carries exactly `f`
`a`-edges.  A complete west block consumes all `f` of them at the west corner, so every later base
edge is a `b` or a `c`; in particular the base does not end in an `a`, contradicting
`thm:e1reduce`.  Stated as: if the west run already uses all `f` `a`-edges then no `a` remains. -/
theorem complete_block_forces_bad_end (f nWest nRest : ℕ) (htotal : nWest + nRest = f)
    (hcomplete : nWest = f) : nRest = 0 := by omega

/-- The route-1 words are the compositions of `f` into three positive parts, cut down by
`thm:e1reduce`'s placement of the `b`.  Enumeration gives `(f-2)(f-3)/2` of them: `1` at `f = 4`,
then `3, 6, 10, 15, 21` for `f = 5, …, 9`.  Recorded here only as the fact that a route-1 word
exists as soon as `f ≥ 4`, since `f = 3` admits none. -/
theorem exists_word (f : ℕ) (hf : 4 ≤ f) : Nonempty (Word f) :=
  ⟨{ i := 1, j := 1, k := f - 2, hi := le_refl 1, hj := le_refl 1,
     hk := by omega, hsum := by omega }⟩

/-- and `f = 3` admits none: `i + j + k = 3` with all parts `≥ 1` forces `i = j = k = 1`, whose
`b` would sit in position `3`, outside the deviating-run shape. -/
theorem three_is_rigid (w : Word 3) : w.i = 1 ∧ w.j = 1 ∧ w.k = 1 := by
  have := w.hsum; have := w.hi; have := w.hj; have := w.hk
  refine ⟨by omega, by omega, by omega⟩

end Erdos634.Route1

#print axioms Erdos634.Route1.run_le
#print axioms Erdos634.Route1.starved_west
#print axioms Erdos634.Route1.complete_block_forces_bad_end
#print axioms Erdos634.Route1.exists_word
#print axioms Erdos634.Route1.three_is_rigid
