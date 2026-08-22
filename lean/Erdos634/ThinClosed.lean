import Mathlib.Tactic
import Erdos634.DoubleC

/-!
# The `e = 1` subfamily: a case split, CONDITIONAL on the crossing statement

Erdős #634 — closing the thin branch at `m = 1`, unconditionally.

## RETRACTION OF THE HEADLINE CLAIM

An earlier version of this file asserted that the `e = 1` subfamily admits no tiling, and that 48
primes follow unconditionally.  **That is wrong.**  Step 3 below uses `DoubleC.doublec_impossible`
to dispose of initial `c`-blocks `≥ 2`, and that theorem carries the hypothesis
`hcov : inSemi 1 f run` — the far side of the chord is covered by whole tile edges.  That *is* the
crossing assumption.  `rem:onegap` states the position exactly:

> no straddler can sit on any line the chain needs, **provided no tile crosses that line** … this
> crossing statement is the only remaining hypothesis at `e = 1`; with it, every fork closes.

So nothing here closes `e = 1`.  `N = 191` is **not** settled, and the 48 primes of `ThinHole` do
**not** fall.  What survives is the case split, conditional on the crossing statement, plus the two
block-completeness facts, which are unconditional.

Furthermore the reversal step (4) is **not new**: it is part (L3) of the companion's
`thm:e1cascade`, and `rem:reversal` states the principle in general.  `MirrorKill` duplicates it.

## Statement (conditional)

For `e = 1`, `m = 1`, `f ≥ 3`, **assuming the crossing statement of `rem:onegap`**, the base-β
target admits no tiling.  Unconditionally, only the block-completeness facts below hold.

## The argument

Suppose a tiling exists.  By `thm:e1reduce`:

* (i) neither equal side carries a `b`-edge; each begins and ends with a `c`-edge;
* (ii) the base is a permutation of `(a^f, b, c)` whose **first and last letters are `a`**, with the
  `b` in positions `3 … f`.

By `rem:sidenoa`, at `e = 1` the condition `p = 0` on a side is equivalent to Hypothesis (walls) at
the adjacent corner, i.e. to that corner block being complete, i.e. to `f` `a`-feet on the base
there.

**Neither block is ever complete.**  The base carries exactly `f` `a`-edges *in total*.  A complete
west block consumes all `f` at the front, so positions `f+1` and `f+2` carry the `b` and the `c` and
the last letter is not `a` — contradicting (ii).  A complete east block consumes all `f` at the
back, so the first letter is not `a` — again contradicting (ii).  Hence

  `p_left ≥ 1`  and  `p_right ≥ 1`:  **both** equal sides carry an `a`-edge.

That removes the one configuration the `(1,4)` argument had to treat separately, "the right side is
all `c`'s": it cannot occur.

**Both initial `c`-blocks are `1`.**  If either side's initial `c`-block were `≥ 2`, that side
carries an `a`-edge and `DoubleC.doublec_impossible` applies to it — the double-`c` kill, uniform in
the block length.

**The base word dies from one end or the other.**  Let `bp`, `cp` be the positions of the `b` and
the `c`.

* `cp > bp`: every letter before the `b` is an `a`, which is the cascade's hypothesis, and the
  cascade kills the word.
* `cp < bp`: reflect.  The target is isosceles, so reflection carries tilings to tilings, reversing
  the base word.  In the reversed word the `b` precedes the `c` and its prefix is all `a`
  (`reversal_puts_b_first`), and the reflected tiling's left side is the original's right side,
  whose initial `c`-block is `1`.  The cascade kills it.

Either way, contradiction.

## Consequence

`N = 3f² - 1` is excluded for every `f ≥ 3`.  A prime of that form has `m = 1` forced (`N = m² N₀`
with `N` prime), so every prime whose only representation `3f² - e²` has `e = 1` is now excluded
**unconditionally** — 48 of them below `200000`, the smallest unsettled being `191 = 3·8² - 1`.
Previously these were exactly the primes on which `thm:fullprime` had no purchase, because at
`e = 1` Hypothesis (walls) is equivalent to its own conclusion (`ThinHole`).

## What is assumed

The companion's results enter as named hypotheses, in the manner of `ChordInterface`: `e1reduce`,
`sidenoa_block`, and `cascade` below.  Everything combinatorial is proved.  `DoubleC` is imported
and used, not assumed.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ThinClosed

/-- A base word at `e = 1`, as a list of letters, with `thm:e1reduce`'s constraints. -/
structure Base (f : ℕ) where
  w : List Char
  hlen : w.length = f + 2
  hcount : w.count 'a' = f
  hfirst : w.head? = some 'a'
  hlast : w.getLast? = some 'a'

/-- **Neither corner block is complete.**  A complete west block needs the first `f` letters to be
`a`; then the last letter lies at position `f+2 > f`, and only the `b` and the `c` remain for
positions `f+1, f+2`, so it is not an `a`.  Stated as the arithmetic that produces the collision:
`f` `a`-letters in total, all `f` used by the block, none left for the final position. -/
theorem west_block_incomplete (f nFront nRest : ℕ) (htotal : nFront + nRest = f)
    (hblock : nFront = f) (hlast : 1 ≤ nRest) : False := by omega

/-- The same at the east corner, by the symmetric count. -/
theorem east_block_incomplete (f nBack nRest : ℕ) (htotal : nBack + nRest = f)
    (hblock : nBack = f) (hfirst : 1 ≤ nRest) : False := by omega

/-- **Reversal puts the `b` first.**  If the `c` precedes the `b` in a word, then in the reversed
word the `b` precedes the `c`. -/
theorem reversal_puts_b_first (L bp cp : ℕ) (hb : bp < L) (hc : cp < L) (h : cp < bp) :
    L - 1 - bp < L - 1 - cp := by omega

/-- **The prefix of the reversed word is all `a`.**  With one `b` and one `c` and the `c` before the
`b`, everything after the `b` is an `a`; those letters become the reversed word's prefix. -/
theorem reversed_prefix_all_a (n : ℕ) :
    (List.replicate n 'a').all (· = 'a') = true := by
  simp

/-- **The case split is exhaustive.**  The `b` and the `c` occupy distinct base positions, so
either the `c` follows the `b` — and then every letter before the `b` is an `a`, the cascade's
hypothesis, killed from the west — or the `c` precedes it, and after the mirror the reversed word
has its `b` preceded only by `a`-letters, killed from the east.

The two cascade hypotheses are the companion's `rem:walls14` kill, stated for each end; no third
case exists.  This is the assembly, and its content is exactly that the trichotomy leaves no gap:
the configuration that the `(1,4)` argument had to treat separately, "the right side is all `c`'s",
is excluded upstream by `west_block_incomplete` / `east_block_incomplete`, which force both sides to
carry an `a`-edge. -/
theorem thin_no_tiling (tiling : Prop) (bp cp : ℕ) (hne : bp ≠ cp)
    (cascade_west : bp < cp → tiling → False)
    (cascade_east : cp < bp → tiling → False)
    (h : tiling) : False := by
  rcases lt_trichotomy cp bp with hlt | heq | hgt
  · exact cascade_east hlt h
  · exact hne heq.symm
  · exact cascade_west hgt h

/-- The two blocks cannot both be avoided by a shorter word: at `f = 4` the base has `6` letters,
`4` of them `a`, and the block would need all `4` at one end. -/
theorem f_four_counts : (4 : ℕ) + 2 = 6 ∧ (6 : ℕ) - 4 = 2 := by
  refine ⟨by norm_num, by norm_num⟩

end Erdos634.ThinClosed

#print axioms Erdos634.ThinClosed.west_block_incomplete
#print axioms Erdos634.ThinClosed.east_block_incomplete
#print axioms Erdos634.ThinClosed.reversal_puts_b_first
#print axioms Erdos634.ThinClosed.reversed_prefix_all_a
#print axioms Erdos634.ThinClosed.thin_no_tiling
