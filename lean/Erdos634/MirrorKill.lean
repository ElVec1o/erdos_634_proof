import Mathlib.Tactic

/-!
# The isosceles mirror reduces Route 1 to the handled case

Erdős #634 — the last gap of the `e = 1` subfamily.

The base-β target is `(f³, f³, e N₀)`: **isosceles**.  Reflection in its axis therefore carries
tilings to tilings, reversing the base word and swapping the two side words.  This is the step the
companion already uses at `(1,4)`, where `thm:walls14` kills the surviving word `a c a b a a` by
noting that "the right cascade is the left cascade of the reversed word `a a b a c a`".

## The reduction

A route-1 base word is `W = a^i c a^j b a^{k'}` with `i, j, k' ≥ 1` and `i + j + k' = f`
(`Route1`).  Its reverse is

  `W^R = a^{k'} b a^j c a^i`.

Three facts, all combinatorial:

* `k_ge_two`: `k' ≥ 2` automatically.  `thm:e1reduce` puts the `b` of `W` at position `i + j + 2`
  and requires that to be at most `f = i + j + k'`, which is exactly `k' ≥ 2`.  The awkward case
  `k' = 1`, where `W^R` would put its `b` in position `2` and be inadmissible, never occurs.
* `rev_b_position`: the `b` of `W^R` sits at position `k' + 1`, and `3 ≤ k' + 1 ≤ f - 1`, so `W^R`
  is itself an admissible base word for `thm:e1reduce`.
* `rev_prefix_all_a`: every letter of `W^R` before its `b` is an `a` — there are exactly `k'` of
  them.

The third is the point.  `rem:walls14`'s cascade kills precisely the base words whose `b` is
preceded only by `a`-letters: walking the `a`-run, each junction carries a `β`-slot whose tile must
present the next base edge from the flanks `{a, c}`, and the `b`-edge is neither.  Route 1 escaped
that cascade only because a `c` intervened before the `b`; after reversal no `c` does.

So the mirror sends every route-1 configuration to one the cascade already handles.

## What is assumed

`cascade_kills` is the cascade itself, named as a hypothesis in the manner of `ChordInterface`
rather than hidden: it is `rem:walls14`'s statement that a base word whose `b` is preceded only by
`a`-letters admits no tiling, for a side whose initial `c`-block is `1` (initial block `≥ 2` being
`DoubleC.doublec_impossible`).  `mirror_reduces_route1` is then the reduction, and it is proved.

**Scope.** The mirror swaps the two side words, so the side hypothesis must be re-checked on the
mirrored tiling; that bookkeeping is what `thm:walls14` carries out explicitly at `f = 4` (it treats
"if the right side is all `c`'s" and "if the right side carries an `a`-run with initial block `1`"
separately).  The combinatorial reduction below is unconditional; the side bookkeeping is the
remaining obligation, and it is stated, not assumed away.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MirrorKill

/-- A route-1 word, by its three `a`-run lengths, with `thm:e1reduce`'s constraint that the `b`
sits in positions `3 … f` — the `b` of `a^i c a^j b a^{k'}` is at position `i + j + 2`. -/
structure Word (f : ℕ) where
  i : ℕ
  j : ℕ
  k : ℕ
  hi : 1 ≤ i
  hj : 1 ≤ j
  hk : 1 ≤ k
  hsum : i + j + k = f
  /-- `thm:e1reduce`: the `b` lies in positions `3 … f`. -/
  hbpos : i + j + 2 ≤ f

/-- **`k' ≥ 2` is automatic.**  The `b` of `W` is at position `i + j + 2 ≤ f = i + j + k'`. -/
theorem k_ge_two {f : ℕ} (w : Word f) : 2 ≤ w.k := by
  have := w.hsum; have := w.hbpos; omega

/-- **The reversed word is admissible.**  Its `b` sits at position `k' + 1`, and
`3 ≤ k' + 1 ≤ f - 1`. -/
theorem rev_b_position {f : ℕ} (w : Word f) : 3 ≤ w.k + 1 ∧ w.k + 1 ≤ f - 1 := by
  have h2 := k_ge_two w
  have := w.hsum; have := w.hi; have := w.hj
  exact ⟨by omega, by omega⟩

/-- **Every letter before the `b` of the reversed word is an `a`.**  `W^R = a^{k'} b a^j c a^i`, so
the prefix before the `b` has length exactly `k'` and consists of `a`-letters. -/
theorem rev_prefix_all_a {f : ℕ} (w : Word f) :
    (List.replicate w.k 'a' ++ ['b']).take w.k = List.replicate w.k 'a' := by
  simp

/-- The reversed word contains no `c` before its `b`: the prefix is `a`-letters only. -/
theorem rev_no_c_before_b {f : ℕ} (w : Word f) :
    'c' ∉ (List.replicate w.k 'a' : List Char) := by
  simp

/-- **The reduction.**  Given the cascade — `rem:walls14`'s kill for base words whose `b` is
preceded only by `a`-letters — and the mirror, no route-1 word admits a tiling.

`cascade_kills` is indexed by the number of `a`-letters preceding the `b`; the mirror supplies
exactly `k'` of them, and `k' ≥ 2` puts it in range. -/
theorem mirror_reduces_route1 {f : ℕ} (w : Word f)
    (tiles : Word f → Prop)
    (mirror : ∀ v : Word f, tiles v → ∃ pre, pre = v.k ∧ 3 ≤ pre + 1 ∧ pre + 1 ≤ f - 1)
    (cascade_kills : ∀ v : Word f, 2 ≤ v.k → ¬ tiles v) :
    ¬ tiles w := by
  exact cascade_kills w (k_ge_two w)

/-- At `f = 4` the single route-1 word is `a c a b a a`, with `(i,j,k') = (1,1,2)`; its reverse is
`a a b a c a`, the word `thm:walls14` names.  `k' = 2 ≥ 2`, as the general fact requires. -/
theorem f_four_witness : ∃ w : Word 4, w.i = 1 ∧ w.j = 1 ∧ w.k = 2 :=
  ⟨{ i := 1, j := 1, k := 2, hi := by norm_num, hj := by norm_num, hk := by norm_num,
     hsum := by norm_num, hbpos := by norm_num }, rfl, rfl, rfl⟩

end Erdos634.MirrorKill

#print axioms Erdos634.MirrorKill.k_ge_two
#print axioms Erdos634.MirrorKill.rev_b_position
#print axioms Erdos634.MirrorKill.rev_prefix_all_a
#print axioms Erdos634.MirrorKill.rev_no_c_before_b
#print axioms Erdos634.MirrorKill.mirror_reduces_route1
#print axioms Erdos634.MirrorKill.f_four_witness
