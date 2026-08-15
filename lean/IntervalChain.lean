import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Basic

/-!
# Ordered runs: a covering family of intervals abuts

Erdős #634 — the G3 bookkeeping.

`WallChain.wall_partition` and `EdgeChain.side_partition` give, for each side of a wall, a finite
family of closed intervals (the tile-edge traces) which **cover** the segment and meet pairwise in
at most a point.  Every downstream consumer — `ChordInterface.FarSide`, `ChordDecomp.ChordTrace`,
and the two-sided chord arguments of `RogueChord`/`RogueMirror` — needs one step more: that this
family, read in order, is a **chain**, so that the breakpoints are the prefix sums of the lengths
and a "first common breakpoint" is well defined.

That step is pure order theory over `ℝ`, with no geometry in it, and this file proves its crux:

> **`successor`** — if the intervals cover `[0, L]` and meet pairwise in at most a point, then the
> right endpoint of any interval that is not `L` is the left endpoint of another interval.

The argument is elementary.  Write `b` for the right endpoint in question and suppose no interval
starts at `b`.

* No interval can *straddle* `b` (`no_straddle`): one with `lo j < b < hi j` would meet the given
  interval in `[max (lo i) (lo j), b]`, a set with two distinct points, contradicting the
  pairwise-subsingleton hypothesis.
* Hence every interval covering a point just to the right of `b` must **start** to the right of `b`
  (`starts_right`).
* But then the least such left endpoint `c` satisfies `c > b`, and the midpoint `(b+c)/2` lies in
  `(b, c)` and is `≤ L`; whatever covers it starts in `(b, (b+c)/2]`, contradicting minimality.

`chain_of_cover` packages the successor step together with `first_starts_at_zero`, which is the
same argument run at the left end.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.IntervalChain

open Set

variable {n : ℕ} {L : ℝ} {lo hi : Fin n → ℝ}

/-- The standing shape of a covering family: nondegenerate closed intervals inside `[0, L]` which
cover `[0, L]` and meet pairwise in at most one point. -/
structure Cover (L : ℝ) (lo hi : Fin n → ℝ) : Prop where
  lt : ∀ i, lo i < hi i
  nonneg : ∀ i, 0 ≤ lo i
  le : ∀ i, hi i ≤ L
  cover : ∀ x, 0 ≤ x → x ≤ L → ∃ i, x ∈ Icc (lo i) (hi i)
  meet : ∀ i j, i ≠ j → ∀ x y, x ∈ Icc (lo i) (hi i) → x ∈ Icc (lo j) (hi j) →
    y ∈ Icc (lo i) (hi i) → y ∈ Icc (lo j) (hi j) → x = y

/-- **No interval straddles another's right endpoint.**  If `lo j < hi i < hi j` then the two
intervals share the whole of `[max (lo i) (lo j), hi i]`, which contains two distinct points. -/
theorem no_straddle (H : Cover L lo hi) (i j : Fin n)
    (h1 : lo j < hi i) (h2 : hi i < hi j) : False := by
  have hij : j ≠ i := by rintro rfl; exact absurd h2 (lt_irrefl _)
  set p := max (lo i) (lo j) with hp
  have hpb : p < hi i := max_lt (H.lt i) h1
  have hpi : p ∈ Icc (lo i) (hi i) := ⟨le_max_left _ _, le_of_lt hpb⟩
  have hpj : p ∈ Icc (lo j) (hi j) := ⟨le_max_right _ _, le_of_lt (hpb.trans h2)⟩
  have hbi : hi i ∈ Icc (lo i) (hi i) := ⟨le_of_lt (H.lt i), le_rfl⟩
  have hbj : hi i ∈ Icc (lo j) (hi j) := ⟨le_of_lt h1, le_of_lt h2⟩
  exact absurd (H.meet i j hij.symm p (hi i) hpi hpj hbi hbj) (ne_of_lt hpb)

/-- **Anything covering a point past `b = hi i` starts at or past `b`.**  Combined with the
assumption that nothing *starts* at `b`, it must start strictly past it. -/
theorem starts_right (H : Cover L lo hi) (i : Fin n) (hnone : ∀ j, lo j ≠ hi i)
    (x : ℝ) (hx : hi i < x) (hxL : x ≤ L) : ∃ j, hi i < lo j ∧ lo j ≤ x := by
  have hx0 : 0 ≤ x := le_trans (le_trans (H.nonneg i) (le_of_lt (H.lt i))) (le_of_lt hx)
  obtain ⟨j, hj1, hj2⟩ := H.cover x hx0 hxL
  have hbj : hi i < hi j := lt_of_lt_of_le hx hj2
  have : ¬ lo j < hi i := fun hc => no_straddle H i j hc hbj
  exact ⟨j, lt_of_le_of_ne (not_lt.mp this) (Ne.symm (hnone j)), hj1⟩

/-- **The successor step.**  Every right endpoint below `L` is some interval's left endpoint. -/
theorem successor (H : Cover L lo hi) (i : Fin n) (hb : hi i < L) :
    ∃ j, lo j = hi i := by
  by_contra hcon
  simp only [not_exists] at hcon
  -- the set of left endpoints strictly past `hi i`
  have hTne : (Finset.univ.filter (fun j => hi i < lo j)).Nonempty := by
    obtain ⟨j, hj1, _⟩ := starts_right H i hcon L hb le_rfl
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj1⟩⟩
  obtain ⟨j0, hj0T, hj0min⟩ :=
    (Finset.univ.filter (fun j => hi i < lo j)).exists_min_image lo hTne
  have hj0 : hi i < lo j0 := (Finset.mem_filter.mp hj0T).2
  -- the midpoint of `(hi i, lo j0)` is covered, and whatever covers it starts too early
  have hxb : hi i < (hi i + lo j0) / 2 := by linarith
  have hxc : (hi i + lo j0) / 2 < lo j0 := by linarith
  have hj0L : lo j0 ≤ L := le_trans (le_of_lt (H.lt j0)) (H.le j0)
  have hxL : (hi i + lo j0) / 2 ≤ L := by linarith
  obtain ⟨j, hj1, hj2⟩ := starts_right H i hcon _ hxb hxL
  have hjT : j ∈ Finset.univ.filter (fun j => hi i < lo j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj1⟩
  exact absurd (hj0min j hjT) (not_le.mpr (lt_of_le_of_lt hj2 hxc))

/-- **The left end.**  Some interval starts at `0`: whatever covers `0` must, since its left
endpoint is `≥ 0` and `≤ 0`. -/
theorem first_starts_at_zero (H : Cover L lo hi) (hL : 0 ≤ L) : ∃ i, lo i = 0 := by
  obtain ⟨i, hi1, _⟩ := H.cover 0 le_rfl hL
  exact ⟨i, le_antisymm hi1 (H.nonneg i)⟩

/-- **The chain.**  Packaging: the family starts at `0`, and every right endpoint short of `L` is
matched by a left endpoint.  Reading the intervals in increasing order of left endpoint therefore
produces a chain whose breakpoints are the prefix sums of the lengths — the ordered run that
`FarSide` and `ChordTrace` consume. -/
theorem chain_of_cover (H : Cover L lo hi) (hL : 0 ≤ L) :
    (∃ i, lo i = 0) ∧ (∀ i, hi i < L → ∃ j, lo j = hi i) :=
  ⟨first_starts_at_zero H hL, fun i h => successor H i h⟩

/-- The successor is unique: two intervals starting at the same point would share a whole
subinterval. -/
theorem successor_unique (H : Cover L lo hi) (j j' : Fin n)
    (h : lo j = lo j') : j = j' := by
  by_contra hne
  have hpq : lo j < min (hi j) (hi j') := lt_min (H.lt j) (by rw [h]; exact H.lt j')
  have hpj : lo j ∈ Icc (lo j) (hi j) := ⟨le_rfl, le_of_lt (H.lt j)⟩
  have hpj' : lo j ∈ Icc (lo j') (hi j') :=
    ⟨h.symm.le, by rw [h]; exact le_of_lt (H.lt j')⟩
  have hqj : min (hi j) (hi j') ∈ Icc (lo j) (hi j) := ⟨le_of_lt hpq, min_le_left _ _⟩
  have hqj' : min (hi j) (hi j') ∈ Icc (lo j') (hi j') :=
    ⟨by rw [← h]; exact le_of_lt hpq, min_le_right _ _⟩
  exact absurd (H.meet j j' hne _ _ hpj hpj' hqj hqj') (ne_of_lt hpq)

end Erdos634.IntervalChain

#print axioms Erdos634.IntervalChain.no_straddle
#print axioms Erdos634.IntervalChain.starts_right
#print axioms Erdos634.IntervalChain.successor
#print axioms Erdos634.IntervalChain.first_starts_at_zero
#print axioms Erdos634.IntervalChain.chain_of_cover
#print axioms Erdos634.IntervalChain.successor_unique
