import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Contiguity: a closed cover of full measure has no gaps

Erdős #634, bridge (c)'s remaining geometry.  The wall partition gives that the tile edges along a
wall have measures summing to the wall's length.  That alone does **not** give contiguity — a
measure identity says nothing about gaps a priori.  What closes it is that the edges are *closed*
sets: a closed subset of an interval whose measure is the interval's whole measure **is** the
interval, because its complement is open and null, and a nonempty open set in `ℝ` has positive
measure.

`closed_full_measure_eq` is that fact.  Applied to the union of a wall's chain edges — finitely
many closed segments, so the union is closed — it upgrades "the measures sum to the length" into
"the union is the whole segment", which is exactly the no-gap statement the ordering needs.

`no_gap_between` records the consequence in the form the indexing consumes: a point of the wall
missed by every chain edge cannot exist.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Contiguity

open MeasureTheory Set

/-- **A closed subset of full measure is everything.**  If `S` is closed, contained in `[a,b]` with
`a < b`, and has the same volume, then `S = [a,b]`. -/
theorem closed_full_measure_eq {a b : ℝ} (hab : a < b) (S : Set ℝ)
    (hclosed : IsClosed S) (hsub : S ⊆ Icc a b)
    (hvol : volume S = volume (Icc a b)) : S = Icc a b := by
  have hfin : volume (Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hSfin : volume S ≠ ⊤ := by rw [hvol]; exact hfin
  -- the leftover is null
  have hdiff : volume (Icc a b \ S) = 0 := by
    rw [measure_diff hsub hclosed.measurableSet.nullMeasurableSet hSfin, hvol]
    simp
  -- the open part of the leftover is open and null, hence empty
  have hopen : IsOpen (Ioo a b \ S) := isOpen_Ioo.sdiff hclosed
  have hnull : volume (Ioo a b \ S) = 0 :=
    measure_mono_null (diff_subset_diff_left Ioo_subset_Icc_self) hdiff
  have hempty : Ioo a b \ S = ∅ := by
    by_contra hne
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hne
    have : 0 < volume (Ioo a b \ S) :=
      hopen.measure_pos volume ⟨x, hx⟩
    exact absurd hnull (ne_of_gt this)
  -- so the open interval is inside S, and S is closed
  have hIoo : Ioo a b ⊆ S := by
    intro x hx
    by_contra hcon
    exact absurd (mem_empty_iff_false x |>.mp (hempty ▸ ⟨hx, hcon⟩)) not_false
  have hIcc : Icc a b ⊆ S := by
    have := closure_mono hIoo
    rwa [closure_Ioo (ne_of_lt hab), hclosed.closure_eq] at this
  exact subset_antisymm hsub hIcc

/-- **No gaps.**  Under the same hypotheses, every point of the interval lies in `S`: a point of
the wall missed by every chain edge cannot exist. -/
theorem no_gap_between {a b : ℝ} (hab : a < b) (S : Set ℝ)
    (hclosed : IsClosed S) (hsub : S ⊆ Icc a b)
    (hvol : volume S = volume (Icc a b)) {x : ℝ} (hx : x ∈ Icc a b) : x ∈ S := by
  rw [closed_full_measure_eq hab S hclosed hsub hvol]; exact hx

/-- The union of finitely many closed sets is closed — so a wall's chain edges, being finitely
many closed segments, present a closed union and the lemma above applies to them. -/
theorem finite_union_closed {ι : Type*} (s : Finset ι) (E : ι → Set ℝ)
    (h : ∀ i ∈ s, IsClosed (E i)) : IsClosed (⋃ i ∈ s, E i) :=
  Set.Finite.isClosed_biUnion s.finite_toSet h

/-! ## What the sort needs: a key, and no gaps between consecutive keys

Turning `lineChain` into a list means sorting by a key — the left endpoint's parameter along the
base — and reading adjacency off the sorted order.  Two facts make that mechanical, and neither is
free:

* the key is **injective** on the chain.  Two distinct non-degenerate edges cannot share a left
  endpoint, since their interiors would then overlap, contradicting the tiles' disjointness
  (`distinct_left_endpoints`).
* consecutive keys leave **no gap**.  If one edge ends at `q`, the next begins at `r`, and `q < r`,
  then any point strictly between is covered by neither — and by `no_gap_between` it must be
  covered, so no such point exists and `q = r` (`gap_forces_meet`).

Together with `closed_full_measure_eq` these reduce the ordering to `Finset.sort` bookkeeping. -/

/-- **The sort key is injective.**  Two non-degenerate intervals with disjoint interiors cannot
share a left endpoint. -/
theorem distinct_left_endpoints {p q r s : ℝ} (hpq : p < q) (hrs : r < s)
    (hdisj : Ioo p q ∩ Ioo r s = ∅) : p ≠ r := by
  intro hpr
  subst hpr
  have hmin : p < min q s := lt_min hpq hrs
  obtain ⟨x, hx1, hx2⟩ := exists_between hmin
  have hxq : x ∈ Ioo p q := ⟨hx1, lt_of_lt_of_le hx2 (min_le_left _ _)⟩
  have hxs : x ∈ Ioo p s := ⟨hx1, lt_of_lt_of_le hx2 (min_le_right _ _)⟩
  exact absurd (hdisj ▸ Set.mem_inter hxq hxs) (Set.notMem_empty x)

/-- **No gap between consecutive edges.**  If the covered set contains all of `[a,b]`, and a point
strictly between `q` and `r` lies in `[a,b]` but in no edge, the covering fails.  Contrapositive:
under full coverage the edges meet. -/
theorem gap_forces_meet {a b q r : ℝ} (S : Set ℝ) (hcov : Icc a b ⊆ S)
    (hqr : q < r) (hsub : Ioo q r ⊆ Icc a b) (huncov : Ioo q r ∩ S = ∅) : False := by
  obtain ⟨x, hx1, hx2⟩ := exists_between hqr
  have hx : x ∈ Ioo q r := ⟨hx1, hx2⟩
  exact absurd (huncov ▸ Set.mem_inter hx (hcov (hsub hx))) (Set.notMem_empty x)

/-! ## The sort itself: a chain becomes an ordered word

With the key injective, the ordering is concrete.  Sorting the chain's *positions* (a `Finset ℝ`,
where the ambient linear order is available) and pulling back along the key gives a list whose
length is the chain's cardinality and whose entries increase.  This is the construction the
orientation word is read off; it needs no geometry beyond the two facts above. -/

/-- The positions of a chain, in increasing order. -/
noncomputable def sortedPositions {ι : Type*} (chain : Finset ι) (pos : ι → ℝ) : List ℝ :=
  open Classical in (chain.image pos).sort

/-- **The word has one letter per chain edge.**  When the key is injective on the chain, sorting
the positions loses nothing. -/
theorem sortedPositions_length {ι : Type*} [DecidableEq ι] (chain : Finset ι) (pos : ι → ℝ)
    (hinj : Set.InjOn pos chain) :
    (sortedPositions chain pos).length = chain.card := by
  classical
  rw [sortedPositions, Finset.length_sort, Finset.card_image_of_injOn hinj]

/-- **The word is ordered** — strictly, since positions are distinct in a `Finset`. -/
theorem sortedPositions_sorted {ι : Type*} (chain : Finset ι) (pos : ι → ℝ) :
    (sortedPositions chain pos).SortedLT := by
  classical
  exact Finset.sortedLT_sort _

/-- **Every chain edge appears.** -/
theorem mem_sortedPositions {ι : Type*} [DecidableEq ι] (chain : Finset ι) (pos : ι → ℝ)
    {i : ι} (hi : i ∈ chain) : pos i ∈ sortedPositions chain pos := by
  classical
  rw [sortedPositions, Finset.mem_sort]
  exact Finset.mem_image_of_mem pos hi

/-! ## Reading the edge back: the chain as an ordered list

The last step of the ordering.  Each sorted position came from a chain edge, and by injectivity
from exactly one, so mapping the sorted positions back recovers the chain in base order. -/

/-- Every sorted position comes from a chain edge. -/
theorem exists_of_mem_sortedPositions {ι : Type*} [DecidableEq ι] (chain : Finset ι) (pos : ι → ℝ)
    {p : ℝ} (hp : p ∈ sortedPositions chain pos) : ∃ i, i ∈ chain ∧ pos i = p := by
  classical
  rw [sortedPositions, Finset.mem_sort, Finset.mem_image] at hp
  obtain ⟨i, hi, hip⟩ := hp
  exact ⟨i, hi, hip⟩

open Classical in
/-- **The chain, in base order.**  The orientation word is read off this list. -/
noncomputable def orderedChain {ι : Type*} [Inhabited ι] (chain : Finset ι) (pos : ι → ℝ) :
    List ι :=
  (sortedPositions chain pos).map fun p =>
    if h : ∃ i, i ∈ chain ∧ pos i = p then h.choose else default

/-- **One entry per chain edge.** -/
theorem orderedChain_length {ι : Type*} [Inhabited ι] [DecidableEq ι]
    (chain : Finset ι) (pos : ι → ℝ) (hinj : Set.InjOn pos chain) :
    (orderedChain chain pos).length = chain.card := by
  classical
  rw [orderedChain, List.length_map, sortedPositions_length chain pos hinj]

/-- **Every entry is a chain edge**, and sits at the position it was sorted by. -/
theorem orderedChain_mem {ι : Type*} [Inhabited ι] [DecidableEq ι]
    (chain : Finset ι) (pos : ι → ℝ) {i : ι} (hi : i ∈ orderedChain chain pos) :
    i ∈ chain := by
  classical
  rw [orderedChain, List.mem_map] at hi
  obtain ⟨p, hp, hip⟩ := hi
  have hex : ∃ j, j ∈ chain ∧ pos j = p := exists_of_mem_sortedPositions chain pos hp
  rw [dif_pos hex] at hip
  exact hip ▸ hex.choose_spec.1

end Erdos634.Contiguity
