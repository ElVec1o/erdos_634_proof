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

end Erdos634.Contiguity
