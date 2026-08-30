import Erdos634.Contiguity

/-!
# A sorted cover has no gap: the chain reaches the next edge

Erdős #634, bridge (c).  `Contiguity` builds the ordered chain from an injective key, and
`EdgeDisjoint` supplies the pairwise disjointness the key needs.  What was left is the *global*
half: that the edges, taken in order of left endpoint, actually cover the base contiguously —
that the reach of the first `k+1` edges is at least the left endpoint of the next.

The statement is elementary once phrased over `ℝ`, and it is exactly what the march induction
consumes: it is what says the next junction of the run is where the previous edge ended.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ChainOrder

open Set

/-- **A sorted cover has no gap.**  Closed intervals `[L j, R j]`, `j < n`, sorted by left
endpoint, covering `[a, b]` and contained in it.  If every one of the first `k+1` intervals stops
at or before `c`, and `c` is strictly left of the next interval's left endpoint, the cover fails:
a point of `(c, L (k+1))` lies in `[a, b]` and in no interval.

Contrapositive, and the form the chain uses: **the reach of the first `k+1` edges is at least
`L (k+1)`** — consecutive edges of the chain meet, with no uncovered stretch between them. -/
theorem no_gap_in_sorted_cover (n : ℕ) (L R : ℕ → ℝ) (a b c : ℝ) (k : ℕ) (hk1 : k + 1 < n)
    (hnd : ∀ j < n, L j ≤ R j)
    (hcov : Icc a b ⊆ ⋃ j ∈ Finset.range n, Icc (L j) (R j))
    (hsub : ∀ j, j < n → Icc (L j) (R j) ⊆ Icc a b)
    (hsorted : ∀ i j, i ≤ j → j < n → L i ≤ L j)
    (hreach : ∀ j ≤ k, R j ≤ c) (hlt : c < L (k + 1)) : False := by
  have hk : k < n := by omega
  -- a witness in the gap
  obtain ⟨y, hy1, hy2⟩ := exists_between hlt
  -- `y` lies in the base interval
  have hLk1 : Icc (L (k + 1)) (R (k + 1)) ⊆ Icc a b := hsub (k + 1) hk1
  have hmem1 : L (k + 1) ∈ Icc a b := hLk1 ⟨le_refl _, hnd (k + 1) hk1⟩
  have hmemk : L k ∈ Icc a b := (hsub k hk) ⟨le_refl _, hnd k hk⟩
  have hay : a ≤ y := le_trans hmemk.1 (le_trans (le_trans (hnd k hk) (hreach k (le_refl k)))
    (le_of_lt hy1))
  have hyb : y ≤ b := le_trans (le_of_lt hy2) hmem1.2
  -- so some interval contains it
  obtain ⟨s, hs, hys⟩ := Set.mem_iUnion₂.mp (hcov ⟨hay, hyb⟩)
  have hsn : s < n := Finset.mem_range.mp hs
  -- an early interval stops before `y`, a late one starts after it
  rcases le_or_gt s k with hsk | hsk
  · exact absurd hys.2 (not_le.mpr (lt_of_le_of_lt (hreach s hsk) hy1))
  · have : L (k + 1) ≤ L s := hsorted (k + 1) s hsk hsn
    exact absurd hys.1 (not_le.mpr (lt_of_lt_of_le hy2 this))

/-- **The reach statement, positively.**  Under the same hypotheses, some one of the first `k+1`
edges reaches at least as far as the next edge's left endpoint. -/
theorem reach_next (n : ℕ) (L R : ℕ → ℝ) (a b : ℝ) (k : ℕ) (hk1 : k + 1 < n)
    (hnd : ∀ j < n, L j ≤ R j)
    (hcov : Icc a b ⊆ ⋃ j ∈ Finset.range n, Icc (L j) (R j))
    (hsub : ∀ j, j < n → Icc (L j) (R j) ⊆ Icc a b)
    (hsorted : ∀ i j, i ≤ j → j < n → L i ≤ L j) :
    ∃ j ≤ k, L (k + 1) ≤ R j := by
  by_contra hcon
  push_neg at hcon
  -- the largest reach among the first `k+1`
  classical
  obtain ⟨m, hm, hmax⟩ : ∃ m ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1), R j ≤ R m :=
    Finset.exists_max_image (Finset.range (k + 1)) R ⟨0, by simp⟩
  have hmk : m ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hm
  refine no_gap_in_sorted_cover n L R a b (R m) k hk1 hnd hcov hsub hsorted
    (fun j hj => hmax j (Finset.mem_range.mpr (by omega))) (hcon m hmk)

/-- **Non-vacuity.**  The hypothesis set of `reach_next` is inhabited: two edges `[0,1]` and
`[1,2]` covering `[0,2]`.  So `no_gap_in_sorted_cover`, whose conclusion is `False`, refutes the
gap rather than reading `False → False`. -/
theorem cover_witness :
    Icc (0:ℝ) 2 ⊆ ⋃ j ∈ Finset.range 2, Icc ((![0, 1] : Fin 2 → ℝ) ⟨j % 2, by omega⟩)
      ((![1, 2] : Fin 2 → ℝ) ⟨j % 2, by omega⟩) := by
  intro x hx
  rcases le_or_gt x 1 with h | h
  · exact Set.mem_iUnion₂.mpr ⟨0, by simp, by simpa using ⟨hx.1, h⟩⟩
  · exact Set.mem_iUnion₂.mpr ⟨1, by simp, by simpa using ⟨le_of_lt h, hx.2⟩⟩

end Erdos634.ChainOrder
