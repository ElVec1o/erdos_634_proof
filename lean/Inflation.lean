-- Inflation.lean — the inflated tile's boundary at (1,3), and what forces it.
--
-- The base-β tile is a rep-tile: expansion by f is tiled by f² copies (companion `rem:blockbreaks`).
-- At m = 1 the west corner block IS that inflation, and its far side is the whole equal side, so
-- "is the inflation rigid?" and "is p = 0 on the west side?" are the same question. This file carries
-- the combinatorial half at (1,3), tile (3,8,9), inflated to (9,24,27).
--
-- Each corner of the inflated triangle takes a single tile (companion), and that tile's two edges
-- there are the flanks of the corner angle. Hence each side begins and ends with a prescribed edge,
-- and the middle is a word over {3,8,9} of known sum. The three lemmas below settle those middles.
--
-- SCOPE. That each corner takes one tile, and that the corner tile's edges lie along the two sides,
-- is geometric input and is NOT proved here; it is the hypothesis these arithmetic facts are applied
-- under. Per the project rule the corpus was surveyed first: `ChordDecomp` and `SecondEdge` carry
-- chord and vertex arithmetic, neither carries inflation side words.

import Mathlib.Tactic

namespace Erdos634.Inflation

/-- The three side lengths of the tile at `(1,3)`. -/
def isSide (x : ℕ) : Prop := x = 3 ∨ x = 8 ∨ x = 9

/-- Every tile side is at least `3`. -/
theorem three_le_of_isSide {x : ℕ} (h : isSide x) : 3 ≤ x := by
  rcases h with h | h | h <;> omega

/-- A word of tile sides has sum `0` or at least `3`; there is nothing in between. -/
theorem sum_zero_or_three {w : List ℕ} (h : ∀ x ∈ w, isSide x) : w.sum = 0 ∨ 3 ≤ w.sum := by
  match w with
  | [] => left; simp
  | x :: t =>
      right
      have := three_le_of_isSide (h x (by simp))
      simp only [List.sum_cons]
      omega

/-- A word of tile sides summing to `3` is a single `a`-edge.  This is the middle of the inflated
`a`-side, whose ends are `a`-edges: `3 + 3 + 3 = 9`. -/
theorem middle_three (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 3) : w = [3] := by
  match w with
  | [] => simp at hs
  | [x] => simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs; simp [hs]
  | x :: y :: t =>
      have hx := three_le_of_isSide (h x (by simp))
      have hy := three_le_of_isSide (h y (by simp))
      simp only [List.sum_cons] at hs
      omega

/-- A word of tile sides summing to `8` is a single `b`-edge.  This is the middle of the inflated
`b`-side: `8 + 8 + 8 = 24`, and no other composition exists. -/
theorem middle_eight (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 8) : w = [8] := by
  match w with
  | [] => simp at hs
  | [x] => simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs; simp [hs]
  | x :: y :: t =>
      exfalso
      have hx := h x (by simp)
      have hy := h y (by simp)
      have ht := sum_zero_or_three (w := t) (fun z hz => h z (by simp [hz]))
      simp only [List.sum_cons] at hs
      rcases hx with h'|h'|h' <;> rcases hy with h''|h''|h'' <;>
        rw [h', h''] at hs <;> omega

/-- A word of tile sides summing to `9` is `[9]` or `[3,3,3]`.  This is the middle of the inflated
`c`-side, whose ends are `c`-edges: `9 + 9 + 9 = 27` and `9 + 3 + 3 + 3 + 9 = 27`.  **Two words
survive, and this is exactly the rigidity question.** -/
theorem middle_nine (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 9) :
    w = [9] ∨ w = [3, 3, 3] := by
  match w with
  | [] => simp at hs
  | [x] => simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs; exact Or.inl (by simp [hs])
  | [x, y] =>
      exfalso
      rcases h x (by simp) with h'|h'|h' <;> rcases h y (by simp) with h''|h''|h'' <;>
        simp only [List.sum_cons, List.sum_nil, h', h''] at hs <;> omega
  | [x, y, z] =>
      right
      have hx := h x (by simp); have hy := h y (by simp); have hz := h z (by simp)
      simp only [List.sum_cons, List.sum_nil] at hs
      rcases hx with h'|h'|h' <;> rcases hy with h''|h''|h'' <;> rcases hz with h'''|h'''|h''' <;>
        simp_all <;> omega
  | x :: y :: z :: u :: t =>
      exfalso
      have hx := three_le_of_isSide (h x (by simp))
      have hy := three_le_of_isSide (h y (by simp))
      have hz := three_le_of_isSide (h z (by simp))
      have hu := three_le_of_isSide (h u (by simp))
      simp only [List.sum_cons] at hs
      omega

/-- **The two inflated `c`-side words at `(1,3)`.**  Both have length `27`; the first is the standard
subdivision, the second is the `p=1` side word `c a a a c`. -/
theorem c_side_words : ([9, 9, 9] : List ℕ).sum = 27 ∧ ([9, 3, 3, 3, 9] : List ℕ).sum = 27 := by
  constructor <;> decide

/-- The inflated `a`- and `b`-sides are rigid: `9 = 3+3+3` and `24 = 8+8+8` are their only
compositions with the prescribed end edges. -/
theorem a_b_sides_rigid : ([3, 3, 3] : List ℕ).sum = 9 ∧ ([8, 8, 8] : List ℕ).sum = 24 := by
  constructor <;> decide

end Erdos634.Inflation
