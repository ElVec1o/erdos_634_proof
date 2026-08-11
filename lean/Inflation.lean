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


/-! ## The same forcing at `(3,7)`

Tile `(21,40,49)` inflated to `(147,280,343)`, `49` copies. The residual lengths after removing the
two prescribed end edges are `105`, `200`, `245`. The first two have unique compositions; the third
has exactly two, and they are `p = 0` and `p = 1` on the equal side. -/

/-- The inflated `a`-side is rigid at `(3,7)`: `105 = 5·21` and nothing else. -/
theorem residual_105 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 105) :
    x = 5 ∧ y = 0 ∧ z = 0 := by
  have hy : y ≤ 2 := by omega
  have hz : z ≤ 2 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- The inflated `b`-side is rigid at `(3,7)`: `200 = 5·40` and nothing else. -/
theorem residual_200 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 200) :
    x = 0 ∧ y = 5 ∧ z = 0 := by
  have hy : y ≤ 5 := by omega
  have hz : z ≤ 4 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- **The inflated `c`-side at `(3,7)` has exactly two compositions**, `5·49` and `7·21 + 2·49`.
Adding the two end `c`-edges gives the whole-side profiles `(0 a, 7 c)` and `(7 a, 4 c)` --- that is,
`p = 0` and `p = 1`. This is the crux, posed on `49` tiles instead of `138`. -/
theorem residual_245 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 245) :
    (x = 0 ∧ y = 0 ∧ z = 5) ∨ (x = 7 ∧ y = 0 ∧ z = 2) := by
  have hy : y ≤ 6 := by omega
  have hz : z ≤ 5 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- Both survivors have the right length, and the whole-side profiles are `p=0` and `p=1`. -/
theorem c_side_profiles_37 :
    49 + (49 * 5) + 49 = 343 ∧ 49 + (21 * 7 + 49 * 2) + 49 = 343 := by
  constructor <;> decide

/-- The inflation is `35%` of the target at `(3,7)`: `49` tiles against `N = 138`. -/
theorem inflation_smaller_37 : 49 < 138 := by decide


/-! ## The γ-corner hypothesis is not needed

Only the `α`- and `β`-corners need be single, and both are: two tiles at the `α`-corner already exceed
`α`, and the `β`-corner would need `β/α` integral, which fails at both members. The `γ`-corner may
split as `{α,α,β}` for all we know, and it does not matter:

* the `c`-side joins the `α`- and `β`-vertices, so **both** its end edges are `c` unconditionally;
* the `a`-side has its `β`-end forced to `a`, and the residual has a unique composition;
* the `b`-side has its `α`-end forced to `b`, and likewise.

So the side words are determined without any assumption at the `γ`-corner. -/

/-- The inflated `a`-side at `(3,7)`, with only its `β`-end known: residual `126` is `6·21`. -/
theorem residual_126 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 126) :
    x = 6 ∧ y = 0 ∧ z = 0 := by
  have hy : y ≤ 3 := by omega
  have hz : z ≤ 2 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- The inflated `b`-side at `(3,7)`, with only its `α`-end known: residual `240` is `6·40`. -/
theorem residual_240 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 240) :
    x = 0 ∧ y = 6 ∧ z = 0 := by
  have hy : y ≤ 6 := by omega
  have hz : z ≤ 4 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- The same at `(1,3)`: residuals `6` and `16` over `{3,8,9}` are `2·3` and `2·8`. -/
theorem residual_13_sides (x y z : ℕ) :
    (3 * x + 8 * y + 9 * z = 6 → x = 2 ∧ y = 0 ∧ z = 0)
  ∧ (3 * x + 8 * y + 9 * z = 16 → x = 0 ∧ y = 2 ∧ z = 0) := by
  constructor <;> intro h <;> [skip; skip] <;>
    (have hy : y ≤ 2 := by omega
     have hz : z ≤ 1 := by omega
     interval_cases y <;> interval_cases z <;> omega)

end Erdos634.Inflation
