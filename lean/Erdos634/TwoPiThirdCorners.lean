/-
TwoPiThirdCorners.lean — corner structure of the 2π/3 branch targets (Erdős #634).
No imports, no axioms: kernel-checked with the core toolchain only.

SETTING. In this branch the tile has γ = 2π/3 opposite c and α + β = π/3, so

    γ = 2π/3 = 2(α+β),   i.e.   α ↦ (1,0),  β ↦ (0,1),  γ ↦ (2,2)

in coordinates (X,Y) meaning the angle X·α + Y·β. As in the other branch, α/β is irrational (a
rational ratio together with α+β = π/3 would make both rational multiples of π), so an angle has at
most one representation and a vertex figure at (X,Y) is exactly a solution in nonnegative integers of

    x + 2z = X ,    y + 2z = Y ,

with x, y, z the numbers of α-, β-, γ-corners meeting there.

THE LEMMA. A γ-corner costs one unit in BOTH coordinates twice over, so `z ≥ 1` needs `X ≥ 2` and
`Y ≥ 2`. Every corner of the six shapes in play has `min(X,Y) ≤ 1`; hence at every one of them the
vertex figure is γ-FREE and UNIQUE, namely `x = X`, `y = Y`.

The eighteen corners, in (X,Y) coordinates (each shape's three angles sum to (3,3) = π):

    iso base-α  (1,0) (1,0) (1,3)        iso base-β  (0,1) (0,1) (3,1)
    F3          (1,0) (2,0) (0,3)        F3'         (0,1) (0,2) (3,0)
    F4          (1,0) (0,2) (2,1)        F4'         (0,1) (2,0) (1,2)

CONSEQUENCE, AND ITS LIMIT. This pins the tile multiset at every corner of every one of the six
shapes, hence the flanks the corner tiles present along the two rays: an α-corner of the tile is
flanked by b and c, a β-corner by a and c, a γ-corner by a and b. It is the first step of the
exclusion of the configuration (★) of `RationalityFree.lean`. It does NOT by itself exclude (★):
on the iso base-α target, for instance, (★) asks each equal side (length a multiple of c) to be
covered by c-edges alone and the base (length a+2b) by a- and b-edges alone, and the corner data
above is consistent with that — the base corner is a single α-tile presenting c along the equal side
and b along the base, and the apex figure (1,3,0) can present c along both equal sides. Excluding
(★) therefore needs an argument beyond the corners, and none is claimed here.
-/

namespace Erdos634.TwoPiThirdCorners

/-! ## The vertex equation -/

/-- **A γ-corner needs both coordinates at least 2.** If `x + 2z = X`, `y + 2z = Y` and `z ≥ 1`
then `2 ≤ X` and `2 ≤ Y`. -/
theorem gamma_needs_two (x y z X Y : Nat) (hx : x + 2*z = X) (hy : y + 2*z = Y) (hz : 1 ≤ z) :
    2 ≤ X ∧ 2 ≤ Y := by omega

/-- **The γ-free criterion.** If `min(X,Y) ≤ 1` then every vertex figure at `(X,Y)` has `z = 0`,
and is therefore the unique figure `x = X`, `y = Y`. -/
theorem unique_figure (x y z X Y : Nat) (hx : x + 2*z = X) (hy : y + 2*z = Y)
    (hmin : X ≤ 1 ∨ Y ≤ 1) : z = 0 ∧ x = X ∧ y = Y := by omega

/-! ## The eighteen corners.  Each is an instance of `unique_figure`, so we record the hypothesis
`min(X,Y) ≤ 1` for every corner of every shape. -/

theorem corners_iso_base_alpha :
    ((1:Nat) ≤ 1 ∨ (0:Nat) ≤ 1) ∧ ((1:Nat) ≤ 1 ∨ (0:Nat) ≤ 1) ∧ ((1:Nat) ≤ 1 ∨ (3:Nat) ≤ 1) := by
  decide

theorem corners_iso_base_beta :
    ((0:Nat) ≤ 1 ∨ (1:Nat) ≤ 1) ∧ ((0:Nat) ≤ 1 ∨ (1:Nat) ≤ 1) ∧ ((3:Nat) ≤ 1 ∨ (1:Nat) ≤ 1) := by
  decide

theorem corners_F3 :
    ((1:Nat) ≤ 1 ∨ (0:Nat) ≤ 1) ∧ ((2:Nat) ≤ 1 ∨ (0:Nat) ≤ 1) ∧ ((0:Nat) ≤ 1 ∨ (3:Nat) ≤ 1) := by
  decide

theorem corners_F4 :
    ((1:Nat) ≤ 1 ∨ (0:Nat) ≤ 1) ∧ ((0:Nat) ≤ 1 ∨ (2:Nat) ≤ 1) ∧ ((2:Nat) ≤ 1 ∨ (1:Nat) ≤ 1) := by
  decide

theorem corners_F3' :
    ((0:Nat) ≤ 1 ∨ (1:Nat) ≤ 1) ∧ ((0:Nat) ≤ 1 ∨ (2:Nat) ≤ 1) ∧ ((3:Nat) ≤ 1 ∨ (0:Nat) ≤ 1) := by
  decide

theorem corners_F4' :
    ((0:Nat) ≤ 1 ∨ (1:Nat) ≤ 1) ∧ ((2:Nat) ≤ 1 ∨ (0:Nat) ≤ 1) ∧ ((1:Nat) ≤ 1 ∨ (2:Nat) ≤ 1) := by
  decide

/-! ## Angle sums: each shape's three corners sum to π = 3α+3β. -/

theorem sum_iso_base_alpha : (1+1+1 : Nat) = 3 ∧ (0+0+3 : Nat) = 3 := by decide
theorem sum_iso_base_beta : (0+0+3 : Nat) = 3 ∧ (1+1+1 : Nat) = 3 := by decide
theorem sum_F3 : (1+2+0 : Nat) = 3 ∧ (0+0+3 : Nat) = 3 := by decide
theorem sum_F4 : (1+0+2 : Nat) = 3 ∧ (0+2+1 : Nat) = 3 := by decide
theorem sum_F3' : (0+0+3 : Nat) = 3 ∧ (1+2+0 : Nat) = 3 := by decide
theorem sum_F4' : (0+2+1 : Nat) = 3 ∧ (1+0+2 : Nat) = 3 := by decide

/-! ## Corner flanks.  Encoding the tile's sides as a ↦ 0, b ↦ 1, c ↦ 2, the two sides adjacent to
a corner are the two not opposite it: α is opposite a, so an α-corner is flanked by b and c. -/

/-- α-corner: flanks b, c. -/
theorem flanks_alpha : (1, 2) = ((1:Nat), (2:Nat)) := by decide
/-- β-corner: flanks a, c. -/
theorem flanks_beta : (0, 2) = ((0:Nat), (2:Nat)) := by decide
/-- γ-corner: flanks a, b — which by `unique_figure` never occurs at a corner of these six
targets. -/
theorem flanks_gamma : (0, 1) = ((0:Nat), (1:Nat)) := by decide

end Erdos634.TwoPiThirdCorners
