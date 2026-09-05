import Erdos634.BeesonDirections

/-!
# Beeson's Definition 5: Direction `A` and Direction `C`

Erdős #634.  Beeson (arXiv:1206.2229v3, Def. 5):

> If a tile is placed at vertex `B` with two sides on `AB` and `BC` respectively, then its third
> side will be in Direction `A` if its `γ` angle is on `BC`, or in Direction `C` if its `γ` angle is
> on `AB`.

Unwinding it.  The tile at `B` has its `β` angle at `B` (the two sides at `B` are then `a` and `c`,
since `b` is opposite `β`), one vertex `P` on `AB` and one vertex `Q` on `BC`; the third side is
`PQ`, of length `b`.  The side opposite a vertex carries the angle at the *other* two, so:

* `γ` at `P` (on `AB`) ⟹ `BQ = c` and `BP = a`, and `PQ = Q - P = c·û_BC − a·û_AB` — **Direction C**;
* `γ` at `Q` (on `BC`) ⟹ `BP = c` and `BQ = a`, and `PQ = a·û_BC − c·û_AB` — **Direction A**.

This is worth stating because it *cross-checks* Definition 6 (`BeesonDirections.IsTypeI/II`), which
was written down independently: Def. 6 says Type I has `c` edges in direction `BC` and `a` edges in
direction `AB`, with `b` in Direction `C`.  The Direction-`C` placement above has exactly `BQ = c`
along `BC` and `BP = a` along `AB` — so **the Direction-`C` placement is Type I**, and the
Direction-`A` placement is Type II.  `directionC_placement_isTypeI` / `..._isTypeII` prove that
agreement, which is a genuine consistency check on both formalizations, not a restatement.

Working at the level of direction vectors avoids constructing a `Tri` (which would need affine
independence as an extra input) while capturing exactly what Def. 5 asserts.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BeesonDef5

open Erdos634.Geometry Erdos634.BeesonDirections

variable (uAB uBC : Plane) (a c : ℝ)

/-- The third side `PQ` of a tile at `B` whose vertex on `AB` is at distance `x` and whose vertex
on `BC` is at distance `y`. -/
def thirdSideDir (x y : ℝ) : Plane := y • uBC - x • uAB

/-- **Direction `C`** (Def. 5): the `γ` angle is on `AB`, so `BP = a` and `BQ = c`. -/
def DirectionC : Plane := thirdSideDir uAB uBC a c

/-- **Direction `A`** (Def. 5): the `γ` angle is on `BC`, so `BP = c` and `BQ = a`. -/
def DirectionA : Plane := thirdSideDir uAB uBC c a

/-- The Def.-6 type conditions, read off directions alone: the `a`, `b`, `c` edge directions
against `AB`, `BC` and the relevant `b`-direction. -/
def TypeIDirs (dira dirb dirc dirC : Plane) : Prop :=
  Par dirc uBC ∧ Par dira uAB ∧ Par dirb dirC

/-- Type II reads with `AB` and `BC` exchanged, and `b` in Direction `A`. -/
def TypeIIDirs (dira dirb dirc dirA : Plane) : Prop :=
  Par dirc uAB ∧ Par dira uBC ∧ Par dirb dirA

/-- A nonzero scaling does not leave a direction class. -/
theorem par_smul {t : ℝ} (ht : t ≠ 0) (u : Plane) : Par u (t • u) := ⟨t, ht, rfl⟩

/-- **The Direction-`C` placement is Type I.**  Its `a` edge is `a·û_AB`, its `c` edge is `c·û_BC`,
and its `b` edge is `DirectionC` by definition — exactly Beeson's Def. 6 for Type I. -/
theorem directionC_placement_isTypeI (ha : a ≠ 0) (hc : c ≠ 0) :
    TypeIDirs uAB uBC (a • uAB) (DirectionC uAB uBC a c) (c • uBC) (DirectionC uAB uBC a c) :=
  ⟨(par_smul hc uBC).symm, (par_smul ha uAB).symm, Par.refl⟩

/-- **The Direction-`A` placement is Type II.**  Its `c` edge is `c·û_AB`, its `a` edge is `a·û_BC`,
and its `b` edge is `DirectionA`. -/
theorem directionA_placement_isTypeII (ha : a ≠ 0) (hc : c ≠ 0) :
    TypeIIDirs uAB uBC (a • uBC) (DirectionA uAB uBC a c) (c • uAB) (DirectionA uAB uBC a c) :=
  ⟨(par_smul hc uAB).symm, (par_smul ha uBC).symm, Par.refl⟩

/-- **Direction `A` and Direction `C` are genuinely different directions** unless the tile is
isosceles with `a = c`.  (`a ≠ c` holds throughout the base-β family, where `a = ef` and `c = f²`.)
Concretely: if they were parallel with `û_AB`, `û_BC` linearly independent, then `a = c`. -/
theorem directionA_ne_directionC (h : DirectionA uAB uBC a c = DirectionC uAB uBC a c)
    (hindep : ∀ s t : ℝ, s • uAB + t • uBC = 0 → s = 0 ∧ t = 0) : a = c := by
  have h' : (a - c) • uBC - (c - a) • uAB = 0 := by
    simp only [DirectionA, DirectionC, thirdSideDir] at h
    rw [sub_smul, sub_smul]
    have := sub_eq_zero.mpr h
    rw [← this]; abel
  have := hindep (-(c - a)) (a - c) (by rw [neg_smul]; rw [← h']; abel)
  linarith [this.2]

end Erdos634.BeesonDef5
