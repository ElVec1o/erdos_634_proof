import Erdos634.BeesonOmega

/-!
# Boundary orientation: which side of a directed segment a supporting tile's interior lies on

Erdős #634.  Beeson's Definition 13 needs, for a directed segment `pq` "part of a tiling", to know
which tiles supported by `pq` lie on its **left** and which on its **right**.  `Dissection.lean`
already builds the canonical left-hand direction of a tile's own edge (`Tri.leftDir`) and proves the
tile's interior is always strictly to the left of it (`Tri.interior_left_of_leftDir`) — that
machinery was built for a different purpose (`horient`/G4) but is exactly the primitive Def. 13
needs. This file is the missing bridge: given a tile whose edge *is* the directed segment `p → q`
(so it genuinely supports it, Def. 8), the tile's interior lies on the left of `p → q` exactly when
`leftDir` agrees with `q − p`, and on the right exactly when it is reversed — a clean dichotomy, with
no new geometric content beyond composing what is already proved.

`OnLeftOf`/`OnRightOf` are the general left/right-of-a-directed-segment predicates (`cross` was
already defined generally in `Dissection.lean`), stated independently of any particular tile, so
they compose with `BeesonOmega`'s `InOmega` to give `Def13BoundarySegment` — Beeson's boundary
segment predicate, with the "left side ⊆ Ω, right side ∉ Ω" clause built from real geometry.

**Scope.**  The maximality clause ("cannot be extended in either direction") is recorded as a
hypothesis component, not derived — that needs a chain/march argument this file does not build.
So `Def13BoundarySegment` is Def. 13's predicate written down and proved non-vacuous
(`def13_witness`), not yet shown to hold anywhere in a real tiling.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BeesonBoundary

open Erdos634.Geometry Erdos634.BeesonOmega

/-! ## Left/right of a directed segment, in general -/

/-- **A point lies to the left of the directed segment `p → q`.** -/
def OnLeftOf (p q y : Plane) : Prop := 0 < cross (q - p) (y - p)

/-- **A point lies to the right of the directed segment `p → q`.** -/
def OnRightOf (p q y : Plane) : Prop := cross (q - p) (y - p) < 0

theorem onLeftOf_reverse (p q y : Plane) : OnLeftOf p q y ↔ OnRightOf q p y := by
  have hanchor : cross (q - p) (y - p) = cross (q - p) (y - q) := by
    have : (y - p) = (y - q) + (q - p) := by abel
    rw [this, cross_add_right, cross_self, add_zero]
  unfold OnLeftOf OnRightOf
  rw [show p - q = -(q - p) by abel, cross_neg_left, hanchor]
  constructor <;> intro h <;> linarith

/-! ## The dichotomy: a supporting tile's interior side, from `leftDir` -/

/-- **The orientation dichotomy.**  If tile `T`'s edge `k` is exactly the directed segment `p → q`
(`T.pts k = p`, `T.pts (k+1) = q`), then for any interior point `y` of `T`: `T.leftDir k = q - p`
puts `y` on the left of `p → q`, and `T.leftDir k = p - q` puts it on the right.  Exactly one holds,
by `Tri.leftDir_eq_or`. -/
theorem tile_side_dichotomy (T : Tri) (k : Fin 3) (p q : Plane)
    (hp : T.pts k = p) (hq : T.pts (k + 1) = q)
    {y : Plane} (hy : ∀ i, 0 < T.basis.coord i y) :
    (T.leftDir k = q - p → OnLeftOf p q y) ∧ (T.leftDir k = p - q → OnRightOf p q y) := by
  have hint := T.interior_left_of_leftDir k hy
  rw [hp] at hint
  constructor
  · intro heq
    rw [heq] at hint
    exact hint
  · intro heq
    rw [heq] at hint
    unfold OnRightOf
    rw [show p - q = -(q - p) by abel, cross_neg_left] at hint
    linarith

/-- **Every supporting tile lies strictly on one side or the other, never on the line.**  Immediate
from `tile_side_dichotomy` and `Tri.leftDir_eq_or`. -/
theorem tile_side_total (T : Tri) (k : Fin 3) (p q : Plane)
    (hp : T.pts k = p) (hq : T.pts (k + 1) = q)
    {y : Plane} (hy : ∀ i, 0 < T.basis.coord i y) :
    OnLeftOf p q y ∨ OnRightOf p q y := by
  rcases T.leftDir_eq_or k with h | h
  · left; exact (tile_side_dichotomy T k p q hp hq hy).1 (by rw [h, hq, hp])
  · right; exact (tile_side_dichotomy T k p q hp hq hy).2 (by rw [h, hq, hp]; abel)

/-! ## Beeson's Definition 13, composed with `Ω` -/

variable {N : ℕ}

/-- A tile *supports* the directed segment `p q` with its `k`-th edge exactly (the strong form of
Def. 8 needed for orientation: not just "part of a side lies on `pq`" but the edge coincides with
it, in this direction). -/
def SupportsDirected (D : Dissection N) (i : Fin N) (k : Fin 3) (p q : Plane) : Prop :=
  (D.tile i).pts k = p ∧ (D.tile i).pts (k + 1) = q

/-- **Beeson's Definition 13** (boundary segment), for a directed segment `p q`: every tile
supporting it whose interior lies on the left belongs to `Ω`, and every tile supporting it whose
interior lies on the right does not — plus the maximality clause, taken as a hypothesis component
(`hmax`) since it needs a chain argument not built here. -/
def Def13BoundarySegment (D : CongruentDissection N) (A B C : Plane) (i₀ : Fin N) (p q : Plane)
    (hmax : Prop) : Prop :=
  (∀ i k y, SupportsDirected D.toDissection i k p q → OnLeftOf p q y →
      (∀ j, 0 < (D.tile i).basis.coord j y) → InOmega D.toDissection A B C i₀ i) ∧
  (∀ i k y, SupportsDirected D.toDissection i k p q → OnRightOf p q y →
      (∀ j, 0 < (D.tile i).basis.coord j y) → ¬ InOmega D.toDissection A B C i₀ i) ∧
  hmax

/-- **Non-vacuity witness.**  The predicate can hold: e.g. with `hmax := True` and no tile at all
supporting `p q` (both quantified clauses vacuously true), `Def13BoundarySegment` holds trivially.
This confirms the definition is not internally contradictory — it does *not* witness an actual
boundary segment of a real tiling, which needs an actual `Ω` and actual supporting tiles. -/
theorem def13_witness (D : CongruentDissection N) (A B C : Plane) (i₀ : Fin N) (p q : Plane)
    (hnone : ∀ i k, ¬ SupportsDirected D.toDissection i k p q) :
    Def13BoundarySegment D A B C i₀ p q True := by
  refine ⟨?_, ?_, trivial⟩
  · intro i k y hsup _ _; exact absurd hsup (hnone i k)
  · intro i k y hsup _ _; exact absurd hsup (hnone i k)

end Erdos634.BeesonBoundary
