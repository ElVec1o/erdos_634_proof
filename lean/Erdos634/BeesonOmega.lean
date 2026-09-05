import Erdos634.BeesonDirections
import Erdos634.BeesonGraphH

/-!
# Beeson's Definition 11: the region `Ω`

Erdős #634 (arXiv:1206.2229v3, Def. 11, quoted verbatim against the source):

> Given a tiling of triangle `ABC`, with angle `β` at `B` filled by just one tile, we define `Ω` to
> be the set of all (closed) Type I and Type II tiles that contains `B` and such that each tile in
> `Ω` can be connected to `B` by a chain of Type I and Type II tiles, each sharing (part of) an edge
> with the next.

This is **not** `BeesonGraphH`'s graph `H`: `H`-adjacency (Def. 3) *excludes* pairs presenting the
same angles at their shared side, which is exactly what lets two out-of-sync components stay
disconnected (Beeson's own point in Def. 7's remark).  `Ω`'s adjacency has no such exclusion — any
two Type I/II tiles sharing part of an edge are `Ω`-adjacent.  So `Ω` is formalized here as its own
relation, built the same way `BeesonGraphH.HConn` was (a `ReflTransGen` closure), but over a
different base adjacency.

`IsTypeIOrII` packages `BeesonDirections`'s `IsTypeI`/`IsTypeII` as an existential over which of a
tile's three edges plays the `a`/`c` role.  `SharesEdgePart` is Beeson's "sharing (part of) an edge"
— two tiles whose edges meet in more than a single point, i.e. in a genuine sub-segment.

**Scope.**  This formalizes the *object* `Ω` and its immediate closure properties (every member is
Type I or II, `Ω` is connected by construction).  It does **not** touch the boundary of `Ω`
(Def. 13), arrows (Def. 12), or the traversal argument (Theorem 2's parts 1 and 3) — those still
need an orientation/left-right convention on `Ω`'s boundary that this file does not build.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BeesonOmega

open Erdos634.Geometry Erdos634.BeesonDirections Erdos634.BeesonGraphH

variable {N : ℕ}

/-- **A tile is Type I or Type II** (Beeson's "that tile is either Type I or Type II"), for *some*
choice of which two edges play the tile's `a`/`c` roles. -/
def IsTypeIOrII (D : Dissection N) (i : Fin N) (A B C : Plane) : Prop :=
  ∃ ka kc : Fin 3, IsTypeI (D.tile i) ka kc A B C ∨ IsTypeII (D.tile i) ka kc A B C

/-- **Two tiles share part of an edge**: some edge of each meets the other in two distinct points,
hence in a genuine sub-segment rather than at most a vertex. -/
def SharesEdgePart (D : Dissection N) (i j : Fin N) : Prop :=
  ∃ (k l : Fin 3) (x y : Plane), x ≠ y ∧
    x ∈ (D.tile i).edge k ∧ y ∈ (D.tile i).edge k ∧
    x ∈ (D.tile j).edge l ∧ y ∈ (D.tile j).edge l

/-- **`Ω`-adjacency** (Def. 11's chain step): both tiles Type I or II, sharing part of an edge. -/
def OmegaAdj (D : Dissection N) (A B C : Plane) (i j : Fin N) : Prop :=
  IsTypeIOrII D i A B C ∧ IsTypeIOrII D j A B C ∧ SharesEdgePart D i j

/-- **`Ω` itself**: the tiles reachable from the corner tile `i₀` at `B` by a chain of
`OmegaAdj`-steps.  (`i₀` is Type I or II by hypothesis at every use site — Beeson's argument
establishes this as its very first step, before `Ω` is even defined.) -/
def InOmega (D : Dissection N) (A B C : Plane) (i₀ i : Fin N) : Prop :=
  Relation.ReflTransGen (OmegaAdj D A B C) i₀ i

theorem inOmega_refl (D : Dissection N) (A B C : Plane) (i₀ : Fin N) : InOmega D A B C i₀ i₀ :=
  Relation.ReflTransGen.refl

theorem inOmega_trans (D : Dissection N) (A B C : Plane) {i₀ i j : Fin N}
    (h1 : InOmega D A B C i₀ i) (h2 : InOmega D A B C i j) : InOmega D A B C i₀ j :=
  Relation.ReflTransGen.trans h1 h2

/-- **`Ω`-adjacency is symmetric.** -/
theorem omegaAdj_symm (D : Dissection N) (A B C : Plane) {i j : Fin N}
    (h : OmegaAdj D A B C i j) : OmegaAdj D A B C j i := by
  obtain ⟨hi, hj, k, l, x, y, hxy, hxik, hyik, hxjl, hyjl⟩ := h
  exact ⟨hj, hi, l, k, x, y, hxy, hxjl, hyjl, hxik, hyik⟩

/-- **`Ω` is symmetric as a reachability relation**: if `i` is reachable from `i₀`, then `i₀` is
reachable from `i`.  (Beeson: "`Ω` is a connected set, since any two tiles in `Ω` can be connected
to [each other]".) -/
theorem inOmega_symm (D : Dissection N) (A B C : Plane) {i₀ i : Fin N}
    (h : InOmega D A B C i₀ i) : InOmega D A B C i i₀ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (omegaAdj_symm D A B C hstep)) ih

/-- **Every member of `Ω` is Type I or Type II**, provided the seed `i₀` is. -/
theorem inOmega_isTypeIOrII (D : Dissection N) (A B C : Plane) {i₀ i : Fin N}
    (hi₀ : IsTypeIOrII D i₀ A B C) (h : InOmega D A B C i₀ i) : IsTypeIOrII D i A B C := by
  induction h with
  | refl => exact hi₀
  | tail _ hstep _ => exact hstep.2.1

/-- **`Ω` is connected**: any two of its members are joined through the seed `i₀`, hence through
each other. -/
theorem inOmega_connected (D : Dissection N) (A B C : Plane) {i₀ i j : Fin N}
    (hi : InOmega D A B C i₀ i) (hj : InOmega D A B C i₀ j) :
    Relation.ReflTransGen (OmegaAdj D A B C) i j :=
  inOmega_trans D A B C (inOmega_symm D A B C hi) hj

end Erdos634.BeesonOmega
