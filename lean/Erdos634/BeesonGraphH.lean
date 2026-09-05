import Erdos634.BeesonDirections
import Erdos634.TilePlacement

/-!
# Beeson's Definition 3: the component graph `H`

Erdős #634.  Beeson (arXiv:1206.2229v3, Def. 3):

> The graph `H` has for its nodes the tiles used in the tiling, and its edges (connections) are
> defined as follows: Tiles `T` and `S` are connected if `T` and `S` share two vertices (and hence
> the edge between those vertices), and `S` and `T` do **not** have the same angles at the vertices
> of their shared side.  A connected component, or just a component, of a tiling is a maximal
> connected set in the graph `H`.

The negative clause is load-bearing and Beeson flags it explicitly: with the weaker "same-length
edges on a common segment" notion of connection, Fig. 4 would have three components instead of
four, and "it will turn out to be important that they not be connected".  So the definition is
formalized here with that clause intact.

Two tiles can meet along their shared side with either orientation, so `SharesSide` comes in a
direct and a reversed form, and the angle comparison follows the same matching.

Provided here: the relation `HAdj`, its symmetry and irreflexivity, the component relation as the
reflexive–transitive closure (`HConn`, an equivalence), and `hAdj_shared_side_ne` recording that a
shared side is a genuine segment.  **Not** provided: Lemma 13/14 (a connected pair forms a
parallelogram, hence components are lattice tilings), which needs the angle-to-side correspondence,
and Def. 7's out-of-sync relation.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BeesonGraphH

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

/-- `T` and `S` share the side `kT` / `kS`, endpoints matched in order. -/
def SharesSide (T S : Tri) (kT kS : Fin 3) : Prop :=
  T.pts kT = S.pts kS ∧ T.pts (kT + 1) = S.pts (kS + 1)

/-- `T` and `S` share the side `kT` / `kS`, endpoints matched in reverse. -/
def SharesSideRev (T S : Tri) (kT kS : Fin 3) : Prop :=
  T.pts kT = S.pts (kS + 1) ∧ T.pts (kT + 1) = S.pts kS

/-- The two tiles present the same angles at both ends of the shared side (order-matched). -/
def SameAngles (T S : Tri) (kT kS : Fin 3) : Prop :=
  angleAt T kT = angleAt S kS ∧ angleAt T (kT + 1) = angleAt S (kS + 1)

/-- Same, for the reversed matching. -/
def SameAnglesRev (T S : Tri) (kT kS : Fin 3) : Prop :=
  angleAt T kT = angleAt S (kS + 1) ∧ angleAt T (kT + 1) = angleAt S kS

/-- **Beeson's `H`-adjacency.**  Share a side, and *not* with the same angles at its two ends. -/
def HAdj (D : Dissection N) (i j : Fin N) : Prop :=
  i ≠ j ∧ ∃ kT kS : Fin 3,
    (SharesSide (D.tile i) (D.tile j) kT kS ∧ ¬ SameAngles (D.tile i) (D.tile j) kT kS) ∨
    (SharesSideRev (D.tile i) (D.tile j) kT kS ∧ ¬ SameAnglesRev (D.tile i) (D.tile j) kT kS)

theorem hAdj_irrefl (D : Dissection N) (i : Fin N) : ¬ HAdj D i i := fun h => h.1 rfl

/-- `H`-adjacency is symmetric: swapping the roles swaps the matching, and the reversed matching is
its own mirror. -/
theorem hAdj_symm (D : Dissection N) {i j : Fin N} (h : HAdj D i j) : HAdj D j i := by
  obtain ⟨hij, kT, kS, hcase⟩ := h
  refine ⟨hij.symm, kS, kT, ?_⟩
  rcases hcase with ⟨⟨h1, h2⟩, hne⟩ | ⟨⟨h1, h2⟩, hne⟩
  · exact Or.inl ⟨⟨h1.symm, h2.symm⟩, fun hs => hne ⟨hs.1.symm, hs.2.symm⟩⟩
  · exact Or.inr ⟨⟨h2.symm, h1.symm⟩, fun hs => hne ⟨hs.2.symm, hs.1.symm⟩⟩

/-- A shared side is a genuine segment: its two endpoints are distinct. -/
theorem hAdj_shared_side_ne (D : Dissection N) (i : Fin N) (k : Fin 3) :
    (D.tile i).pts k ≠ (D.tile i).pts (k + 1) :=
  pts_ne (D.tile i) (by revert k; decide)

/-! ## Components -/

/-- **Connectivity in `H`**: the reflexive–transitive closure of `HAdj`.  A *component* is an
equivalence class of this relation — "a maximal connected set in the graph `H`". -/
def HConn (D : Dissection N) : Fin N → Fin N → Prop := Relation.ReflTransGen (HAdj D)

theorem hConn_refl (D : Dissection N) (i : Fin N) : HConn D i i := Relation.ReflTransGen.refl

theorem hConn_trans (D : Dissection N) {i j k : Fin N} (h1 : HConn D i j) (h2 : HConn D j k) :
    HConn D i k := Relation.ReflTransGen.trans h1 h2

theorem hConn_symm (D : Dissection N) {i j : Fin N} (h : HConn D i j) : HConn D j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single
      (hAdj_symm D hstep)) ih

/-- **Components partition the tiles**: `HConn` is an equivalence relation. -/
theorem hConn_equivalence (D : Dissection N) : Equivalence (HConn D) :=
  ⟨hConn_refl D, fun h => hConn_symm D h, fun h1 h2 => hConn_trans D h1 h2⟩

/-- An adjacent pair is connected. -/
theorem hConn_of_hAdj (D : Dissection N) {i j : Fin N} (h : HAdj D i j) : HConn D i j :=
  Relation.ReflTransGen.single h

end Erdos634.BeesonGraphH
