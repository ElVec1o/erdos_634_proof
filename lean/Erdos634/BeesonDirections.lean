import Erdos634.Dissection
import Erdos634.TilePlacement

/-!
# The direction layer: parallelism classes, and Beeson's Type I / Type II

Erdős #634.  Beeson's Definitions 5–7 (arXiv:1206.2229v3) — and therefore both geometric parts of
his Theorem 2 — are stated entirely in the vocabulary of **directions**: "a direction is given by an
equivalence class of parallel lines", and

> Type I: `c` edges have direction `BC`, `a` edges have direction `AB`, and `b` edges have
> Direction `C`.  Type II: `c` edges have direction `AB`, `a` edges have direction `BC`, and `b`
> edges have Direction `A`.

`DirectionGroup.lean` develops the *angle* side of this (directions lie in one coset of `⟨α,β⟩` in
`ℝ/πℤ`).  The *geometric* side — parallelism of actual tile edges — was missing.  This file builds
it: `Par` on direction vectors, its equivalence properties, `EdgeDir` for a tile side, and the
Type I / Type II predicates as Beeson states them.

The first real consequence is `typeI_typeII_disjoint`: a tile cannot be both, because that would
force `AB ∥ BC` and collapse the target to a line.  This is used silently throughout §6.1 (a tile at
`B` "is either Type I or Type II" — exclusively).

**Scope.**  This is the vocabulary, not the theorem.  Beeson's components (the connectivity graph
`H`), out-of-sync components (Def. 7), the region `Ω` (Def. 11), arrows (Def. 12) and boundary
segments (Def. 13) are still unbuilt, and with them Theorem 2's parts 1 and 3.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BeesonDirections

open Erdos634.Geometry

/-- Two direction vectors are **parallel** if one is a nonzero multiple of the other. -/
def Par (u v : Plane) : Prop := ∃ t : ℝ, t ≠ 0 ∧ v = t • u

theorem Par.refl {u : Plane} : Par u u := ⟨1, one_ne_zero, (one_smul ℝ u).symm⟩

theorem Par.symm {u v : Plane} (h : Par u v) : Par v u := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t⁻¹, inv_ne_zero ht, by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]⟩

theorem Par.trans {u v w : Plane} (h1 : Par u v) (h2 : Par v w) : Par u w := by
  obtain ⟨t, ht, rfl⟩ := h1
  obtain ⟨s, hs, rfl⟩ := h2
  exact ⟨s * t, mul_ne_zero hs ht, by rw [smul_smul]⟩

/-- Reversing a segment does not change its direction class. -/
theorem Par.neg (u : Plane) : Par u (-u) := ⟨-1, by norm_num, by simp⟩

/-- The direction vector of side `k` of a triangle. -/
def EdgeDir (T : Tri) (k : Fin 3) : Plane := T.pts (k + 1) - T.pts k

/-! ## Beeson's Definition 6 -/

/-- **Type I** (Beeson Def. 6): the `c` edge has direction `BC`, the `a` edge has direction `AB`.
(The `b` edge's direction is then forced — it is what Def. 5 calls Direction `C`.) -/
def IsTypeI (T : Tri) (ka kc : Fin 3) (A B C : Plane) : Prop :=
  Par (EdgeDir T kc) (C - B) ∧ Par (EdgeDir T ka) (B - A)

/-- **Type II** (Beeson Def. 6): the `c` edge has direction `AB`, the `a` edge has direction `BC`. -/
def IsTypeII (T : Tri) (ka kc : Fin 3) (A B C : Plane) : Prop :=
  Par (EdgeDir T kc) (B - A) ∧ Par (EdgeDir T ka) (C - B)

/-! ## The two types are exclusive -/

/-- Parallel `AB` and `BC` force `A`, `B`, `C` collinear. -/
theorem collinear_of_par {A B C : Plane} (h : Par (B - A) (C - B)) :
    Collinear ℝ ({A, B, C} : Set Plane) := by
  obtain ⟨t, _, ht⟩ := h
  rw [collinear_iff_of_mem (show B ∈ ({A, B, C} : Set Plane) by simp)]
  refine ⟨B - A, fun p hp => ?_⟩
  rcases hp with rfl | rfl | rfl
  · exact ⟨-1, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨t, by rw [vadd_eq_add, ← ht]; abel⟩

/-- **A tile is not both Type I and Type II.**  Beeson's §6.1 uses this exclusivity from its first
paragraph ("that tile is either Type I or Type II"); it holds because both types together make the
tile's `a` edge parallel to `AB` and to `BC`. -/
theorem typeI_typeII_disjoint (T : Tri) (ka kc : Fin 3) (A B C : Plane)
    (hncol : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (h1 : IsTypeI T ka kc A B C) (h2 : IsTypeII T ka kc A B C) : False :=
  hncol (collinear_of_par (h1.2.symm.trans h2.2))

/-- Non-vacuity: `IsTypeI` is satisfiable.  Any triangle whose `c` and `a` edges are literally the
segments `BC` and `AB` is Type I. -/
theorem isTypeI_witness (T : Tri) (ka kc : Fin 3) (A B C : Plane)
    (hc : EdgeDir T kc = C - B) (ha : EdgeDir T ka = B - A) : IsTypeI T ka kc A B C :=
  ⟨hc ▸ Par.refl, ha ▸ Par.refl⟩

/-- The direction of a nondegenerate side is nonzero — the parallelism classes above are classes of
genuine directions, not of the zero vector. -/
theorem edgeDir_ne_zero (T : Tri) (k : Fin 3) : EdgeDir T k ≠ 0 := by
  rw [EdgeDir, sub_ne_zero]
  exact Erdos634.TilePlacement.pts_ne T (by revert k; decide)

end Erdos634.BeesonDirections
