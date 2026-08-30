import Erdos634.BaseSelection

/-!
# An edge touching the wall in its interior lies along the wall

Erdős #634, bridge (c), the last step of the selection.  `BaseSelection.frontier_subset_edges` says
every point of the target's frontier is on some tile edge, but not that the edge lies *along* the
base: a priori it could cross it.  It cannot, and the reason is an inequality rather than geometry.

The target lies in a closed half-plane bounded by the line of its base, so an affine functional `g`
cutting that line attains its maximum `c` on the whole target.  An edge with an interior point on
the line has `g = c` at an interior point of a segment on which `g ≤ c`; an affine function on a
segment attaining its maximum in the interior is constant there.  So both endpoints lie on the
line, and the edge lies along the wall.

That is what makes the base chain a chain of intervals rather than an arbitrary family of edges.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WallEdges

open Erdos634.Geometry

/-- **An affine function on a segment attaining its bound strictly inside is constant.** -/
theorem endpoints_of_interior_max (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (p q : Plane) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hp : g p ≤ c) (hq : g q ≤ c)
    (hx : g (AffineMap.lineMap p q t) = c) :
    g p = c ∧ g q = c := by
  rw [AffineMap.apply_lineMap] at hx
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] at hx
  constructor <;> nlinarith

/-- **The wall lemma.**  If a tile edge has a point of the open wall line in its relative interior,
both its endpoints lie on that line: the edge lies along the wall.

`hwall` is the half-plane containment — the whole target on one side of the base line, which is
what makes the base a side of the target rather than a chord. -/
theorem edge_along_wall {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c)
    (i : Fin N) (k : Fin 3) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hx : g (AffineMap.lineMap ((D.tile i).pts k) ((D.tile i).pts (k + 1)) t) = c) :
    g ((D.tile i).pts k) = c ∧ g ((D.tile i).pts (k + 1)) = c := by
  have hsub := Erdos634.BaseSelection.tile_subset_target D i
  have hmem : ∀ j : Fin 3, (D.tile i).pts j ∈ (D.tile i).carrier := by
    intro j
    rw [Tri.carrier]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  have hp : g ((D.tile i).pts k) ≤ c := hwall _ (hsub (hmem k))
  have hq : g ((D.tile i).pts (k + 1)) ≤ c := hwall _ (hsub (hmem (k + 1)))
  exact endpoints_of_interior_max g c _ _ t ht0 ht1 hp hq hx

end Erdos634.WallEdges
