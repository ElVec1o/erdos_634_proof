import Erdos634.Dissection
import Erdos634.AngleSumDissection
import Erdos634.BaseSelection

/-!
# The tile-placement layer, first primitive: `tileAt`

Erdős #634.  Four blockers recur across the formalization debt (`PAPER_MAP.md`'s foot): no
tile-placement layer, no scale/composition map, no certified-search format, no dual-graph
development. This file starts the first and highest-leverage of the four: ~31 `PROVED` statements
name it directly.

The layer needs, at minimum: given a point of the target, *the* tile covering it, and a proof this
is well-defined off a measure-zero set (the union of all tile frontiers). That is `tileAt` below —
existence unconditionally, uniqueness off the bad set. Everything downstream ('the tile at a
corner', 'matched by exactly one tile', 'the corner tile's base edge') is a further layer on top of
this one; this file does not attempt them.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Existence -/

/-- **Every point of the target lies in some tile.**  Immediate from `covers`. -/
theorem exists_tile_mem (D : Dissection N) {p : Plane} (hp : p ∈ D.target.carrier) :
    ∃ i, p ∈ (D.tile i).carrier := by
  rw [← D.covers] at hp
  simpa using hp

/-! ## The bad set: where more than one tile can cover a point -/

/-- **The frontier set.**  The union of all tile frontiers — the only place two tiles' carriers
can meet, since their interiors are pairwise disjoint by `interiors_disjoint`. It has measure
zero, so it is negligible for every measure-theoretic argument, but a single point of a real
dissection can certainly lie on it (an edge or vertex of the dissection). -/
def badSet (D : Dissection N) : Set Plane := ⋃ i, frontier (D.tile i).carrier

theorem volume_badSet (D : Dissection N) : MeasureTheory.volume D.badSet = 0 :=
  (MeasureTheory.measure_iUnion_null_iff).mpr (fun i => (D.tile i).volume_frontier)

/-- **Off the bad set, the covering tile is unique.**  If `p` lies in two tiles' carriers and in
neither tile's frontier, the two tiles' interiors both contain `p`, so `interiors_disjoint` forces
them equal. -/
theorem tile_unique_of_not_mem_badSet (D : Dissection N) {p : Plane} (hbad : p ∉ D.badSet)
    {i j : Fin N} (hi : p ∈ (D.tile i).carrier) (hj : p ∈ (D.tile j).carrier) : i = j := by
  by_contra hij
  have hfi : p ∉ frontier (D.tile i).carrier := fun h => hbad (Set.mem_iUnion.mpr ⟨i, h⟩)
  have hfj : p ∉ frontier (D.tile j).carrier := fun h => hbad (Set.mem_iUnion.mpr ⟨j, h⟩)
  have hii : p ∈ interior (D.tile i).carrier := by
    by_contra hnot
    exact hfi ⟨subset_closure hi, hnot⟩
  have hjj : p ∈ interior (D.tile j).carrier := by
    by_contra hnot
    exact hfj ⟨subset_closure hj, hnot⟩
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hii hjj

/-! ## `tileAt`: the covering tile, off the bad set -/

/-- **The tile covering `p`.**  Defined for every `p` in the target via `exists_tile_mem`
(choice); its defining property (`tileAt_mem`) holds unconditionally, but it only deserves the
name "the" tile — i.e. only agrees with *every* witnessing tile — off `badSet`
(`tileAt_eq_of_mem`). This is the placement layer's first primitive: a function from points of
the target to tiles, everywhere the notion is defined at all. -/
noncomputable def tileAt (D : Dissection N) {p : Plane} (hp : p ∈ D.target.carrier) : Fin N :=
  (D.exists_tile_mem hp).choose

theorem tileAt_mem (D : Dissection N) {p : Plane} (hp : p ∈ D.target.carrier) :
    p ∈ (D.tile (D.tileAt hp)).carrier :=
  (D.exists_tile_mem hp).choose_spec

/-- **Off the bad set, `tileAt` is *the* tile: any witness agrees with it.** -/
theorem tileAt_eq_of_mem (D : Dissection N) {p : Plane} (hp : p ∈ D.target.carrier)
    (hbad : p ∉ D.badSet) {i : Fin N} (hi : p ∈ (D.tile i).carrier) : D.tileAt hp = i :=
  D.tile_unique_of_not_mem_badSet hbad (D.tileAt_mem hp) hi

/-- **`tileAt` is independent of the membership proof, off the bad set.**  Two proofs that `p` is
in the target give the same `tileAt`, so long as `p` avoids the bad set — the well-definedness a
"the tile at a point" reading needs. -/
theorem tileAt_congr (D : Dissection N) {p : Plane} (hp hp' : p ∈ D.target.carrier)
    (hbad : p ∉ D.badSet) : D.tileAt hp = D.tileAt hp' :=
  D.tileAt_eq_of_mem hp hbad (D.tileAt_mem hp')

/-! ## Target vertices are always on the bad set

The docstring above claimed this without proof: a target vertex sits on the bad set by
construction, so `tileAt` cannot reach it directly. Here it is, proved — reusing
`BaseSelection.tile_subset_target`/`.tile_interior_subset`, already exactly the inclusions needed,
rather than reproving them. -/

/-- **A target vertex is never interior to the target.**  Its `k`-th barycentric coordinate is
`1`, but the `(k+1)`-th is `0` (`AffineBasis.coord_apply`), so not every coordinate is positive. -/
theorem target_vertex_not_interior (T : Erdos634.Geometry.Tri) (k : Fin 3) :
    T.pts k ∉ interior T.carrier := by
  rw [T.mem_interior_iff_coord_pos]
  push_neg
  refine ⟨k + 1, ?_⟩
  have hne : (k + 1 : Fin 3) ≠ k := by
    have h : ∀ x : Fin 3, x + 1 ≠ x := by decide
    exact h k
  have hz : T.basis.coord (k + 1) (T.pts k) = 0 := by
    have h := T.basis.coord_apply (k + 1) k
    simp only [if_neg hne] at h
    exact h
  rw [hz]

/-- **A target vertex is never interior to any tile.**  A tile's interior sits inside the
target's (`BaseSelection.tile_interior_subset`); a target vertex is not there
(`target_vertex_not_interior`). -/
theorem target_vertex_not_interior_tile (D : Dissection N) (k : Fin 3) (i : Fin N) :
    D.target.pts k ∉ interior (D.tile i).carrier := by
  intro h
  exact target_vertex_not_interior D.target k (Erdos634.BaseSelection.tile_interior_subset D i h)

/-- **A target vertex, in whichever tile covers it, sits on that tile's frontier.**  It is in the
tile's carrier, hence its closure (`subset_closure`), but not in the interior
(`target_vertex_not_interior_tile`), which is exactly `frontier`. So the vertex is in `badSet` —
the claim `TileAt.lean`'s own docstring made. -/
theorem target_vertex_mem_badSet (D : Dissection N) (k : Fin 3) :
    D.target.pts k ∈ D.badSet := by
  have hk : D.target.pts k ∈ D.target.carrier :=
    subset_convexHull ℝ _ (Set.mem_range_self k)
  obtain ⟨i, hi⟩ := D.exists_tile_mem hk
  exact Set.mem_iUnion.mpr ⟨i, subset_closure hi, D.target_vertex_not_interior_tile k i⟩

end Erdos634.Geometry.Dissection
