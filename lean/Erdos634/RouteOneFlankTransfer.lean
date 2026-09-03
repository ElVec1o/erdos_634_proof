import Erdos634.RouteOneThroughEdge

/-!
# The flank conclusion transfers to `E`, and `habove` reduces to three vertex signs

Split out of `RouteOneThroughEdge.lean` (Lean rule 2.3's file-length guideline) — two sections:
`flank_propagates`, showing the flank conclusion at `V` propagates to the advanced point `E` with no
new figure and no straight angle needed there (the edge laid at the previous step plays the role the
`α`-tile played at `V`); and the reduction of `habove` — a tile's whole carrier lying weakly above
the wall — to its three vertices' heights, via the barycentric-coordinate average.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RouteOne

open Erdos634.Geometry

/-! ## Does the mechanism transfer to `E`?  It does — but not in the obvious direction

The descent's `fig n` input wants a *straight angle at the advanced point* `E`, and the mechanism of
`two_through_excludes_mem` **excludes** straight angles rather than producing them, so it does not
transfer as stated.  What transfers is the whole flank argument.

`route_one_flank_from_configuration` needs, at its point, some *other* tile laying a horizontal edge
from that point **leftward**.  At `V` that role is the `α`-tile's edge `VA`.  At `E` it is played by
the edge just produced: the serving tile at `V` lays a horizontal edge from `V` rightward to `E`, and
that same edge, read from `E`, runs horizontally *leftward* to `V`.  So the step supplies its own
successor's hypothesis, and the flank conclusion at `E` follows with **no figure at `E` and no
straight angle there**. -/

/-- **The flank conclusion propagates.**  Given the flank conclusion at `V` — the tile `i` has `V` as
a vertex and a horizontal rightward edge from `V` to `E` — the flank conclusion holds at `E` for the
tile `i'` serving the tangential approach there, with no new figure and no straight angle at `E`.
The edge laid at the previous step plays the role the `α`-tile played at `V`. -/
theorem flank_propagates {N : ℕ} (D : Dissection N) (i i' : Fin N) (V E : Plane) (m : Fin 3)
    (hii' : i' ≠ i)
    (hV : (D.tile i).pts m = V)
    (hE : (D.tile i).pts (m + 1) = E ∨ (D.tile i).pts (m + 2) = E)
    (hEy : (E - V) 1 = 0) (hEx : 0 < (E - V) 0)
    (hne0 : (D.tile i').localAngle E ≠ 0)
    (hne2pi : (D.tile i').localAngle E ≠ 2 * Real.pi)
    (habovei' : ∀ q : Plane, q ∈ (D.tile i').carrier → 0 ≤ (q - E) 1)
    (habovei : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - E) 1)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i').carrier ∧
      0 < (q - E) 0 ∧ (q - E) 1 ≤ δ * ((q - E) 0))
    (hEint : E ∈ interior D.target.carrier) (hVint : V ∈ interior D.target.carrier) :
    ∃ m' : Fin 3, (D.tile i').pts m' = E ∧
      ((((D.tile i').pts (m' + 1) - E) 1 = 0 ∧ 0 < ((D.tile i').pts (m' + 1) - E) 0) ∨
       (((D.tile i').pts (m' + 2) - E) 1 = 0 ∧ 0 < ((D.tile i').pts (m' + 2) - E) 0)) := by
  have hVy : (V - E) 1 = 0 := by
    have h := hEy; simp only [PiLp.sub_apply] at h ⊢; linarith
  have hVx : (V - E) 0 < 0 := by
    have h := hEx; simp only [PiLp.sub_apply] at h ⊢; linarith
  have hidx : ∀ x : Fin 3, (x + 2) + 1 = x ∧ (x + 2) + 2 = x + 1
      ∧ (x + 1) + 1 = x + 2 ∧ (x + 1) + 2 = x := by decide
  obtain ⟨a1, a2, b1, b2⟩ := hidx m
  rcases hE with hE1 | hE2
  · refine route_one_flank_from_configuration D i' i E V hii' hne0 hne2pi habovei' habovei hserve
      (m + 2) ?_ hVy hVx hEint hVint
    intro W hW
    rw [a1, a2, hV, hE1, openSegment_symm]
    exact hW
  · refine route_one_flank_from_configuration D i' i E V hii' hne0 hne2pi habovei' habovei hserve
      (m + 1) ?_ hVy hVx hEint hVint
    intro W hW
    rw [b1, b2, hV, hE2]
    exact hW

/-! ## `habove` is three sign conditions, not a global assumption

Every theorem above takes `habove` — that a tile's whole carrier lies weakly above the wall — as a
hypothesis, and the uniformity worry was that this has to be re-supplied at each advanced point.  It
does not have to be *assumed* at all: it is equivalent to the three vertices lying weakly above,
because the second coordinate is an affine function and the barycentric coordinates are nonnegative
on the carrier.  That is exactly the shape `RouteOne.no_downward_edge` / `.edge_dir_nonneg_of_local`
produce from local containment. -/

/-- **The height of a carrier point is the barycentric average of the vertices' heights.** -/
theorem height_eq_coord_combo (T : Tri) (V q : Plane) :
    (q - V) 1 = ∑ j, T.basis.coord j q * ((T.pts j - V) 1) := by
  have hq : ∑ j, T.basis.coord j q • T.pts j = q := T.basis.linear_combination_coord_eq_self q
  have hs : ∑ j, T.basis.coord j q = 1 := T.basis.sum_coord_apply_eq_one q
  have hqy : q 1 = ∑ j, T.basis.coord j q * (T.pts j) 1 := by
    conv_lhs => rw [← hq]
    simp
  have key : ∑ j, T.basis.coord j q * ((T.pts j - V) 1)
      = (∑ j, T.basis.coord j q * (T.pts j) 1) - (∑ j, T.basis.coord j q) * (V 1) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp only [PiLp.sub_apply]; ring)
  rw [key, hs, one_mul, ← hqy]
  simp only [PiLp.sub_apply]

/-- **A tile whose vertices lie weakly above the wall lies weakly above it.**  This turns `habove`
from a global hypothesis into three sign conditions on the vertices. -/
theorem carrier_above_of_vertices (T : Tri) (V : Plane)
    (h : ∀ j, 0 ≤ (T.pts j - V) 1) : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1 := by
  intro q hq
  have hnn : ∀ j, 0 ≤ T.basis.coord j q := by
    rw [Erdos634.Geometry.Tri.carrier_eq_nonneg_coord] at hq; exact hq
  rw [height_eq_coord_combo T V q]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hnn j) (h j))

/-- **Route 1's flank at `V` from vertex sign conditions.**  `route_one_flank_from_configuration`
with both `habove` hypotheses replaced by the statement that each tile's three vertices lie weakly
above the wall — the form the corpus's own `no_downward_edge` supplies. -/
theorem route_one_flank_of_vertices {N : ℕ} (D : Dissection N) (i j : Fin N) (V A : Plane)
    (hij : i ≠ j)
    (hne0 : (D.tile i).localAngle V ≠ 0)
    (hne2pi : (D.tile i).localAngle V ≠ 2 * Real.pi)
    (hvi : ∀ m : Fin 3, 0 ≤ ((D.tile i).pts m - V) 1)
    (hvj : ∀ m : Fin 3, 0 ≤ ((D.tile j).pts m - V) 1)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0))
    (mj : Fin 3)
    (hjseg : openSegment ℝ V A
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (hAy : (A - V) 1 = 0) (hAx : (A - V) 0 < 0)
    (hVint : V ∈ interior D.target.carrier) (hAint : A ∈ interior D.target.carrier) :
    ∃ m : Fin 3, (D.tile i).pts m = V ∧
      ((((D.tile i).pts (m + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 1) - V) 0) ∨
       (((D.tile i).pts (m + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 2) - V) 0)) :=
  route_one_flank_from_configuration D i j V A hij hne0 hne2pi
    (carrier_above_of_vertices (D.tile i) V hvi)
    (carrier_above_of_vertices (D.tile j) V hvj) hserve mj hjseg hAy hAx hVint hAint


end Erdos634.RouteOne
