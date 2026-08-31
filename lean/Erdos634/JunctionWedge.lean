import Erdos634.WedgeExtremal
import Erdos634.VertexFigureReal
import Erdos634.BaseBetaE1

/-!
# The junction wedge has opening `α`

Erdős #634, `e = 1`, the march step.  `WedgeExtremal.Dissection.corner_on_wedge_sides` needs one
input it cannot supply itself: that the uncovered region at a march junction is a wedge whose
opening equals the corner angle of the tile that fills it.  That input has two halves.

* **Arithmetic.**  At the junction the placed tiles present `γ` and `β`, and the junction lies on a
  straight edge, so the covered angle is `γ + β` out of `π`.  With `γ = 2α + β` and the tile
  relation `3α + 2β = π`, the uncovered opening is `π - (γ + β) = α`.  That is `wedge_opening`
  below, and with it `alpha_lt_pi`, both proved here.
* **Configuration.**  That the two placed tiles at the junction really present `γ` and `β`, and
  that the junction really lies on a straight edge.  This is read from the traces and is *not*
  proved.  It enters `junction_step` below as a named hypothesis rather than being assumed
  silently.

So the open link is now isolated to one hypothesis with a name, and everything after it is formal.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.JunctionWedge

open Erdos634.Geometry

/-- **The uncovered opening at a junction is `α`.**  `γ + β` covered out of `π`, with
`γ = 2α + β` and `3α + 2β = π`. -/
theorem wedge_opening (α β γ : ℝ) (hγ : γ = 2 * α + β) (hsum : 3 * α + 2 * β = Real.pi) :
    Real.pi - (γ + β) = α := by rw [hγ, ← hsum]; ring

/-- The base tile's smallest angle is less than a half turn — needed by `corner_on_wedge_sides`,
and immediate from `3α + 2β = π` with `β > 0`. -/
theorem alpha_lt_pi (α β : ℝ) (hβ : 0 < β) (hα : 0 < α) (hsum : 3 * α + 2 * β = Real.pi) :
    α < Real.pi := by nlinarith

/-- **The march step, assembled.**  The junction's uncovered opening is written as it arises,
`π - (γ + β)`; the filling tile's corner angle equals it and its two edges point into it.  The
conclusion is that those edges lie along the wedge's sides — the two chiralities, and no third
placement.  `wedge_opening` is what turns the opening into `α`, so the tile relation is doing work
here rather than decorating the statement. -/
theorem junction_step (o : Orientation ℝ Plane (Fin 2)) {A P Q u : Plane} {α β γ φ ψ : ℝ}
    (hγ : γ = 2 * α + β) (hsum : 3 * α + 2 * β = Real.pi) (hβ : 0 < β) (hα : 0 < α)
    (hu : u ≠ 0) (hP : P - A ≠ 0) (hQ : Q - A ≠ 0)
    (hφ : (o.oangle u (P - A)).toReal = φ) (hψ : (o.oangle u (Q - A)).toReal = ψ)
    (hφm : φ ∈ Set.Icc (0:ℝ) (Real.pi - (γ + β)))
    (hψm : ψ ∈ Set.Icc (0:ℝ) (Real.pi - (γ + β)))
    (hcorner : cornerAngle P A Q = Real.pi - (γ + β)) :
    (φ = 0 ∧ ψ = Real.pi - (γ + β)) ∨ (φ = Real.pi - (γ + β) ∧ ψ = 0) := by
  have hopen : Real.pi - (γ + β) = α := wedge_opening α β γ hγ hsum
  rw [hopen] at hφm hψm hcorner ⊢
  exact Erdos634.WedgeExtremal.Dissection.corner_on_wedge_sides o hu hP hQ
    (alpha_lt_pi α β hβ hα hsum) hφ hψ hφm hψm hcorner

/-! ## The configuration, reduced

The hypothesis that the placed tiles at a junction present `γ` and `β` is not free-standing.  A
vertex on a straight edge of the dissection has an angle figure `xα + yβ + zγ = π`, which
`BaseBetaE1.vertex_pi` classifies: with `3α + 2β = π` and `γ = 2α + β` the only solutions are
`(x,y,z) = (3,2,0)` and `(1,1,1)`.  So the presence of a single `γ` at a straight-edge vertex
already forces the whole figure, and with it the `β` and the single `α`.

What remains of the configuration is one fact: that a `γ` is present at a march junction — the
apex angle of the `a`-tile whose apex the march is joining.  Everything else follows. -/

/-- **A `γ` at a straight-edge vertex forces the figure `α + β + γ`.**  Consumes
`BaseBetaE1.vertex_pi`; the second solution is the only one with a `γ`. -/
theorem junction_figure (x y z : ℕ) (h1 : y + z = 2) (h2 : 2 * x + z = 3 * y) (hγ : 1 ≤ z) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  rcases Erdos634.BaseBetaE1.vertex_pi x y z h1 h2 with ⟨_, _, hz⟩ | h
  · omega
  · exact h

/-- **The junction's uncovered opening, from the figure.**  At a straight-edge vertex carrying a
`γ`, the figure is `α + β + γ`; with the `γ` and the `β` placed, what is left uncovered is one `α`,
which is the opening `π - (γ + β)`. -/
theorem junction_uncovered (α β γ : ℝ) (x y z : ℕ)
    (h1 : y + z = 2) (h2 : 2 * x + z = 3 * y) (hγz : 1 ≤ z)
    (hγ : γ = 2 * α + β) (hsum : 3 * α + 2 * β = Real.pi) :
    x = 1 ∧ Real.pi - (γ + β) = α :=
  ⟨(junction_figure x y z h1 h2 hγz).1, wedge_opening α β γ hγ hsum⟩

/-- **The march step with the configuration folded in.**  At a straight-edge vertex `A` carrying a
`γ` — which is what an `a`-tile presents at its apex, and a march junction is the meeting of two
such apexes — the uncovered opening is `α`, and a tile filling it with its `α`-corner at `A` has
its two edges along the wedge's sides.  Two placements, no third.

The angle figure `(h1, h2, hγz)` replaces the earlier hypothesis that the placed tiles present `γ`
and `β`: that is now derived.  What this theorem does not establish is that the march's steps land
on vertices of this kind; that is a statement about the run, not about a vertex. -/
theorem march_junction_two_placements (o : Orientation ℝ Plane (Fin 2))
    {A P Q u : Plane} {α β γ φ ψ : ℝ} (x y z : ℕ)
    (h1 : y + z = 2) (h2 : 2 * x + z = 3 * y) (hγz : 1 ≤ z)
    (hγ : γ = 2 * α + β) (hsum : 3 * α + 2 * β = Real.pi) (hβ : 0 < β) (hα : 0 < α)
    (hu : u ≠ 0) (hP : P - A ≠ 0) (hQ : Q - A ≠ 0)
    (hφ : (o.oangle u (P - A)).toReal = φ) (hψ : (o.oangle u (Q - A)).toReal = ψ)
    (hφm : φ ∈ Set.Icc (0:ℝ) α) (hψm : ψ ∈ Set.Icc (0:ℝ) α)
    (hcorner : cornerAngle P A Q = α) :
    (x = 1 ∧ y = 1 ∧ z = 1) ∧ ((φ = 0 ∧ ψ = α) ∨ (φ = α ∧ ψ = 0)) := by
  refine ⟨junction_figure x y z h1 h2 hγz, ?_⟩
  have := junction_step o hγ hsum hβ hα hu hP hQ hφ hψ
    (by rw [wedge_opening α β γ hγ hsum]; exact hφm)
    (by rw [wedge_opening α β γ hγ hsum]; exact hψm)
    (by rw [wedge_opening α β γ hγ hsum]; exact hcorner)
  rw [wedge_opening α β γ hγ hsum] at this
  exact this

/-- **Non-vacuity.**  The angle hypotheses of `junction_step` are satisfiable: the base-`β` tile at
`e = 1` has `0 < α`, `0 < β`, `3α + 2β = π` and `γ = 2α + β`, and then the uncovered opening really
is `α`.  Exhibited here with `α = π/9`, `β = π/3`, which satisfies every angle hypothesis. -/
theorem junction_angles_witness :
    (0:ℝ) < Real.pi / 9 ∧ (0:ℝ) < Real.pi / 3 ∧
    3 * (Real.pi / 9) + 2 * (Real.pi / 3) = Real.pi ∧
    Real.pi - ((2 * (Real.pi / 9) + Real.pi / 3) + Real.pi / 3) = Real.pi / 9 := by
  have hπ := Real.pi_pos
  refine ⟨by linarith, by linarith, by ring, by ring⟩

/-! ## The configuration, no longer assumed

The header above says of the configuration half — that the placed tiles present `γ` and `β`, and
that the junction lies on a straight edge — that it "is read from the traces and is *not* proved".
It is proved now.  `VertexFigureReal.gamma_boundary_figure_real` derives the figure at a real
frontier point of a `Dissection` carrying a `γ`: exactly one tile presents each of `α`, `β`, `γ`,
and none is straight.  That is the configuration, and it comes from the boundary figure
classification rather than from a trace. -/

/-- **The march step at a real junction.**  Let `v` be a point of the target's frontier that is not
a target vertex, and let some tile present `γ` there.  Then the figure at `v` is exactly
`{α, β, γ}` — one tile each, none straight — so with the `γ` and the `β` placed the uncovered
opening is `α`; and a tile filling it with its `α`-corner at `v` has its two edges on the wedge's
two boundary rays, in one of exactly two ways.

This is `march_junction_two_placements` with its angle-figure hypotheses discharged from the
dissection.  What remains open for `rem:marchobl` is *not* this: it is that the march's steps land
on vertices of this kind, which is a statement about the run, not about a vertex. -/
theorem march_junction_real {N : ℕ} (D : Dissection N) (o : Orientation ℝ Plane (Fin 2))
    {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hβpos : 0 < β) (hαpos : 0 < α)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (iγ : Fin N) (hiγ : (D.tile iγ).localAngle v = γ)
    {P Q u : Plane} {φ ψ : ℝ}
    (hu : u ≠ 0) (hP : P - v ≠ 0) (hQ : Q - v ≠ 0)
    (hφ : (o.oangle u (P - v)).toReal = φ) (hψ : (o.oangle u (Q - v)).toReal = ψ)
    (hφm : φ ∈ Set.Icc (0:ℝ) α) (hψm : ψ ∈ Set.Icc (0:ℝ) α)
    (hcorner : cornerAngle P v Q = α) :
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 0)
    ∧ ((φ = 0 ∧ ψ = α) ∨ (φ = α ∧ ψ = 0)) := by
  refine ⟨Erdos634.VertexFigureReal.gamma_boundary_figure_real D hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr hv hnv hvals iγ hiγ, ?_⟩
  have hstep := junction_step o hγdef hrel hβpos hαpos hu hP hQ hφ hψ
    (by rw [wedge_opening α β γ hγdef hrel]; exact hφm)
    (by rw [wedge_opening α β γ hγdef hrel]; exact hψm)
    (by rw [wedge_opening α β γ hγdef hrel]; exact hcorner)
  rw [wedge_opening α β γ hγdef hrel] at hstep
  exact hstep

end Erdos634.JunctionWedge
