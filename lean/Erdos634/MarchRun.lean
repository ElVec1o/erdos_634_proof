import Erdos634.VertexFigureReal

/-!
# The march's junctions: obligation (i) of `rem:marchobl`

`rem:marchobl` leaves three statements, all about the *run* rather than a vertex:

* (i) the march's steps land on vertices carrying a `γ` at a straight edge;
* (ii) the two placements advance the configuration by exactly one and by exactly two positions;
* (iii) both advances reduce to the same problem at smaller `bp`.

This file attacks (i), and reduces it to `prop:orientmono`, which is already a recorded statement of
the programme rather than a new obligation.

The reduction is a dichotomy.  At a straight-edge point the figure is `(3,2,0)` or `(1,1,1)`
(`VertexFigureReal.boundary_figure_cases`), and at an interior point of a straight edge with a
straddling tile on the far side it is again `(1,1,1)` once a `γ` is present
(`VertexFigureReal.one_gamma_real`).  So a junction either carries the figure `{3α, 2β}` — no `γ`
at all — or it carries a `γ` and is a march junction.  `prop:orientmono` says at most one junction
of an `a`-run is of the first kind, and names it: the `BG → GB` transition.  Every other junction of
the run is therefore of the second kind.

What this does **not** do is prove `prop:orientmono` at a real run; that is bridge (c), and is
recorded as such.  The content here is that (i) needs nothing beyond it.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchRun

open Erdos634.Geometry

/-- **The junction dichotomy.**  At a point of the frontier that is not a target vertex, either no
tile presents `γ` — and then the figure is exactly `{3α, 2β}` — or some tile does, and then the
figure is exactly `{α, β, γ}`.  There is no third case, so "carries a `γ`" and "is not the
`{3α,2β}` junction" are the same condition. -/
theorem junction_dichotomy {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hns : ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 0) :
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 3 ∧
     ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 2 ∧
     ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0)
    ∨
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1) := by
  classical
  have hsum := Erdos634.VertexFigureReal.boundary_multiplicities_cards D α β γ
    hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hv hnv hvals
  rcases Erdos634.VertexFigureReal.boundary_figure_cases hγdef hrel hirr _ _ _ _ hsum with
    ⟨hs, hp, hq, hr⟩ | ⟨-, hcase⟩
  · omega
  · rcases hcase with ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩
    · exact Or.inl ⟨hp, hq, hr⟩
    · exact Or.inr ⟨hp, hq, hr⟩

/-- **A junction that is not the `{3α,2β}` figure carries a `γ`.**  The form (i) is used in: given
that the junction is not the exceptional one, some tile presents `γ`, which is exactly the
hypothesis `march_junction_real` consumes. -/
theorem gamma_of_not_exceptional {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hns : ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 0)
    (hnotexc : ¬ (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 3 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0)) :
    ∃ i : Fin N, (D.tile i).localAngle v = γ := by
  classical
  rcases junction_dichotomy D hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr
    hv hnv hvals hns with h | ⟨-, -, hr⟩
  · exact absurd h hnotexc
  · have : ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := this
    exact ⟨i, by simpa using hi⟩

/-- **Obligation (i), reduced.**  Along an `a`-run, let `J` index the junctions and let `exc` be the
set of those carrying the exceptional figure `{3α,2β}`.  `prop:orientmono` states `exc` has at most
one element.  Then every junction outside `exc` carries a `γ`, so all but at most one junction of
the run is a march junction.  Stated abstractly so that the only input is the orientation-monotone
bound. -/
theorem all_but_one_is_march_junction {J : Type*} [Fintype J] [DecidableEq J]
    (exc march : Finset J) (hmono : exc.card ≤ 1)
    (hdich : ∀ j, j ∉ exc → j ∈ march) :
    (Finset.univ \ march).card ≤ 1 := by
  refine le_trans (Finset.card_le_card ?_) hmono
  intro j hj
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
  by_contra hne
  exact hj (hdich j hne)

/-! ## The boundary run: `BG → GB` dies by counting alone

`MarchCoords`' orientation convention, read off the distances: a `BG` tile has `β` at the left end
of its `a`-edge and `γ` at the right (`bg_left` puts the left end at distance `c` from the apex, so
its flanking sides are `a, c`, the `β`-corner); a `GB` tile has `γ` at the left.  So at a `BG → GB`
junction **both tiles present `γ`**.

At a straight-edge point that is one `γ` too many: the figure system is `x + 2z = 3`, `y + z = 2`,
so `z = 2` forces `x = -1`.  `gamma_boundary_figure_real` already says the `γ`-count is exactly one,
so two distinct tiles presenting `γ` there is immediate.

This is a **second, independent kill** of `BG → GB`, and on the boundary it is far cheaper than the
wedge route of `MarchKill`/`MarchRunStep`.  The wedge route is not redundant: it uses only
`interiors_disjoint` and so applies at *interior* junctions too, where the budget is `2π` and the
figure `{β, 3γ}` makes `r = 3` possible — counting cannot kill it there. -/

/-- **Two tiles cannot both present `γ` at a straight-edge point.** -/
theorem no_two_gammas {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (i j : Fin N) (hij : i ≠ j)
    (hi : (D.tile i).localAngle v = γ) (hj : (D.tile j).localAngle v = γ) :
    False := by
  classical
  obtain ⟨-, -, hcard, -⟩ := Erdos634.VertexFigureReal.gamma_boundary_figure_real D
    hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hv hnv hvals i hi
  have hsub : ({i, j} : Finset (Fin N))
      ⊆ ({k | (D.tile k).localAngle v = γ} : Finset (Fin N)) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simpa using hi
    · simpa using hj
  have h2 : ({i, j} : Finset (Fin N)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

/-! ## Obligation (i)'s `BG → GB` half, assembled

At a straight-edge junction each of the two `a`-tiles presents `β` or `γ` (those are the corners
flanking an `a`-edge: `β` flanks `{a,c}`, `γ` flanks `{a,b}`, and `α` is opposite `a` so cannot sit
on the line).  `no_two_gammas` removes the `(γ, γ)` case, which is `BG → GB`.  So on a boundary run
the orientation word never has a `BG` immediately followed by a `GB`. -/

/-- **No `BG → GB` on a boundary run.**  Stated as: the two tiles at a straight-edge junction cannot
both present `γ`, given that each presents `β` or `γ` there.  The three surviving cases are
`(β,β)`, `(β,γ)`, `(γ,β)` — `GB → GB`, `GB → BG`, `BG → BG` — exactly the orientation words with no
`BG → GB` factor. -/
theorem junction_cases {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (i j : Fin N) (hij : i ≠ j)
    (hi : (D.tile i).localAngle v = β ∨ (D.tile i).localAngle v = γ)
    (hj : (D.tile j).localAngle v = β ∨ (D.tile j).localAngle v = γ) :
    ((D.tile i).localAngle v = β ∧ (D.tile j).localAngle v = β) ∨
    ((D.tile i).localAngle v = β ∧ (D.tile j).localAngle v = γ) ∨
    ((D.tile i).localAngle v = γ ∧ (D.tile j).localAngle v = β) := by
  rcases hi with hi | hi
  · rcases hj with hj | hj
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inr (Or.inl ⟨hi, hj⟩)
  · rcases hj with hj | hj
    · exact Or.inr (Or.inr ⟨hi, hj⟩)
    · exact absurd (no_two_gammas D hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
        hγdef hrel hirr hv hnv hvals i j hij hi hj) not_false

end Erdos634.MarchRun
