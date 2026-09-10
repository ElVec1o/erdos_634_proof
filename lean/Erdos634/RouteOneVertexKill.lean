import Erdos634.RouteOne
import Erdos634.BaseBetaE1
import Erdos634.CornerAnglePerm

/-!
# The escape point's vertex/edge-interior dichotomy: a two-case enumeration, and its kill

**Status note (2026-09-11).**  The project's Zenodo description (written at commit `7e38693`,
2026-09-01) records as the last open item of Route 1: *"A single hypothesis remains uncomposed:
that the escape point is a vertex of the serving tile rather than interior to one of its edges."*
That sentence is **stale**.  Later the same day, commit `68b5af9` added
`RouteOne.serving_has_vertex` / `RouteOne.route_one_flank_composed`, which discharge exactly that
hypothesis — *given* `RouteOne.EscapeData.hcard`, the statement that the straight-angle count at the
escape point `V` is exactly one.  So the residue is not the vertex/edge dichotomy; it is `hcard`.

This file settles `hcard`.  What it establishes:

* **The dichotomy is a two-case enumeration, not a family** (`straight_dichotomy`,
  `straight_two_iff_no_corner`).  At an interior point carrying at least one straight angle, the
  vertex figure is either
  - `s = 1`, and then at least one tile presents a corner angle there, or
  - `s = 2`, and then `p = q = r = u = 0`: **exactly two tiles meet `V`, both with `V` interior to
    an edge, and no tile anywhere at `V` has a corner.**
  There is no third possibility and no parameter.  The two branches are separated by a single
  Boolean: does *any* tile have a corner at `V`.

* **Any corner kills the bad branch** (`unique_straight_of_corner`,
  `card_straight_eq_one_of_corner`).  This is strictly weaker input than
  `RouteOne.alpha_wall_figure`, which requires the corner to be an `α`; here `α`, `β` or `γ` will
  do, and by `localAngle_mem_of_vertex` a *vertex* of any tile at `V` supplies one.  So the input is
  purely combinatorial: some edge of the dissection **ends** at `V`.

* **The composition** (`serving_vertex_of_any_corner`, `escape_flank_of_corner`): from a vertex
  witness at `V`, `EscapeData.hcard` is derived, hence the serving tile has `V` as a vertex, hence
  Route 1's flank conclusion.  `hcard` stops being a hypothesis.

* **What the surviving `s = 2` branch would look like, geometrically**
  (`straight_above_forces_horizontal`).  A tile with `V` interior to an edge whose carrier stays
  weakly above `V` has that edge *horizontal*, and then contains points strictly left **and**
  strictly right of `V` on the wall.  In particular no tile edge ends at `V` — which is precisely
  the blocking edge `[A, V]` that defines the escape configuration.  Same kill, geometric form.

* **The congruent-dissection form** (`congruentDissection_serving_vertex`), in which `hvals` is
  discharged as well by `Geometry.congruentDissection_localAngle_mem_all`.  Read against
  `rem:route1uniform` this is the operative statement: there the escape point is *defined* as the
  third vertex of the second side tile, `V = c·u + (c,0)`, so the corner witness is supplied by the
  configuration's own definition rather than assumed.

**What is honestly still open.**  Everything upstream of the local figure.  Producing the
configuration — an actual tile `b` below `V` with a straight angle there, `V` interior to the
target, the approach sequence — from a hypothetical base-`β` tiling is *attachment*, and it is not
done here or anywhere; it is the same obligation `RouteOne.route_one_given_attachment` names.
Nothing in this file proves that a base-`β` tiling exists or does not exist, closes `conj:advance`,
or touches the `e ≥ 2` crossing question.  What changed is the *shape* of Route 1's local residue:
it was a metric count of straight angles at `V` (`hcard`), and it is now a purely combinatorial
witness — some dissection edge ends at `V` — which `rem:route1uniform` supplies definitionally.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RouteOneVertexKill

open Erdos634.Geometry

/-! ## 1. The arithmetic: the dichotomy is two cases -/

/-- **The straight-angle dichotomy.**  At an interior point of a dissection by a `(α, β, γ)` tile
with `γ = 2α + β`, `3α + 2β = π` and `α/π` irrational, if at least one tile presents a straight
angle then exactly one of two figures occurs: `s = 2` with **no** corner angles at all, or `s = 1`
with at least one corner angle.  No other configuration is possible. -/
theorem straight_dichotomy {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s u : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi
      + (u : ℝ) * (2 * Real.pi) = 2 * Real.pi)
    (hs : 1 ≤ s) :
    (s = 2 ∧ p = 0 ∧ q = 0 ∧ r = 0 ∧ u = 0) ∨ (s = 1 ∧ u = 0 ∧ 1 ≤ p + q + r) := by
  rcases Erdos634.VertexFigureReal.interior_figure_cases_gen hγ hrel hirr p q r s u hsum with
    ⟨-, -, -, -, hs0⟩ | ⟨hu, hs2, hp0, hq0, hr0⟩ | ⟨hu, hs1, hcase⟩ | ⟨-, hs0, -⟩
  · omega
  · exact Or.inl ⟨hs2, hp0, hq0, hr0, hu⟩
  · exact Or.inr ⟨hs1, hu, by rcases hcase with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> omega⟩
  · omega

/-- **The dichotomy as an exact iff.**  With a straight angle present, two straight angles occur
**exactly when** no tile presents a corner angle.  This is the precise sense in which the
"vertex or edge-interior" question has no third case and no parameter. -/
theorem straight_two_iff_no_corner {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s u : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi
      + (u : ℝ) * (2 * Real.pi) = 2 * Real.pi)
    (hs : 1 ≤ s) :
    s = 2 ↔ p + q + r = 0 := by
  constructor
  · intro h2
    rcases straight_dichotomy hγ hrel hirr p q r s u hsum hs with ⟨-, hp, hq, hr, -⟩ | ⟨h1, -, -⟩
    · omega
    · omega
  · intro h0
    rcases straight_dichotomy hγ hrel hirr p q r s u hsum hs with ⟨h2, -, -, -, -⟩ | ⟨-, -, hge⟩
    · exact h2
    · omega

/-- **Any corner angle forces a unique straight angle.**  Strictly weaker input than
`RouteOne.alpha_wall_figure`, which requires the corner to be an `α`. -/
theorem unique_straight_of_corner {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s u : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi
      + (u : ℝ) * (2 * Real.pi) = 2 * Real.pi)
    (hs : 1 ≤ s) (hcorner : 1 ≤ p + q + r) :
    s = 1 ∧ u = 0 := by
  rcases straight_dichotomy hγ hrel hirr p q r s u hsum hs with ⟨-, hp, hq, hr, -⟩ | ⟨h1, hu, -⟩
  · omega
  · exact ⟨h1, hu⟩

/-! ## 2. Non-vacuity: both branches satisfy the angle sum

A dichotomy proved from a case list is worth nothing if one branch is arithmetically impossible for
a reason the case list hides.  Both are realizable at the level of the angle equation, so the
`s = 2` branch is genuinely there and genuinely needs the corner witness to remove it. -/

/-- `(p,q,r,s,u) = (0,0,0,2,0)` satisfies the angle sum: the `s = 2` branch is not vacuous. -/
theorem sum_witness_two_straight {α β γ : ℝ} :
    ((0 : ℕ) : ℝ) * α + ((0 : ℕ) : ℝ) * β + ((0 : ℕ) : ℝ) * γ + ((2 : ℕ) : ℝ) * Real.pi
      + ((0 : ℕ) : ℝ) * (2 * Real.pi) = 2 * Real.pi := by
  push_cast; ring

/-- `(p,q,r,s,u) = (1,1,1,1,0)` satisfies the angle sum: the `s = 1` branch is not vacuous. -/
theorem sum_witness_one_each {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) :
    ((1 : ℕ) : ℝ) * α + ((1 : ℕ) : ℝ) * β + ((1 : ℕ) : ℝ) * γ + ((1 : ℕ) : ℝ) * Real.pi
      + ((0 : ℕ) : ℝ) * (2 * Real.pi) = 2 * Real.pi := by
  subst hγ; push_cast; linarith

/-- `(p,q,r,s,u) = (3,2,0,1,0)` satisfies the angle sum: the other `s = 1` figure is realizable. -/
theorem sum_witness_three_two {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) :
    ((3 : ℕ) : ℝ) * α + ((2 : ℕ) : ℝ) * β + ((0 : ℕ) : ℝ) * γ + ((1 : ℕ) : ℝ) * Real.pi
      + ((0 : ℕ) : ℝ) * (2 * Real.pi) = 2 * Real.pi := by
  push_cast; linarith

/-- **Non-vacuity of the whole arithmetic layer.**  The hypothesis bundle of `straight_dichotomy`
is satisfiable at a genuine base-`β` tile — `(e,f) = (1,2)`, `α = 2·arcsin(1/4)`, whose irrationality
is `BaseBetaE1.tile_alpha_irrational` — and *both* branches of the dichotomy solve the angle
equation there.  So neither branch is empty for a hidden arithmetic reason, and the corner witness
in `unique_straight_of_corner` is doing real work rather than removing a case that never occurs. -/
theorem straight_dichotomy_nonvacuous :
    ∃ α β γ : ℝ, γ = 2 * α + β ∧ 3 * α + 2 * β = Real.pi ∧
      (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧
      (((0 : ℕ) : ℝ) * α + ((0 : ℕ) : ℝ) * β + ((0 : ℕ) : ℝ) * γ + ((2 : ℕ) : ℝ) * Real.pi
        + ((0 : ℕ) : ℝ) * (2 * Real.pi) = 2 * Real.pi) ∧
      (((1 : ℕ) : ℝ) * α + ((1 : ℕ) : ℝ) * β + ((1 : ℕ) : ℝ) * γ + ((1 : ℕ) : ℝ) * Real.pi
        + ((0 : ℕ) : ℝ) * (2 * Real.pi) = 2 * Real.pi) := by
  refine ⟨2 * Real.arcsin (1 / 4), (Real.pi - 3 * (2 * Real.arcsin (1 / 4))) / 2,
    2 * (2 * Real.arcsin (1 / 4)) + (Real.pi - 3 * (2 * Real.arcsin (1 / 4))) / 2,
    rfl, by ring, ?_, sum_witness_two_straight, sum_witness_one_each rfl (by ring)⟩
  have hsin : Real.sin ((2 * Real.arcsin (1 / 4)) / 2) = ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ)) := by
    have h : (2 * Real.arcsin (1 / 4)) / 2 = Real.arcsin (1 / 4) := by ring
    rw [h, Real.sin_arcsin (by norm_num) (by norm_num)]
    norm_num
  exact Erdos634.BaseBetaE1.tile_alpha_irrational 1 2 (by norm_num) (by norm_num) _ hsin

/-! ## 3. A vertex supplies a corner angle

`PinPlumbing.localAngle_cases` says a tile's local angle at a point it has as a vertex is a corner
angle.  To feed the arithmetic that corner angle must be one of `α, β, γ` rather than `π`, `2π` or
`0`.  Positivity is `MarchFlank.cornerAngle_pos`; the strict upper bound is the new piece. -/

/-- **A corner angle is strictly less than `π`.**  Equality would make the three vertices
collinear, against `Tri.indep`. -/
theorem cornerAngle_lt_pi (T : Tri) (j : Fin 3) :
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) < Real.pi := by
  rw [Erdos634.Geometry.cornerAngle]
  rcases lt_or_eq_of_le (EuclideanGeometry.angle_le_pi
    (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exact h
  · exfalso
    have hcol : Collinear ℝ ({T.pts (j + 1), T.pts j, T.pts (j + 2)} : Set Plane) :=
      EuclideanGeometry.collinear_of_angle_eq_pi h
    have hidx : ∀ i j : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := by decide
    have hsub : Set.range T.pts ⊆ ({T.pts (j + 1), T.pts j, T.pts (j + 2)} : Set Plane) := by
      rintro _ ⟨i, rfl⟩
      have := hidx i j
      rcases this with rfl | rfl | rfl <;> simp
    have hrange : Collinear ℝ (Set.range T.pts) := hcol.subset hsub
    exact (affineIndependent_iff_not_collinear.mp T.indep) hrange

/-- **A tile with `V` as a vertex presents one of `α, β, γ` there.**  From the four-way split, the
value is a corner angle, which is strictly between `0` and `π`; the tile-angle hypothesis then
places it among the three corner angles. -/
theorem localAngle_mem_of_vertex {N : ℕ} (D : Dissection N) {α β γ : ℝ} {V : Plane} (j : Fin N)
    (hvals : (D.tile j).localAngle V ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (hvert : ∃ k : Fin 3, (D.tile j).pts k = V) :
    (D.tile j).localAngle V = α ∨ (D.tile j).localAngle V = β ∨ (D.tile j).localAngle V = γ := by
  classical
  obtain ⟨k, hk⟩ := hvert
  have hex : ∃ m : Fin 3, V = (D.tile j).pts m := ⟨k, hk.symm⟩
  have hcorner : (D.tile j).localAngle V
      = cornerAngle ((D.tile j).pts (hex.choose + 1)) ((D.tile j).pts hex.choose)
        ((D.tile j).pts (hex.choose + 2)) := by
    rw [Erdos634.Geometry.Tri.localAngle, dif_pos hex]
  have hpos : 0 < (D.tile j).localAngle V := by
    rw [hcorner]; exact Erdos634.MarchFlank.cornerAngle_pos _ _
  have hlt : (D.tile j).localAngle V < Real.pi := by
    rw [hcorner]; exact cornerAngle_lt_pi _ _
  have hpi := Real.pi_pos
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvals
  rcases hvals with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h (ne_of_lt hlt)
  · exact absurd h (by intro hc; rw [hc] at hlt; linarith)
  · exact absurd h (by intro hc; rw [hc] at hpos; linarith)

/-! ## 4. The real-dissection form: the straight-angle count is one

`RouteOne.EscapeData.hcard` — the field Route 1 still carries as a hypothesis — now follows from a
single vertex witness at `V`. -/

/-- **The straight-angle count at `V` is one, from any corner there.**  Weaker input than
`RouteOne.alpha_wall_figure_real`: the corner may be `α`, `β` or `γ`. -/
theorem card_straight_eq_one_of_corner {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {V : Plane} (hV : V ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle V ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (jc : Fin N) (hjc : (D.tile jc).localAngle V = α ∨ (D.tile jc).localAngle V = β ∨
      (D.tile jc).localAngle V = γ)
    (iπ : Fin N) (hiπ : (D.tile iπ).localAngle V = Real.pi) :
    ({i | (D.tile i).localAngle V = Real.pi} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle V = 2 * Real.pi} : Finset (Fin N)).card = 0 := by
  classical
  have hsum := Erdos634.VertexFigureReal.interior_multiplicities_cards D α β γ
    hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hV hvals
  have hspos : 1 ≤ ({i | (D.tile i).localAngle V = Real.pi} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨iπ, by simp [hiπ]⟩
  have hcorner : 1 ≤ ({i | (D.tile i).localAngle V = α} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle V = β} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle V = γ} : Finset (Fin N)).card := by
    rcases hjc with h | h | h
    · have : 1 ≤ ({i | (D.tile i).localAngle V = α} : Finset (Fin N)).card :=
        Finset.card_pos.mpr ⟨jc, by simp [h]⟩
      omega
    · have : 1 ≤ ({i | (D.tile i).localAngle V = β} : Finset (Fin N)).card :=
        Finset.card_pos.mpr ⟨jc, by simp [h]⟩
      omega
    · have : 1 ≤ ({i | (D.tile i).localAngle V = γ} : Finset (Fin N)).card :=
        Finset.card_pos.mpr ⟨jc, by simp [h]⟩
      omega
  obtain ⟨hs, hu⟩ := unique_straight_of_corner hγdef hrel hirr _ _ _ _ _ hsum hspos hcorner
  exact ⟨hs, hu⟩

/-- **The same, from a vertex witness.**  Some tile has `V` as a vertex — i.e. some dissection edge
*ends* at `V` — and some tile has `V` interior to an edge.  Then the straight angle is unique. -/
theorem card_straight_eq_one_of_vertex {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {V : Plane} (hV : V ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle V ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (jc : Fin N) (hjc : ∃ k : Fin 3, (D.tile jc).pts k = V)
    (iπ : Fin N) (hiπ : (D.tile iπ).localAngle V = Real.pi) :
    ({i | (D.tile i).localAngle V = Real.pi} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle V = 2 * Real.pi} : Finset (Fin N)).card = 0 :=
  card_straight_eq_one_of_corner D hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
    hπ2π hπ0 h2π0 hγdef hrel hirr hV hvals jc
    (localAngle_mem_of_vertex D jc (hvals jc) hjc) iπ hiπ

/-! ## 5. The composition: Route 1's serving tile has `V` as a vertex

`RouteOne.route_one_flank_composed` consumes `hcard`.  Section 4 produces it.  The two together
discharge the hypothesis the Zenodo description names, from an input that is not a count. -/

/-- **The serving tile has `V` as a vertex, from any vertex witness at `V`.**  This is the
composition the release description records as missing.  `b` is the tile below carrying the
straight angle; `i` is the serving tile; `jc` is any tile with `V` among its vertices. -/
theorem serving_vertex_of_any_corner {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {V : Plane} (hV : V ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle V ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (jc : Fin N) (hjc : ∃ k : Fin 3, (D.tile jc).pts k = V)
    (i b : Fin N) (hib : i ≠ b) (hb : (D.tile b).localAngle V = Real.pi)
    (hVb : V ∈ (D.tile b).carrier)
    (hclose : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ (D.tile i).carrier ∧ dist q V < r) :
    ∃ k : Fin 3, (D.tile i).pts k = V := by
  obtain ⟨hcard, -⟩ := card_straight_eq_one_of_vertex D hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
    hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hγdef hrel hirr hV hvals jc hjc b hb
  exact Erdos634.RouteOne.serving_has_vertex D i V
    (Erdos634.RouteOne.serving_ne_zero D i hclose)
    (Erdos634.RouteOne.serving_ne_two_pi D hib hVb)
    (Erdos634.RouteOne.not_straight_of_unique D V hcard b hb i hib)

/-- **Route 1's flank, with `hcard` replaced by a vertex witness.**  The full conclusion Route 1
needs — `V` a vertex of the serving tile, carrying a horizontal rightward edge there — from a
configuration in which the straight-angle count is not assumed but derived. -/
theorem escape_flank_of_corner {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {V : Plane} (hV : V ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle V ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (jc : Fin N) (hjc : ∃ k : Fin 3, (D.tile jc).pts k = V)
    (i b : Fin N) (hib : i ≠ b) (hb : (D.tile b).localAngle V = Real.pi)
    (hVb : V ∈ (D.tile b).carrier)
    (hclose : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ (D.tile i).carrier ∧ dist q V < r)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0))
    (habove : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1) :
    ∃ k : Fin 3, (D.tile i).pts k = V ∧
      ((((D.tile i).pts (k + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 1) - V) 0) ∨
       (((D.tile i).pts (k + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 2) - V) 0)) := by
  obtain ⟨hcard, -⟩ := card_straight_eq_one_of_vertex D hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
    hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hγdef hrel hirr hV hvals jc hjc b hb
  exact Erdos634.RouteOne.route_one_flank_composed D V i b hib hcard hb
    (Erdos634.RouteOne.serving_ne_zero D i hclose)
    (Erdos634.RouteOne.serving_ne_two_pi D hib hVb) hserve habove

/-- **The enumeration, at the real dissection.**  At the escape point either the serving tile has
`V` as a vertex — Route 1's conclusion — or the figure at `V` is the single configuration
`(p,q,r,s,u) = (0,0,0,2,0)`: **exactly two tiles present anything at `V`, both with `V` interior to
an edge, and no tile at `V` has a corner.**  There is no third case.  This is the precise content of
the "vertex versus interior to an edge" dichotomy the release description names: it is a Boolean,
not a family, and its bad branch is one fully-determined local picture. -/
theorem serving_vertex_or_two_straight {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {V : Plane} (hV : V ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle V ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (i b : Fin N) (hib : i ≠ b) (hb : (D.tile b).localAngle V = Real.pi)
    (hVb : V ∈ (D.tile b).carrier)
    (hclose : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ (D.tile i).carrier ∧ dist q V < r) :
    (∃ k : Fin 3, (D.tile i).pts k = V) ∨
      (({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card = 2 ∧
       ({j | (D.tile j).localAngle V = α} : Finset (Fin N)).card = 0 ∧
       ({j | (D.tile j).localAngle V = β} : Finset (Fin N)).card = 0 ∧
       ({j | (D.tile j).localAngle V = γ} : Finset (Fin N)).card = 0 ∧
       ({j | (D.tile j).localAngle V = 2 * Real.pi} : Finset (Fin N)).card = 0) := by
  classical
  have hsum := Erdos634.VertexFigureReal.interior_multiplicities_cards D α β γ
    hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hV hvals
  have hspos : 1 ≤ ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨b, by simp [hb]⟩
  rcases straight_dichotomy hγdef hrel hirr _ _ _ _ _ hsum hspos with
    ⟨hs2, hp, hq, hr, hu⟩ | ⟨hs1, -, -⟩
  · exact Or.inr ⟨hs2, hp, hq, hr, hu⟩
  · exact Or.inl (Erdos634.RouteOne.serving_has_vertex D i V
      (Erdos634.RouteOne.serving_ne_zero D i hclose)
      (Erdos634.RouteOne.serving_ne_two_pi D hib hVb)
      (Erdos634.RouteOne.not_straight_of_unique D V hs1 b hb i hib))

/-! ### The congruent-dissection form, with `hvals` discharged too

`CornerAnglePerm.congruentDissection_localAngle_mem_all` proves the six-value hypothesis at *every*
point of a congruent dissection, so for a `CongruentDissection` the only inputs left are the model's
angle arithmetic and the configuration itself.

Read against `rem:route1uniform`, this is the statement that matters: there the escape point is
defined as *the third vertex* of the second side tile, `V = c·u + (c,0)`.  So the corner witness
`hjc` is supplied by the configuration's own definition — it is not a new assumption. -/

/-- **Route 1's vertex conclusion for a congruent dissection.**  Only the model's angle arithmetic
and the local configuration remain as hypotheses; `hvals` and `hcard` are both derived. -/
theorem congruentDissection_serving_vertex {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {V : Plane} (hV : V ∈ interior D.target.carrier)
    (jc : Fin N) (hjc : ∃ k : Fin 3, (D.tile jc).pts k = V)
    (i b : Fin N) (hib : i ≠ b) (hb : (D.tile b).localAngle V = Real.pi)
    (hVb : V ∈ (D.tile b).carrier)
    (hclose : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ (D.tile i).carrier ∧ dist q V < r) :
    ∃ k : Fin 3, (D.tile i).pts k = V :=
  serving_vertex_of_any_corner D.toDissection hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
    hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hγdef hrel hirr hV
    (fun j => Erdos634.Geometry.congruentDissection_localAngle_mem_all D α β γ
      hmα hmβ hmγ V j)
    jc hjc i b hib hb hVb hclose

/-! ## 6. The geometry of the branch that the corner witness removes

If the `s = 2` branch held at `V`, the serving tile would have `V` interior to one of its edges.
That edge is then forced horizontal by the weakly-above hypothesis, and its two endpoints sit
strictly on opposite sides of `V` along the wall.  So in that branch the serving tile *straddles*
`V`: it neither begins nor ends there, and no advance step is available.  This is the same kill in
geometric rather than arithmetic form, and it is what makes the corner witness the right input:
the escape configuration's blocking edge `[A, V]` ends at `V` by construction. -/

/-- **A straight angle from above is horizontal, and straddles.**  `V` strictly between `P` and `Q`
(an edge of a tile whose carrier stays weakly above `V`) forces both `P` and `Q` onto the wall, on
strictly opposite sides of `V`. -/
theorem straight_above_forces_horizontal (P Q V : Plane) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam < 1) (hV : V = lam • P + (1 - lam) • Q)
    (hP : 0 ≤ (P - V) 1) (hQ : 0 ≤ (Q - V) 1) (hPV : (P - V) 0 ≠ 0) :
    (P - V) 1 = 0 ∧ (Q - V) 1 = 0 ∧
      ((P - V) 0 < 0 ∧ 0 < (Q - V) 0 ∨ 0 < (P - V) 0 ∧ (Q - V) 0 < 0) := by
  have key : ∀ c : Fin 2, lam * (P - V) c + (1 - lam) * (Q - V) c = 0 := by
    intro c
    have : (lam • P + (1 - lam) • Q) c = lam * P c + (1 - lam) * Q c := by simp
    have hVc : V c = lam * P c + (1 - lam) * Q c := by rw [hV]; exact this
    simp only [PiLp.sub_apply]
    rw [hVc]; ring
  have h1' := key 1
  have hPy : (P - V) 1 = 0 := by nlinarith [hP, hQ]
  have hQy : (Q - V) 1 = 0 := by nlinarith [hP, hQ, hPy]
  refine ⟨hPy, hQy, ?_⟩
  have h0' := key 0
  rcases lt_or_gt_of_ne hPV with hneg | hpos
  · left; constructor
    · exact hneg
    · nlinarith
  · right; constructor
    · exact hpos
    · nlinarith

end Erdos634.RouteOneVertexKill
