import Erdos634.Congruence
import Erdos634.PinPlumbing
import Erdos634.VertexFigureReal
import Erdos634.RouteOne
import Erdos634.TileAt
import Erdos634.MarchRun
import Erdos634.JunctionWedge
import Erdos634.RouteOneThroughEdge
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# Congruent triangles match corner angles under a single permutation

Erdős #634. `Congruence.Tri.Congruent.dist_eq` exposes the vertex correspondence of a congruence as
a permutation matching every *distance*; `CongruentAngles.congruent_corner_angles` matches corner
angles but only one vertex at a time, existentially. The double count behind `lem:census` needs the
uniform form: **one** permutation matching all three corner angles at once.

The route is the isometry itself rather than the distances. A `Tri.Congruent` carries an
`IsometryEquiv` of the plane; Mazur–Ulam (`IsometryEquiv.toRealAffineIsometryEquiv`) makes it affine,
and `AffineIsometry.angle_map` then transports corner angles directly. The only combinatorial step
left is that `σ` sends the two vertices *other than* `k` to the two other than `σ k`, in one order or
the other — a `Fin 3` fact, settled by `decide`, with `EuclideanGeometry.angle_comm` absorbing the
swap.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry

namespace Erdos634.Geometry

/-- **Congruent triangles match corner angles under one permutation.** -/
theorem Tri.Congruent.cornerAngle_perm {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3,
      cornerAngle (U.pts (σ k + 1)) (U.pts (σ k)) (U.pts (σ k + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨σ, fun k => ?_⟩
  -- the isometry transports the corner angle at `k` to the one at `σ k`
  have hmap : cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2)))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
    rw [← hf (k + 1), ← hf k, ← hf (k + 2)]
    rw [Erdos634.Geometry.cornerAngle, Erdos634.Geometry.cornerAngle]
    rw [show (f : Plane → Plane) = f.toRealAffineIsometryEquiv from
      (IsometryEquiv.coeFn_toRealAffineIsometryEquiv f).symm]
    exact f.toRealAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _
  -- `σ` sends `{k+1, k+2}` onto `{σ k + 1, σ k + 2}`, in one order or the other
  have hidx : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
      (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by decide
  have hne : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  obtain ⟨h1, h2, h12⟩ := hne k
  rcases hidx (σ k) (σ (k + 1)) (σ (k + 2))
      (fun he => h1 (σ.injective he)) (fun he => h2 (σ.injective he))
      (fun he => h12 (σ.injective he)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← ha, ← hb]; exact hmap
  · rw [← ha, ← hb]
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]
    exact hmap

/-- **Each congruent tile has exactly one corner of each model angle.**  Given that the model's
three corner angles are pairwise distinct, the count of a tile's corners carrying a given model
angle is exactly `1`.  This is the per-tile input of the corner-incidence double count behind
`lem:census`: summing it over the `N` tiles gives `N` corners of each type. -/
theorem Tri.Congruent.corner_count_eq_one {T U : Tri} (h : T.Congruent U)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
        = cornerAngle (T.pts (l + 1)) (T.pts l) (T.pts (l + 2)) → k = l)
    (k : Fin 3) :
    ({j | cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))} : Finset (Fin 3)).card = 1 := by
  classical
  obtain ⟨σ, hperm⟩ := h.cornerAngle_perm
  refine Finset.card_eq_one.mpr ⟨σ k, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    have hm := hperm (σ.symm j)
    rw [Equiv.apply_symm_apply] at hm
    have : cornerAngle (T.pts (σ.symm j + 1)) (T.pts (σ.symm j)) (T.pts (σ.symm j + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by rw [← hm]; exact hj
    have hk := hdist _ _ this
    rw [← hk, Equiv.apply_symm_apply]
  · intro hj; subst hj; exact hperm k

/-- **`N` corners of each type.**  Summing the per-tile count over the dissection: in a
`CongruentDissection` whose model has pairwise distinct corner angles, the tiles carry exactly `N`
corners of each of the three angles.  This is the tile side of `lem:census`'s corner-incidence
double count; the vertex side counts the same corners grouped by the point they sit at. -/
theorem congruentDissection_corner_total {N : ℕ} (D : CongruentDissection N)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
        = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2)) → k = l)
    (k : Fin 3) :
    ∑ i : Fin N, ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j)
          ((D.tile i).pts (j + 2))
        = cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))}
        : Finset (Fin 3)).card = N := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => ((D.tiles_congruent i).symm).corner_count_eq_one hdist k)]
  simp

open Classical in
/-- The finite set of all points that are a vertex of some tile. -/
noncomputable def cornerPts {N : ℕ} (D : Dissection N) : Finset Plane :=
  Finset.univ.biUnion (fun i : Fin N => Finset.univ.image (fun j : Fin 3 => (D.tile i).pts j))

theorem mem_cornerPts {N : ℕ} (D : Dissection N) (i : Fin N) (j : Fin 3) :
    (D.tile i).pts j ∈ cornerPts D := by
  classical
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩

/-- **One tile's corners of a given angle, counted at points instead of indices.**  For an angle
that is not `0`, `π` or `2π`, a tile has local angle `θ` exactly at those of its own vertices whose
corner angle is `θ`, and its vertices are distinct — so the two counts agree. -/
theorem tile_corner_card {N : ℕ} (D : Dissection N) (i : Fin N) (θ : ℝ)
    (h0 : θ ≠ 0) (hpi : θ ≠ Real.pi) (h2pi : θ ≠ 2 * Real.pi) :
    ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ}
        : Finset (Fin 3)).card
      = ({v ∈ cornerPts D | (D.tile i).localAngle v = θ} : Finset Plane).card := by
  classical
  have himg : ({v ∈ cornerPts D | (D.tile i).localAngle v = θ} : Finset Plane)
      = ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ}
          : Finset (Fin 3)).image (D.tile i).pts := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hang⟩
      rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with
        ⟨j, hj, hval⟩ | h | h | h
      · exact ⟨j, by rw [← hval]; exact hang, hj.symm⟩
      · exact absurd (h ▸ hang) (Ne.symm h2pi)
      · exact absurd (h ▸ hang) (Ne.symm hpi)
      · exact absurd (h ▸ hang) (Ne.symm h0)
    · rintro ⟨j, hj, rfl⟩
      exact ⟨mem_cornerPts D i j, by rw [Erdos634.Geometry.Tri.localAngle_vertex]; exact hj⟩
  rw [himg, Finset.card_image_of_injective _ (D.tile i).indep.injective]

/-- **The corner-incidence double count.**  The corners of angle `θ` counted tile-by-tile equal the
same corners counted point-by-point.  This is the exchange `lem:census`'s corner balance rests on;
with `congruentDissection_corner_total` the left side is `N`. -/
theorem corner_double_count {N : ℕ} (D : Dissection N) (θ : ℝ)
    (h0 : θ ≠ 0) (hpi : θ ≠ Real.pi) (h2pi : θ ≠ 2 * Real.pi) :
    ∑ i : Fin N,
        ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ}
          : Finset (Fin 3)).card
      = ∑ v ∈ cornerPts D, ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => tile_corner_card D i θ h0 hpi h2pi)]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- **The corner balance, for a real congruent dissection.**  For each of the model's three corner
angles, the multiplicities of that angle summed over all vertex points of the dissection equal `N`.

This is the corner-incidence identity `lem:census` balances "across the `N` tiles", obtained here as
a theorem rather than assumed: the tile side is `congruentDissection_corner_total` (each tile has
exactly one corner of each angle), the exchange is `corner_double_count`. -/
theorem congruentDissection_corner_balance {N : ℕ} (D : CongruentDissection N)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
        = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2)) → k = l)
    (k : Fin 3)
    (h0 : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) ≠ 0)
    (hpi : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) ≠ Real.pi)
    (h2pi : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
      ≠ 2 * Real.pi) :
    ∑ v ∈ cornerPts D.toDissection,
        ({i | (D.tile i).localAngle v
          = cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))}
          : Finset (Fin N)).card = N := by
  classical
  rw [← corner_double_count D.toDissection _ h0 hpi h2pi]
  exact congruentDissection_corner_total D hdist k

/-- **`hvals` at every point.**  For a `CongruentDissection`, *any* tile's local angle at *any*
point of the plane is one of `α`, `β`, `γ`, `π`, `2π`, `0`.

`TileAt.congruentDissection_localAngle_mem` proves this only at the target's own vertices, and the
`hvals` hypothesis it discharges there is carried unproved at general points throughout the corpus
(the vertex-figure lemmas of `VertexFigureReal` all take it). The general statement needs nothing
more: `PinPlumbing.localAngle_cases` splits four ways, and in the corner branch
`CongruentAngles.congruent_corner_angles` sends the tile's own corner angle to one of the model's
three. -/
theorem congruentDissection_localAngle_mem_all {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (v : Plane) (i : Fin N) :
    (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ) := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with
    ⟨j, -, hval⟩ | h2pi | hpi | h0
  · obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
    rw [hval, hk]
    have hall : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
    have hk3 := hall k
    rcases hk3 with rfl | rfl | rfl
    · rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hα]; simp
    · rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, hβ]; simp
    · rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hγ]; simp
  · rw [h2pi]; simp
  · rw [hpi]; simp
  · rw [h0]; simp

/-- **The interior vertex figure of a real congruent dissection.**  At any interior point of the
target, the multiplicities of `α, β, γ, π, 2π` among the tiles are one of the listed solutions: a
single covering tile, two straight angles, one straight angle with a boundary figure, or one of the
four interior figures.

`VertexFigureReal.interior_figure_cases_gen` proves the classification from the multiplicity
equation, and `.interior_multiplicities_cards` proves that equation from `hvals` — but nothing in
the corpus had ever supplied `hvals` at a general interior point, so the classification had never
been instantiated for a real dissection. `congruentDissection_localAngle_mem_all` supplies it, and
this is the composition. -/
theorem congruentDissection_interior_figure_cases {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ interior D.target.carrier) :
    (({i | (D.tile i).localAngle v = 2 * Real.pi} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle v = 2 * Real.pi} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle v = 2 * Real.pi} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 1 ∧
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 3 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 2 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
       (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1))) ∨
    (({i | (D.tile i).localAngle v = 2 * Real.pi} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 0 ∧
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 6 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 4 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
       (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 4 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 3 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1) ∨
       (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 2 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 2 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 2) ∨
       (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 0 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 3))) := by
  classical
  have hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem_all D α β γ hmα hmβ hmγ v i
  have hsum := Erdos634.VertexFigureReal.interior_multiplicities_cards D.toDissection α β γ
    hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hv hvals
  exact Erdos634.VertexFigureReal.interior_figure_cases_gen hγdef hrel hirr _ _ _ _ _ hsum

/-- **`hvals` in the `2π`-free form, at any tile vertex.**  At a point that is a vertex of some
tile, no tile can cover the point, so every tile's local angle there lies in `{α, β, γ, π, 0}`.

This is the exact shape carried as an unproved hypothesis by `MarchRun.junction_dichotomy`,
`JunctionWedge`, and the other junction lemmas — the wider set of
`congruentDissection_localAngle_mem_all` does not fit them, because they need `2π` excluded. -/
theorem congruentDissection_localAngle_mem_at_corner {N : ℕ} (D : CongruentDissection N)
    (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (j : Fin N) (m : Fin 3) (hvj : (D.tile j).pts m = v) (i : Fin N) :
    (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
  classical
  have hmemj : v ∈ (D.tile j).carrier := by
    rw [← hvj, Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨m, rfl⟩
  have hnotint : v ∉ interior (D.tile i).carrier := by
    by_cases hij : i = j
    · subst hij; rw [← hvj]; exact _root_.Erdos634.Geometry.Dissection.target_vertex_not_interior _ m
    · exact fun hint =>
        Erdos634.RouteOne.Dissection.not_mem_interior_of_mem D.toDissection (Ne.symm hij) hmemj hint
  have h2pi := _root_.Erdos634.Geometry.Dissection.localAngle_ne_two_pi_of_not_mem_interior hnotint
  have hmem := congruentDissection_localAngle_mem_all D α β γ hmα hmβ hmγ v i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
  rcases hmem with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact absurd h h2pi
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **A frontier junction with no straight angle is a tile vertex.**  If no tile presents `π` at a
frontier point, then some tile has that point as one of its own vertices: a tile containing it has
nonzero local angle there, and the `2π` and `π` branches are excluded — `2π` because a tile's
interior lies in the target's interior, which misses the frontier. -/
theorem frontier_junction_is_vertex {N : ℕ} (D : Dissection N) {v : Plane}
    (hv : v ∈ frontier D.target.carrier)
    (hns : ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 0) :
    ∃ (j : Fin N) (m : Fin 3), (D.tile j).pts m = v := by
  classical
  have hvt : v ∈ D.target.carrier := (D.target.isCompact.isClosed.closure_eq ▸ hv.1)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (show v ∈ ⋃ i, (D.tile i).carrier by rw [D.covers]; exact hvt)
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile j) v with
    ⟨m, hm, -⟩ | h2pi | hpi | h0
  · exact ⟨j, m, hm.symm⟩
  · exfalso
    have hint : v ∈ interior (D.tile j).carrier := by
      rw [Erdos634.Geometry.Tri.localAngle] at h2pi
      split at h2pi
      · rename_i hvx
        have hle := EuclideanGeometry.angle_le_pi ((D.tile j).pts (hvx.choose + 1))
          ((D.tile j).pts hvx.choose) ((D.tile j).pts (hvx.choose + 2))
        rw [Erdos634.Geometry.cornerAngle] at h2pi
        rw [h2pi] at hle; linarith [Real.pi_pos]
      · split at h2pi
        · rename_i hpos
          exact (D.tile j).mem_interior_iff_coord_pos v |>.mpr hpos
        · split at h2pi
          · have := Real.pi_pos; linarith
          · have := Real.pi_pos; linarith
    exact hv.2 (interior_mono (tile_subset_target D j) hint)
  · exfalso
    have : j ∈ ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)) := by simp [hpi]
    rw [Finset.card_eq_zero] at hns
    simp [hns] at this
  · exact absurd h0 (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hj)

/-- **The junction dichotomy for a real congruent dissection**, with `hvals` discharged.  At a
frontier point that is not a target corner and carries no straight angle, the figure is exactly
`{3α, 2β}` or `{α, β, γ}`.

`MarchRun.junction_dichotomy` proves this from `hvals`, which no caller had ever supplied for a real
dissection (the `rem:marchobl` M-i row records it as still carried). Here it is supplied:
`frontier_junction_is_vertex` makes the point a tile vertex, and
`congruentDissection_localAngle_mem_at_corner` then gives the `2π`-free membership. -/
theorem congruentDissection_junction_dichotomy {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hns : ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 0) :
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 3 ∧
     ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 2 ∧
     ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0)
    ∨
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
     ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1) := by
  classical
  obtain ⟨j, m, hjm⟩ := frontier_junction_is_vertex D.toDissection hv hns
  exact Erdos634.MarchRun.junction_dichotomy D.toDissection hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0
    hπ0 hγdef hrel hirr hv hnv
    (fun i => congruentDissection_localAngle_mem_at_corner D α β γ hmα hmβ hmγ j m hjm i) hns

/-- **A tile presenting a corner-sized angle at a point has that point as a vertex.** -/
theorem vertex_of_localAngle_corner (T : Tri) {v : Plane} {θ : ℝ} (h : T.localAngle v = θ)
    (h0 : θ ≠ 0) (hpi : θ ≠ Real.pi) (h2pi : θ ≠ 2 * Real.pi) :
    ∃ m : Fin 3, T.pts m = v := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases T v with ⟨m, hm, -⟩ | hb | hb | hb
  · exact ⟨m, hm.symm⟩
  · exact absurd (h.symm.trans hb) h2pi
  · exact absurd (h.symm.trans hb) hpi
  · exact absurd (h.symm.trans hb) h0

/-- **The march-junction figure for a real congruent dissection**, with `hvals` discharged.
`JunctionWedge.march_junction_real` takes `hvals` as a hypothesis; here the `γ`-witness it already
requires does the work — a tile presenting `γ` has the point as a vertex, and
`congruentDissection_localAngle_mem_at_corner` then supplies the membership. -/
theorem congruentDissection_march_junction_real {N : ℕ} (D : CongruentDissection N)
    (o : Orientation ℝ Plane (Fin 2)) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hγ2π : γ ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hβpos : 0 < β) (hαpos : 0 < α)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
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
  classical
  obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile iγ) hiγ hγ0 hγπ hγ2π
  exact Erdos634.JunctionWedge.march_junction_real D.toDissection o hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 hγdef hrel hirr hβpos hαpos hv hnv
    (fun i => congruentDissection_localAngle_mem_at_corner D α β γ hmα hmβ hmγ iγ m hm i)
    iγ hiγ hu hP hQ hφ hψ hφm hψm hcorner

/-- **The interior figure at a tile vertex.**  At an interior point that is a vertex of some tile,
two of the four branches of `congruentDissection_interior_figure_cases` are impossible: no tile can
cover the point (`u = 1`), and two straight angles would exhaust the `2π` and leave no room for the
tile owning the vertex (`s = 2`).  What remains is exactly the census's classification — a straight
figure `{3α,2β}` or `{α,β,γ}`, or one of the four interior figures. -/
theorem congruentDissection_interior_figure_at_corner {N : ℕ} (D : CongruentDissection N)
    (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ interior D.target.carrier)
    (j : Fin N) (m : Fin 3) (hjm : (D.tile j).pts m = v) :
    (({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 1 ∧
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 3 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 2 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
       (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1))) ∨
    (({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 0 ∧
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 6 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 4 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
       (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 4 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 3 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1) ∨
       (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 2 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 2 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 2) ∨
       (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 0 ∧
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 3))) := by
  classical
  -- the tile owning the vertex presents a corner angle, so it is not a straight-angle tile
  have hjne : (D.tile j).localAngle v ≠ Real.pi := by
    rw [← hjm, Erdos634.Geometry.Tri.localAngle_vertex]
    obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent j).symm m
    rw [hk]
    have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    rcases hall k with rfl | rfl | rfl
    · rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hαπ
    · rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, hmβ]; exact hβπ
    · rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hmγ]; exact hγπ
  rcases congruentDissection_interior_figure_cases D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
    hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr hv with
    ⟨hu, -, -, -, -⟩ | ⟨-, hs2, -, -, -⟩ | ⟨-, hs1, hcase⟩ | ⟨-, hs0, hcase⟩
  · -- `u = 1`: some tile covers the point, impossible at a tile vertex
    exfalso
    have hpos : 0 < ({i | (D.tile i).localAngle v = 2 * Real.pi} : Finset (Fin N)).card := by
      rw [hu]; norm_num
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hmem := congruentDissection_localAngle_mem_at_corner D α β γ hmα hmβ hmγ j m hjm i
    rw [hi] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    · exact hα2π h.symm
    · exact hβ2π h.symm
    · exact hγ2π h.symm
    · exact hπ2π h.symm
    · exact h2π0 h
  · -- `s = 2`: two straight angles leave no room for the tile owning the vertex
    exfalso
    have hlt : 1 < ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card := by
      rw [hs2]; norm_num
    obtain ⟨i, hi, i', hi', hii'⟩ := Finset.one_lt_card.mp hlt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    have hmemj : v ∈ (D.tile j).carrier := by
      rw [← hjm, Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨m, rfl⟩
    exact Erdos634.RouteOne.two_through_excludes_mem D.toDissection hv i i' j hii'
      (fun h => hjne (h ▸ hi)) (fun h => hjne (h ▸ hi')) hi hi' hmemj
  · exact Or.inl ⟨hs1, hcase⟩
  · exact Or.inr ⟨hs0, hcase⟩

/-- **The corner angle a tile presents at its own vertex is one of the model's three.** -/
theorem localAngle_at_own_vertex_mem {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (j : Fin N) (m : Fin 3) :
    (D.tile j).localAngle ((D.tile j).pts m) = α ∨
    (D.tile j).localAngle ((D.tile j).pts m) = β ∨
    (D.tile j).localAngle ((D.tile j).pts m) = γ := by
  rw [Erdos634.Geometry.Tri.localAngle_vertex]
  obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent j).symm m
  rw [hk]
  have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hall k with rfl | rfl | rfl
  · left
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
    exact hmα
  · right; left
    rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
    exact hmβ
  · right; right
    rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
    exact hmγ

/-- **The boundary figure at a tile vertex.**  At a frontier point that is a tile vertex but not a
target corner, the degenerate branch of `TileAt.congruentDissection_boundary_figure_cases` — a lone
straight angle with no corner angles at all — is impossible, because the tile owning the vertex
presents `α`, `β` or `γ` there.  The figure is `{3α,2β}` or `{α,β,γ}`: the census's `n₂` and `n₁`. -/
theorem congruentDissection_boundary_figure_at_corner {N : ℕ} (D : CongruentDissection N)
    (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (j : Fin N) (m : Fin 3) (hjm : (D.tile j).pts m = v) :
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 3 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1) := by
  classical
  rcases Erdos634.Geometry.Dissection.congruentDissection_boundary_figure_cases D α β γ
    hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ hv hnv with
    ⟨-, hα0', hβ0', hγ0'⟩ | h2 | h3
  · exfalso
    have hj := localAngle_at_own_vertex_mem D α β γ hmα hmβ hmγ j m
    rw [hjm] at hj
    rcases hj with h | h | h
    · have : j ∈ ({i | (D.tile i).localAngle v = α} : Finset (Fin N)) := by simp [h]
      rw [Finset.card_eq_zero] at hα0'; simp [hα0'] at this
    · have : j ∈ ({i | (D.tile i).localAngle v = β} : Finset (Fin N)) := by simp [h]
      rw [Finset.card_eq_zero] at hβ0'; simp [hβ0'] at this
    · have : j ∈ ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)) := by simp [h]
      rw [Finset.card_eq_zero] at hγ0'; simp [hγ0'] at this
  · exact Or.inl h2
  · exact Or.inr h3

/-- **Every tile vertex is a target corner, a frontier non-corner, or an interior point.**  The
three cases the classification handles: `TileAt.congruentDissection_apex_counts` /
`.congruentDissection_base_corner_counts` at the target's own corners,
`congruentDissection_boundary_figure_at_corner` on the rest of the frontier, and
`congruentDissection_interior_figure_at_corner` inside.  This is the coverage half of the partition
`lem:census` needs. -/
theorem cornerPts_trichotomy {N : ℕ} (D : Dissection N) {v : Plane} (hv : v ∈ cornerPts D) :
    v ∈ Set.range D.target.pts ∨
    (v ∈ frontier D.target.carrier ∧ v ∉ Set.range D.target.pts) ∨
    v ∈ interior D.target.carrier := by
  classical
  -- a tile vertex lies in the target
  have hvt : v ∈ D.target.carrier := by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hi
    refine tile_subset_target D i ?_
    rw [← hm, Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨m, rfl⟩
  by_cases hint : v ∈ interior D.target.carrier
  · exact Or.inr (Or.inr hint)
  · have hfr : v ∈ frontier D.target.carrier := by
      rw [(D.target.isCompact.isClosed).frontier_eq]
      exact ⟨hvt, hint⟩
    by_cases hcorner : v ∈ Set.range D.target.pts
    · exact Or.inl hcorner
    · exact Or.inr (Or.inl ⟨hfr, hcorner⟩)

/-! ## The summation engine for the census partition

The census identities all have the shape "sum a per-point weight over all tile vertices, and it
equals a linear combination of the class counts".  With the classes being the fibres of the
multiplicity vector, that is a general fact about summing a fibre-constant function. -/

/-- **Summing a fibre-constant weight.**  If `g` depends on `x` only through `f x`, the sum of `g`
over `s` is the class-count combination `∑ y, c y * |fibre y|`. -/
theorem sum_over_fibers_const {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (f : ι → κ) (hmaps : ∀ x ∈ s, f x ∈ t) (g : ι → ℕ) (c : κ → ℕ)
    (hconst : ∀ x ∈ s, g x = c (f x)) :
    ∑ x ∈ s, g x = ∑ y ∈ t, c y * (s.filter (fun x => f x = y)).card := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmaps g]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have : ∀ x ∈ s.filter (fun x => f x = y), g x = c y := by
    intro x hx
    obtain ⟨hxs, hxy⟩ := Finset.mem_filter.mp hx
    rw [hconst x hxs, hxy]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- The `(α, β, γ)`-multiplicity vector at a point: the census's class label. -/
noncomputable def figureVec {N : ℕ} (D : Dissection N) (α β γ : ℝ) (v : Plane) : ℕ × ℕ × ℕ := by
  classical
  exact (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card)

/-- The eight class labels of `lem:census`: apex `{3α}`, base corner `{β}`, the two straight figures
`{α,β,γ}` and `{3α,2β}`, and the four interior figures `{β,3γ}`, `{2α,2β,2γ}`, `{4α,3β,γ}`,
`{6α,4β}`.  All eight vectors are distinct, so the classes are automatically disjoint. -/
def censusLabels : Finset (ℕ × ℕ × ℕ) :=
  {(3, 0, 0), (0, 1, 0), (1, 1, 1), (3, 2, 0), (0, 1, 3), (2, 2, 2), (4, 3, 1), (6, 4, 0)}

theorem censusLabels_card : censusLabels.card = 8 := by decide

/-- **Every tile vertex carries one of the eight census labels.**  The maps-to obligation of the
partition: `cornerPts_trichotomy` splits the point three ways, and the three classification
theorems — `TileAt.congruentDissection_apex_counts` / `.congruentDissection_base_corner_counts` at
the target's corners, `congruentDissection_boundary_figure_at_corner` on the rest of the frontier,
`congruentDissection_interior_figure_at_corner` inside — land each case on one of the eight labels.

`htarget` is the base-`β` target's own shape: each of its corners is the apex `3α` or a base `β`. -/
theorem figureVec_mem_censusLabels {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β)
    {v : Plane} (hv : v ∈ cornerPts D.toDissection) :
    ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
      ∈ censusLabels := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
  rcases cornerPts_trichotomy D.toDissection hv with hc | ⟨hfr, hnv⟩ | hint
  · obtain ⟨k, hk⟩ := hc
    subst hk
    rcases htarget k with h3 | hb
    · obtain ⟨ha, hb', hc', -⟩ := Erdos634.Geometry.Dissection.congruentDissection_apex_counts D
        α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k h3
      simp [censusLabels, ha, hb', hc']
    · obtain ⟨ha, hb', hc', -⟩ :=
        Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D
        α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k hb
      simp [censusLabels, ha, hb', hc']
  · rcases congruentDissection_boundary_figure_at_corner D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ hfr hnv j m hm with
      ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
    · simp [censusLabels, ha, hb, hc]
    · simp [censusLabels, ha, hb, hc]
  · rcases congruentDissection_interior_figure_at_corner D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ
      hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr hint j m hm with
      ⟨-, hcase⟩ | ⟨-, hcase⟩
    · rcases hcase with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;> simp [censusLabels, ha, hb, hc]
    · rcases hcase with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;>
        simp [censusLabels, ha, hb, hc]

/-- The model's three corner angles are pairwise distinct, indexed. -/
theorem model_corner_dist {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    ∀ k l : Fin 3,
      cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
        = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2)) → k = l := by
  have e0 : (0 : Fin 3) + 1 = 1 := rfl
  have e0' : (0 : Fin 3) + 2 = 2 := rfl
  have e1 : (1 : Fin 3) + 1 = 2 := rfl
  have e1' : (1 : Fin 3) + 2 = 0 := rfl
  have e2 : (2 : Fin 3) + 1 = 0 := rfl
  have e2' : (2 : Fin 3) + 2 = 1 := rfl
  have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  intro k l h
  rcases hall k with rfl | rfl | rfl <;> rcases hall l with rfl | rfl | rfl <;>
    simp only [e0, e0', e1, e1', e2, e2', hmα, hmβ, hmγ] at h <;>
    first
      | rfl
      | exact absurd h hαβ
      | exact absurd h hαγ
      | exact absurd h hβγ
      | exact absurd h.symm hαβ
      | exact absurd h.symm hαγ
      | exact absurd h.symm hβγ

/-- **The `α`-identity of the census, as a sum over the eight classes.**  Instantiating
`sum_over_fibers_const` with the `α`-multiplicity as weight and the label's own first coordinate as
the class constant, against `congruentDissection_corner_balance`'s total of `N`.

This is `lem:census`'s `α`-identity in the form the partition produces it; matching it to
`OrderForcing.vertex_census`'s `ha` needs only the target's corner counts (one apex, two base
corners). -/
theorem census_alpha_sum {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ∑ y ∈ censusLabels, y.1 *
        ((cornerPts D.toDissection).filter (fun v =>
          ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
            ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
            ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ) = y)).card
      = N := by
  classical
  rw [← sum_over_fibers_const (cornerPts D.toDissection) censusLabels _
    (fun v hv => figureVec_mem_censusLabels D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
      hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget hv)
    (fun v => ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card)
    (fun y => y.1) (fun _ _ => rfl)]
  have hbal := congruentDissection_corner_balance D
    (model_corner_dist D hmα hmβ hmγ hαβ hαγ hβγ) 0
    (by rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hα0)
    (by rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hαπ)
    (by rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hα2π)
  rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα] at hbal
  exact hbal

/-- **The base-`β` target has exactly one apex corner.**  Given that each of the target's corners is
`3α` or `β`, the angle sum `3α + 2β = π` and the irrationality of `α/π` force the split to be one
apex and two base corners — the counts `lem:census` writes as the constants `3` and `0` in its
identities.  Not an extra assumption: two apexes, three apexes, or none each force `α = π/9`. -/
theorem target_corner_counts {N : ℕ} (D : CongruentDissection N) {α β : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α}
      : Finset (Fin 3)).card = 1 := by
  classical
  have hne : β ≠ 3 * α := by
    intro h
    exact hirr ⟨1/9, by rw [h] at hrel; push_cast; linarith⟩
  have hnine : α ≠ (1/9 : ℝ) * Real.pi := by
    intro h; exact hirr ⟨1/9, by push_cast; exact h⟩
  have hsum := Erdos634.Geometry.cornerAngle_sum D.target
  have e0 : (0 : Fin 3) + 1 = 1 := rfl
  have e0' : (0 : Fin 3) + 2 = 2 := rfl
  have e1 : (1 : Fin 3) + 1 = 2 := rfl
  have e1' : (1 : Fin 3) + 2 = 0 := rfl
  have e2 : (2 : Fin 3) + 1 = 0 := rfl
  have e2' : (2 : Fin 3) + 2 = 1 := rfl
  have h0 := htarget 0
  have h1 := htarget 1
  have h2 := htarget 2
  simp only [e0, e0', e1, e1', e2, e2'] at h0 h1 h2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rw [h0, h1, h2] at hsum
  all_goals (
    first
      | (exfalso; apply hnine; linarith)
      | (rw [Finset.card_eq_one]
         refine ⟨0, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
         · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           rw [e0, e0']; exact h0
         · intro k hk
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
           have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
           rcases hall k with rfl | rfl | rfl
           · rfl
           · rw [e1, e1'] at hk; rw [h1] at hk; exact absurd hk hne
           · rw [e2, e2'] at hk; rw [h2] at hk; exact absurd hk hne)
      | (rw [Finset.card_eq_one]
         refine ⟨1, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
         · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           rw [e1, e1']; exact h1
         · intro k hk
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
           have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
           rcases hall k with rfl | rfl | rfl
           · rw [e0, e0'] at hk; rw [h0] at hk; exact absurd hk hne
           · rfl
           · rw [e2, e2'] at hk; rw [h2] at hk; exact absurd hk hne)
      | (rw [Finset.card_eq_one]
         refine ⟨2, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
         · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           rw [e2, e2']; exact h2
         · intro k hk
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
           have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
           rcases hall k with rfl | rfl | rfl
           · rw [e0, e0'] at hk; rw [h0] at hk; exact absurd hk hne
           · rw [e1, e1'] at hk; rw [h1] at hk; exact absurd hk hne
           · rfl))

/-- **Only the apex label has `β`-count zero.**  Among the eight census labels, `(3,0,0)` is the
only one whose middle coordinate is `0`; so a tile vertex with no tile presenting `β` must be one of
the target's own corners, and its corner angle is `3α`. -/
theorem beta_free_is_apex {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ cornerPts D.toDissection)
    (hβcount : ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 0) :
    ∃ k : Fin 3, D.target.pts k = v ∧
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) ≠ β := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
  rcases cornerPts_trichotomy D.toDissection hv with hc | ⟨hfr, hnv⟩ | hint
  · obtain ⟨k, hk⟩ := hc
    refine ⟨k, hk, ?_⟩
    intro hβcorner
    obtain ⟨-, hb, -, -⟩ := Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D
      α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k hβcorner
    rw [hk] at hb
    omega
  · exfalso
    rcases congruentDissection_boundary_figure_at_corner D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ hfr hnv j m hm with
      ⟨-, hb, -⟩ | ⟨-, hb, -⟩ <;> omega
  · exfalso
    rcases congruentDissection_interior_figure_at_corner D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ
      hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr hint j m hm with
      ⟨-, hcase⟩ | ⟨-, hcase⟩
    · rcases hcase with ⟨-, hb, -⟩ | ⟨-, hb, -⟩ <;> omega
    · rcases hcase with ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ <;> omega

/-- **The apex class has exactly one point.**  Combining `target_corner_counts` (one target corner
carries `3α`) with `beta_free_is_apex` (only the apex label has `β`-count `0`) and
`TileAt.congruentDissection_apex_counts` (the apex carries `(3,0,0)`): the fibre of the label
`(3,0,0)` in `cornerPts` is the single apex point.  This is the constant `3` in `lem:census`'s
`α`-identity. -/
theorem apex_fibre_card {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (3, 0, 0))).card = 1 := by
  classical
  obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp (target_corner_counts D hrel hirr htarget)
  have hmem₀ : cornerAngle (D.target.pts (k₀ + 1)) (D.target.pts k₀) (D.target.pts (k₀ + 2))
      = 3 * α := by
    have : k₀ ∈ ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
        = 3 * α} : Finset (Fin 3)) := by rw [hk₀]; exact Finset.mem_singleton_self k₀
    simpa using this
  obtain ⟨ha, hb, hc, -⟩ := Erdos634.Geometry.Dissection.congruentDissection_apex_counts D
    α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k₀ hmem₀
  -- the apex is a tile vertex, since some tile presents `α` there
  have hapexmem : D.target.pts k₀ ∈ cornerPts D.toDissection := by
    have hpos : 0 < ({i | (D.tile i).localAngle (D.target.pts k₀) = α} : Finset (Fin N)).card := by
      rw [ha]; norm_num
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) hi hα0 hαπ hα2π
    rw [← hm]; exact mem_cornerPts D.toDissection i m
  refine Finset.card_eq_one.mpr ⟨D.target.pts k₀, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · simp only [Finset.mem_filter]
    exact ⟨hapexmem, by rw [ha, hb, hc]⟩
  · intro v hv
    obtain ⟨hvmem, hvlab⟩ := Finset.mem_filter.mp hv
    have hβ0' : ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 0 := by
      have := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hvlab
      simpa using this
    obtain ⟨k, hk, hkne⟩ := beta_free_is_apex D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
      hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr hvmem hβ0'
    have hk3 : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α :=
      (htarget k).resolve_right hkne
    have : k ∈ ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
        = 3 * α} : Finset (Fin 3)) := by simpa using hk3
    rw [hk₀, Finset.mem_singleton] at this
    rw [← hk, this]

/-- **The base-corner class has exactly two points.**  The discriminator is `α`-count `0` together
with `γ`-count `0`: among the eight labels those two conditions hold only for `(0,1,0)`.  With
`target_corner_counts` giving one apex, the other two target corners carry `β`, and the target's
vertices are distinct — so the fibre has two points.  This is the constant `2` in `lem:census`'s
`β`-identity. -/
theorem base_fibre_card {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (0, 1, 0))).card = 2 := by
  classical
  have hne : β ≠ 3 * α := fun h => hirr ⟨1/9, by rw [h] at hrel; push_cast; linarith⟩
  -- the two base corners, as a `Finset (Fin 3)` of size two
  have hsplit : ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β} : Finset (Fin 3)).card = 2 := by
    have hfil : ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
        (D.target.pts (k + 2)) = β} : Finset (Fin 3))
        = Finset.univ.filter (fun k => ¬ (cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
          (D.target.pts (k + 2)) = 3 * α)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h h3; exact hne (h ▸ h3)
      · intro h; exact (htarget k).resolve_left h
    have hcard := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 3)))
      (p := fun k => cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
        (D.target.pts (k + 2)) = 3 * α)
    rw [hfil]
    have h1 := target_corner_counts D hrel hirr htarget
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  -- the fibre is the image of those two corners
  have himg : ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ) = (0, 1, 0)))
      = ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
          (D.target.pts (k + 2)) = β} : Finset (Fin 3)).image D.target.pts := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hvmem, hvlab⟩
      have hαc : ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 0 := by
        have := congrArg (fun p : ℕ × ℕ × ℕ => p.1) hvlab; simpa using this
      have hγc : ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0 := by
        have := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hvlab; simpa using this
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hvmem
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
      rcases cornerPts_trichotomy D.toDissection hvmem with hc | ⟨hfr, hnv⟩ | hint
      · obtain ⟨k, hk⟩ := hc
        refine ⟨k, ?_, hk⟩
        rcases htarget k with h3 | hb
        · exfalso
          obtain ⟨ha, -, -, -⟩ := Erdos634.Geometry.Dissection.congruentDissection_apex_counts D
            α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k h3
          rw [hk] at ha; omega
        · exact hb
      · exfalso
        rcases congruentDissection_boundary_figure_at_corner D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
          hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ hfr hnv j m hm with
          ⟨ha, -, -⟩ | ⟨ha, -, -⟩ <;> omega
      · exfalso
        rcases congruentDissection_interior_figure_at_corner D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ
          hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr hint j m hm with
          ⟨-, hcase⟩ | ⟨-, hcase⟩
        · rcases hcase with ⟨ha, -, -⟩ | ⟨ha, -, -⟩ <;> omega
        · rcases hcase with ⟨ha, -, hc⟩ | ⟨ha, -, hc⟩ | ⟨ha, -, hc⟩ | ⟨ha, -, hc⟩ <;> omega
    · rintro ⟨k, hkβ, rfl⟩
      obtain ⟨ha, hb, hc, -⟩ :=
        Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D
        α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k
        (by simpa using hkβ)
      refine ⟨?_, by rw [ha, hb, hc]⟩
      have hpos : 0 < ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card := by
        rw [hb]; norm_num
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨m', hm'⟩ := vertex_of_localAngle_corner (D.tile i) hi hβ0 hβπ hβ2π
      rw [← hm']; exact mem_cornerPts D.toDissection i m'
  rw [himg, Finset.card_image_of_injective _ D.target.indep.injective, hsplit]

end Erdos634.Geometry
