import Erdos634.Congruence
import Erdos634.PinPlumbing
import Erdos634.VertexFigureReal
import Erdos634.RouteOne
import Erdos634.TileAt
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

end Erdos634.Geometry
