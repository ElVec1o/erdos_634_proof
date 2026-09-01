import Erdos634.Dissection
import Erdos634.MarchFlank
import Erdos634.CongruentAngles
import Erdos634.TilePlacement
import Erdos634.WallEndpoints
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

/-! ## Existence at a corner: a tile with nonzero, non-`2π` local angle

`tileAt` cannot reach a target vertex (the section above). But existence of *a* covering tile with
a well-behaved local angle there does not need uniqueness — and both nonvanishing and `≠ 2π` are
now available cheaply: nonvanishing from `MarchFlank.localAngle_ne_zero_of_mem`, and `≠ 2π`
directly from `target_vertex_not_interior_tile`, since the `2π` branch of `Tri.localAngle` is
definitionally the all-coordinates-positive (interior) case. This is existence, not the corner
census's uniqueness content (`lem:census`) — recorded honestly as such. -/

/-- **A tile's local angle at an interior-only point is never `2π`.**  The `2π` branch of
`Tri.localAngle` is exactly membership in the interior. -/
theorem localAngle_ne_two_pi_of_not_mem_interior {T : Erdos634.Geometry.Tri} {p : Plane}
    (hp : p ∉ interior T.carrier) : T.localAngle p ≠ 2 * Real.pi := by
  classical
  intro h2
  rw [Erdos634.Geometry.Tri.localAngle] at h2
  split at h2
  · rename_i hv
    have hle := EuclideanGeometry.angle_le_pi ((T.pts (hv.choose + 1)))
      (T.pts hv.choose) (T.pts (hv.choose + 2))
    have hpi := Real.pi_pos
    rw [Erdos634.Geometry.cornerAngle] at h2
    rw [h2] at hle; linarith
  · split at h2
    · rename_i hall
      exact hp (T.mem_interior_iff_coord_pos p |>.mpr hall)
    · split at h2 <;> [skip; skip] <;>
        first
          | (exfalso; have := Real.pi_pos; linarith)
          | (exfalso; have := Real.pi_pos; linarith)

/-- **At a target vertex, some tile covers it with local angle neither `0` nor `2π`.** -/
theorem exists_corner_tile (D : Dissection N) (k : Fin 3) :
    ∃ i : Fin N, D.target.pts k ∈ (D.tile i).carrier ∧
      (D.tile i).localAngle (D.target.pts k) ≠ 0 ∧
      (D.tile i).localAngle (D.target.pts k) ≠ 2 * Real.pi := by
  have hk : D.target.pts k ∈ D.target.carrier :=
    subset_convexHull ℝ _ (Set.mem_range_self k)
  obtain ⟨i, hi⟩ := D.exists_tile_mem hk
  exact ⟨i, hi, Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hi,
    localAngle_ne_two_pi_of_not_mem_interior (D.target_vertex_not_interior_tile k i)⟩

/-! ## Every tile at a target vertex: corner-angle or straight, nothing else

`exists_corner_tile` showed one tile with well-behaved local angle. In fact *every* tile touching a
target vertex is well-behaved — the `0` and `2π` exclusions above did not use any particular
witness — which collapses `PinPlumbing.localAngle_cases`'s four-way split to two at a target
vertex. This is the qualitative shape `lem:census`'s corner counting runs on; it is not the
counting itself (that needs the tile shapes' shared angle *values*, which this file does not
touch), but every contributing tile is now known to be one of exactly two kinds. -/

/-- **At a target vertex, every covering tile presents a corner angle there, or a straight
angle — never `0` or `2π`.** -/
theorem tile_angle_dichotomy_at_vertex (D : Dissection N) (k : Fin 3) {i : Fin N}
    (hi : D.target.pts k ∈ (D.tile i).carrier) :
    (∃ j : Fin 3, D.target.pts k = (D.tile i).pts j ∧
        (D.tile i).localAngle (D.target.pts k)
          = cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))) ∨
    (D.tile i).localAngle (D.target.pts k) = Real.pi := by
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) (D.target.pts k) with
    hvertex | h2pi | hpi | h0
  · exact Or.inl hvertex
  · exact absurd h2pi (localAngle_ne_two_pi_of_not_mem_interior (D.target_vertex_not_interior_tile k i))
  · exact Or.inr hpi
  · exact absurd h0 (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hi)

/-! ## For a `CongruentDissection`, every angle at a vertex is `α`, `β`, `γ` or `π` — real, not
hypothesised

`TilePlacement.base_corner_counts`/`corner_multiplicities` take `hvals : ∀ i, localAngle ∈
{α,β,γ,π,0}` as a *hypothesis*. For a `CongruentDissection` it is a theorem: `tiles_congruent`
gives every tile congruent to the model, `CongruentAngles.congruent_corner_angles` turns "its own
corner angle at `j`" into "one of the model's three corner angles", and
`tile_angle_dichotomy_at_vertex` above rules out everything else. This is the real assembly the
census-adjacent rows (`lem:census`, `lem:rowp0`) were missing — not their full uniqueness content,
but the discrete hypothesis their arithmetic runs on, now derived rather than assumed. -/

open Erdos634.TilePlacement in
/-- **At a target vertex of a congruent dissection, every tile's local angle there is one of the
model's three corner angles, or `π`.** -/
theorem congruentDissection_localAngle_mem (D : CongruentDissection N) (α β γ : ℝ)
    (hα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
  classical
  by_cases hi : D.target.pts k ∈ (D.tile i).carrier
  · rcases D.toDissection.tile_angle_dichotomy_at_vertex k hi with ⟨j, hjp, hjeq⟩ | hpi
    · obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
      rw [hjeq, hm]
      have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hcases with rfl | rfl | rfl
      · left; rw [← hα]; congr 1
      · right; left; rw [← hβ]; congr 1
      · right; right; left; rw [← hγ]; congr 1
    · simp [hpi]
  · -- if `p` is not in the tile's carrier at all, `localAngle` is `0` by definition
    have h0 : (D.tile i).localAngle (D.target.pts k) = 0 := by
      classical
      rw [Erdos634.Geometry.Tri.localAngle]
      split
      · rename_i hv
        have hvmem : (D.target.pts k) ∈ Set.range (D.tile i).pts := ⟨hv.choose, hv.choose_spec.symm⟩
        exact absurd (subset_convexHull ℝ _ hvmem) hi
      · split
        · rename_i hall
          have hint : D.target.pts k ∈ interior (D.tile i).carrier :=
            (D.tile i).mem_interior_iff_coord_pos _ |>.mpr hall
          exact absurd (interior_subset hint) hi
        · split
          · rename_i hedge
            obtain ⟨kk, hkk1, hkk2⟩ := hedge
            have hmem : D.target.pts k ∈ (D.tile i).carrier := by
              rw [(D.tile i).carrier_eq_nonneg_coord]
              intro j
              rcases eq_or_ne j kk with rfl | hne
              · exact hkk1.ge
              · exact (hkk2 j hne).le
            exact absurd hmem hi
          · rfl
    simp [h0]

/-! ## The base corner fills uniquely, for a real `CongruentDissection`

`lem:census`'s own text asserts "the base corners fill uniquely as `{β}` and the apex as `{3α}`" —
this is exactly `TilePlacement.base_corner_counts`/`.apex_counts`, but those took the discrete
`hvals` hypothesis as given. `congruentDissection_localAngle_mem` derives it. Composing: the base
corner's fill is now a theorem about a real `CongruentDissection`, not a hypothesis about one. -/

open Erdos634.TilePlacement in
/-- **A base corner of a real congruent dissection fills uniquely as `{β}`.** -/
theorem congruentDissection_base_corner_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 :=
  base_corner_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr k
    (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner

open Erdos634.TilePlacement in
/-- **The apex of a real congruent dissection fills uniquely as `{3α}`.**  The other half of
`lem:census`'s quoted parenthetical, matching `congruentDissection_base_corner_counts` above. -/
theorem congruentDissection_apex_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 3 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  classical
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i
  have h := corner_multiplicities D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 k
    hvals
  rw [hcorner] at h
  exact apex_counts hγdef hrel hirr _ _ _ _ h

/-! ## `lem:endpoints`, fully assembled

The chain's first tile has `a` as one of its own vertices (`WallEndpoints.chain_endpoints`), so its
local angle there is a definite corner angle (`Tri.localAngle_vertex`), one of `{α,β,γ}`
(`CongruentAngles.congruent_corner_angles`). The base-corner count
(`congruentDissection_base_corner_counts`) says exactly one tile presents `β` at `a` and none
presents `α` or `γ`; since this tile is one of the (at most `{α,β,γ,π}`-valued, `0`/`2π` excluded)
contributors, elimination pins its angle to `β`. The mirror argument at the apex, with
`.congruentDissection_apex_counts`, pins the last tile's angle to `α`. -/

open Erdos634.TilePlacement Erdos634.WallEndpoints Erdos634.BaseChain Erdos634.Placement in
/-- **`lem:endpoints`, for a real `CongruentDissection`.**  The chain's first tile presents `β` at
the base corner `D.target.pts kbase`, and its last tile presents `α` at the apex
`D.target.pts kapex` — the paper's "the bottom angle of the first edge is `β`" and "the top angle
of the last edge is `α`". -/
theorem congruentDissection_endpoints (hN : 0 < N) (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (kbase kapex : Fin 3) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c)
    (hab : D.target.pts kbase ≠ D.target.pts kapex)
    (hdirab : dir (D.target.pts kbase) ≤ dir (D.target.pts kapex))
    (hbase : segment ℝ (D.target.pts kbase) (D.target.pts kapex) ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ (D.target.pts kbase) (D.target.pts kapex), g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c →
      y ∈ segment ℝ (D.target.pts kbase) (D.target.pts kapex))
    (hthird : ∀ p ∈ wallList D.toDissection g c, g ((D.tile p.1).pts (p.2 + 2)) < c)
    (hcornerbase : cornerAngle (D.target.pts (kbase + 1)) (D.target.pts kbase)
      (D.target.pts (kbase + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (kapex + 1)) (D.target.pts kapex)
      (D.target.pts (kapex + 2)) = 3 * α) :
    ∃ E : ℕ → Fin N × Fin 3, ∃ n : ℕ, n = (wallList D.toDissection g c).length ∧ 0 < n ∧
      (D.tile (E 0).1).localAngle (D.target.pts kbase) = β ∧
      (D.tile (E (n - 1)).1).localAngle (D.target.pts kapex) = α := by
  obtain ⟨E, n, hneq, hn0, hwest, heast⟩ :=
    chain_endpoints hN D.toDissection g c dir hker hwall (D.target.pts kbase)
      (D.target.pts kapex) hab hdirab hbase hline hface hthird
  refine ⟨E, n, hneq, hn0, ?_, ?_⟩
  · -- the first tile presents `a` as one of its own vertices
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, D.target.pts kbase = (D.tile (E 0).1).pts j := by
      unfold edgeWest at hwest
      split at hwest
      · exact ⟨(E 0).2, hwest.symm⟩
      · exact ⟨(E 0).2 + 1, hwest.symm⟩
    have hval : (D.tile (E 0).1).localAngle (D.target.pts kbase)
        = cornerAngle ((D.tile (E 0).1).pts (j + 1)) ((D.tile (E 0).1).pts j)
          ((D.tile (E 0).1).pts (j + 2)) := by
      rw [hj, Tri.localAngle_vertex]
    obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent (E 0).1).symm j
    rw [hval, hm]
    -- `m` is `0`, `1`, or `2`; the counts eliminate all but `β`
    have h := congruentDissection_base_corner_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' kbase hcornerbase
    have hcard : ({i | (D.tile i).localAngle (D.target.pts kbase)
        = cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2))} :
        Finset (Fin N)).card ≠ 0 := by
      refine Finset.card_ne_zero_of_mem (a := (E 0).1) ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hval, hm]
    fin_cases m
    · exact absurd (show cornerAngle (D.model.pts (0 + 1)) (D.model.pts 0)
        (D.model.pts (0 + 2)) = α from hα') (fun heq => hcard (heq ▸ h.1))
    · exact hβ'
    · exact absurd (show cornerAngle (D.model.pts (2 + 1)) (D.model.pts 2)
        (D.model.pts (2 + 2)) = γ from hγ') (fun heq => hcard (heq ▸ h.2.2.1))
  · -- the last tile presents `b` as one of its own vertices, mirror argument
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, D.target.pts kapex = (D.tile (E (n - 1)).1).pts j := by
      unfold edgeEast at heast
      split at heast
      · exact ⟨(E (n - 1)).2 + 1, heast.symm⟩
      · exact ⟨(E (n - 1)).2, heast.symm⟩
    have hval : (D.tile (E (n - 1)).1).localAngle (D.target.pts kapex)
        = cornerAngle ((D.tile (E (n - 1)).1).pts (j + 1)) ((D.tile (E (n - 1)).1).pts j)
          ((D.tile (E (n - 1)).1).pts (j + 2)) := by
      rw [hj, Tri.localAngle_vertex]
    obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent (E (n - 1)).1).symm j
    rw [hval, hm]
    have h := congruentDissection_apex_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' kapex hcornerapex
    have hcard : ({i | (D.tile i).localAngle (D.target.pts kapex)
        = cornerAngle (D.model.pts (m + 1)) (D.model.pts m) (D.model.pts (m + 2))} :
        Finset (Fin N)).card ≠ 0 := by
      refine Finset.card_ne_zero_of_mem (a := (E (n - 1)).1) ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hval, hm]
    fin_cases m
    · exact hα'
    · exact absurd (show cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1)
        (D.model.pts (1 + 2)) = β from hβ') (fun heq => hcard (heq ▸ h.2.1))
    · exact absurd (show cornerAngle (D.model.pts (2 + 1)) (D.model.pts 2)
        (D.model.pts (2 + 2)) = γ from hγ') (fun heq => hcard (heq ▸ h.2.2.1))

end Erdos634.Geometry.Dissection