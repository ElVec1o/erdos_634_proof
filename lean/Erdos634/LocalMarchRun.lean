import Erdos634.MarchRunObject
import Erdos634.MarchRun
import Erdos634.RouteOne

/-!
# The march's run as a *locally generated* object

`MarchRunObject.aRun` selects the `a`-edges of the wall by filtering `BaseChain.wallList`, a
**global** list.  Contiguity of that filtered sublist does not follow from
`BaseChain.base_chain_consecutive_meet` — `b`- and `c`-edges may interleave between the `a`-edges —
so `AEdgeReading.aRun_word_monotone` had to assume the junction incidence outright.  That
assumption is obligation (i) of `rem:marchobl`, and it is where the march work stopped.

This file replaces the object.  A march run here is generated **step by step**, from single-step
data: at each position the march has a tile, a corner of that tile sitting *at* the position, and
the next vertex of that tile one step `w` further along.  The position of step `n` is then
`V₀ + n • w` — proved, not posited — and the run's contiguity

> the far endpoint of entry `n` **is** the near endpoint of entry `n+1`

is a theorem (`contig`), by construction: both sides are `V₀ + (n+1) • w`.

What that buys, all for a real `Dissection` and with no contiguity hypothesis anywhere:

* `entry_injective` / `length_le_three_mul` — the entries are pairwise distinct tile edges, so a
  run has length at most `3N`.  This is `RouteOne.advance_count_le_run` at a real object.
* `length_le_runLength` — when the steps lie along a wall line, every entry is an `a`-edge of that
  wall, so the run injects into `MarchRunObject.aRun`: the local object refines the global one.
* `no_perpetual_march` — a step rule defined on a nonempty set closed under advancing is
  impossible.  The march terminates; `RouteOne.terminus_of_run_length`'s hypothesis is discharged.
* `tile_ne_succ` — consecutive entries are **distinct tiles**.  Three collinear vertices would make
  the shared tile degenerate (`Tri.det_cyclic`, `Tri.det_ne_zero`).  This is the fact the junction
  machinery needed and `aRun` could not supply.
* `word_monotone` and `run_exceptional_le_one` — with distinct tiles at each junction,
  `MarchRun.no_two_gammas` applies, and the orientation word's monotonicity is *derived* rather
  than assumed as in `MarchRunObject.run_exceptional_le_one`.

`Erdos634.LocalMarchRunWitness` exhibits a real `Run` of length four — four `a`-edges along the
base of the kernel-verified 44-tile dissection of the `(16,16,22)` triangle — so `contig`,
`tile_ne_succ`, `entry_injective` and `length_le_runLength` are all non-vacuous, and the
strict-shortest-side hypotheses of `orient_mono` are checked there at the first entry.

What is **not** here (2026-09-09):

* the production of a `StepDatum`, or of a `Run` with the angle hypotheses of `orient_mono`, from a
  hypothetical base-`β` tiling.  That is the attachment obligation, the same one
  `RouteOne.EscapeData` carries, and it is not touched.  `orient_mono`'s angle hypotheses
  (`γ = 2α + β`, `3α + 2β = π`, `α/π` irrational) are the base-`β` configuration's, and no witness
  for them is exhibited — witnessing them would be exhibiting a base-`β` tiling.
* any claim that the run is *maximal*, i.e. that the march cannot be extended.  `no_perpetual_march`
  says only that it cannot be extended forever.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LocalMarchRun

open Erdos634.Geometry

variable {N : ℕ}

/-! ## The positions -/

/-- The march's `n`-th position: `n` steps of `w` from the start. -/
def pos (V₀ w : Plane) (n : ℕ) : Plane := V₀ + (n : ℝ) • w

@[simp] theorem pos_zero (V₀ w : Plane) : pos V₀ w 0 = V₀ := by simp [pos]

theorem pos_succ (V₀ w : Plane) (n : ℕ) : pos V₀ w (n + 1) = pos V₀ w n + w := by
  simp [pos, add_smul, add_assoc]

theorem pos_add (V₀ w : Plane) (n k : ℕ) : pos V₀ w (n + k) = pos V₀ w n + (k : ℝ) • w := by
  simp only [pos, Nat.cast_add, add_smul]
  abel

/-- **Positions are distinct.**  A nonzero step never returns. -/
theorem pos_injective {V₀ w : Plane} (hw : w ≠ 0) : Function.Injective (pos V₀ w) := by
  intro m n h
  simp only [pos, add_right_inj] at h
  have : ((m : ℝ) - n) • w = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp this with h0 | h0
  · have : (m : ℝ) = n := by linarith [sub_eq_zero.mp h0]
    exact_mod_cast this
  · exact absurd h0 hw

/-! ## The run -/

/-- **A locally generated march run.**  `L` steps, each carrying a tile and a corner of it: the
corner sits at the step's position and the *next* corner of the same tile sits one step further
along.  Nothing global is filtered, and no contiguity is assumed — see `contig`. -/
structure Run (D : Dissection N) (V₀ w : Plane) (L : ℕ) where
  /-- the tile serving at step `n` -/
  tile : Fin L → Fin N
  /-- the corner of that tile sitting at the step's position -/
  corner : Fin L → Fin 3
  /-- the corner is at the position -/
  head : ∀ n : Fin L, (D.tile (tile n)).pts (corner n) = pos V₀ w (n : ℕ)
  /-- and the next corner is one step along -/
  foot : ∀ n : Fin L, (D.tile (tile n)).pts (corner n + 1) = pos V₀ w ((n : ℕ) + 1)

variable {D : Dissection N} {V₀ w : Plane} {L : ℕ}

/-- **Contiguity, by construction.**  The far endpoint of entry `n` is the near endpoint of entry
`n + 1`: both are the position `V₀ + (n+1) • w`.  This is the statement `MarchRunObject.aRun`
cannot make about its filtered sublist. -/
theorem contig (R : Run D V₀ w L) (m n : Fin L) (h : (n : ℕ) = (m : ℕ) + 1) :
    (D.tile (R.tile m)).pts (R.corner m + 1) = (D.tile (R.tile n)).pts (R.corner n) := by
  rw [R.foot m, R.head n, h]

/-- The edge of entry `n`, as a segment of the march line. -/
theorem edge_dist (R : Run D V₀ w L) (n : Fin L) :
    dist ((D.tile (R.tile n)).pts (R.corner n))
      ((D.tile (R.tile n)).pts (R.corner n + 1)) = ‖w‖ := by
  rw [R.head n, R.foot n]
  simp [pos, dist_eq_norm, add_smul, add_sub_add_left_eq_sub]

/-- **Entries are pairwise distinct.**  Two entries with the same tile *and* the same corner would
have the same near endpoint, hence the same position. -/
theorem entry_injective (R : Run D V₀ w L) (hw : w ≠ 0) :
    Function.Injective (fun n : Fin L => (R.tile n, R.corner n)) := by
  intro m n h
  simp only [Prod.mk.injEq] at h
  have hpos : pos V₀ w (m : ℕ) = pos V₀ w (n : ℕ) := by
    rw [← R.head m, ← R.head n, h.1, h.2]
  exact Fin.ext (pos_injective hw hpos)

/-- **A run is short.**  There are only `3N` tile edges. -/
theorem length_le_three_mul (R : Run D V₀ w L) (hw : w ≠ 0) : L ≤ 3 * N := by
  have := Fintype.card_le_of_injective _ (entry_injective R hw)
  simpa [Fintype.card_prod, Nat.mul_comm] using this

/-! ## The step rule, and the fact that no march is perpetual

A `StepDatum` is the *local* geometry: a set of positions on which the march is defined, and at
each of them a tile edge running from it one step along.  A run of any length is generated from it
(`ofStep`) — and therefore no such datum can have a nonempty domain, because runs are short. -/

/-- **The single-step rule.**  On `S`, every position carries a tile edge to the next position, and
the next position is again in `S`. -/
structure StepDatum (D : Dissection N) (w : Plane) where
  /-- the positions the march is defined at -/
  S : Set Plane
  /-- the serving tile -/
  tl : Plane → Fin N
  /-- the corner sitting at the position -/
  cn : Plane → Fin 3
  /-- it does sit there -/
  hhead : ∀ V ∈ S, (D.tile (tl V)).pts (cn V) = V
  /-- and its successor sits one step along -/
  hfoot : ∀ V ∈ S, (D.tile (tl V)).pts (cn V + 1) = V + w
  /-- the march can be continued -/
  hnext : ∀ V ∈ S, V + w ∈ S

/-- Every position reached from a point of the domain is again in the domain. -/
theorem StepDatum.pos_mem (A : StepDatum D w) {V₀ : Plane} (hV : V₀ ∈ A.S) :
    ∀ n : ℕ, pos V₀ w n ∈ A.S := by
  intro n
  induction n with
  | zero => simpa using hV
  | succ k ih => rw [pos_succ]; exact A.hnext _ ih

/-- **The run generated by the step rule.**  Contiguity is not a field: it is `contig`. -/
def ofStep (A : StepDatum D w) {V₀ : Plane} (hV : V₀ ∈ A.S) (L : ℕ) : Run D V₀ w L where
  tile n := A.tl (pos V₀ w (n : ℕ))
  corner n := A.cn (pos V₀ w (n : ℕ))
  head n := A.hhead _ (A.pos_mem hV _)
  foot n := by
    rw [A.hfoot _ (A.pos_mem hV _), pos_succ]

/-- **No perpetual march.**  A step rule with a nonempty domain would generate runs of every
length, but runs are bounded by the number of tile edges.  So the march terminates — the terminus
of `RouteOne.wall_descent`, for a real dissection rather than as a hypothesis. -/
theorem no_perpetual_march (A : StepDatum D w) (hw : w ≠ 0) (hne : A.S.Nonempty) : False := by
  obtain ⟨V₀, hV⟩ := hne
  have := length_le_three_mul (ofStep A hV (3 * N + 1)) hw
  omega

/-! ## The run refines `MarchRunObject.aRun`

If the march runs along the wall line `g = c` — that is, `g V₀ = c` and the step `w` is in the
kernel of `g`'s linear part — then every entry is a wall edge of length `‖w‖`, so the run injects
into the global object.  The local run is therefore not a competing notion: it is a contiguous
selection *inside* `aRun`. -/

/-- **Entries are wall edges.** -/
theorem wall_edge (R : Run D V₀ w L) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hg : g V₀ = c) (hw0 : g.linear w = 0) (n : Fin L) :
    Erdos634.WallEdges.WallEdge D g c (R.tile n, R.corner n) := by
  have hpos : ∀ m : ℕ, g (pos V₀ w m) = c := by
    intro m
    have h := g.map_vadd' V₀ ((m : ℝ) • w)
    simp only [vadd_eq_add, map_smul, hw0, smul_zero, zero_add] at h
    rw [pos, add_comm]
    exact h.trans hg
  refine ⟨?_, ?_⟩
  · rw [R.head n]; exact hpos _
  · rw [R.foot n]; exact hpos _

/-- **Entries belong to the global run.** -/
theorem mem_aRun (R : Run D V₀ w L) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hg : g V₀ = c) (hw0 : g.linear w = 0) (n : Fin L) :
    (R.tile n, R.corner n) ∈ Erdos634.MarchRunObject.aRun D g c ‖w‖ :=
  (Erdos634.MarchRunObject.mem_aRun D g c ‖w‖ _).mpr ⟨wall_edge R g c hg hw0 n, edge_dist R n⟩

/-- **The local run is at most as long as the global one.**  Injectivity of the entries plus
membership in the `Nodup` list `aRun` bounds the run's length by `runLength`. -/
theorem length_le_runLength (R : Run D V₀ w L) (hw : w ≠ 0) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hg : g V₀ = c) (hw0 : g.linear w = 0) :
    L ≤ Erdos634.MarchRunObject.runLength D g c ‖w‖ := by
  classical
  set A := Erdos634.MarchRunObject.aRun D g c ‖w‖ with hA
  have hcard : A.toFinset.card = A.length :=
    List.toFinset_card_of_nodup (Erdos634.MarchRunObject.aRun_nodup D g c ‖w‖)
  have hmap : ∀ n : Fin L, (R.tile n, R.corner n) ∈ A.toFinset := by
    intro n; simpa [hA] using mem_aRun R g c hg hw0 n
  have hinj : Set.InjOn (fun n : Fin L => (R.tile n, R.corner n))
      ((Finset.univ : Finset (Fin L)) : Set (Fin L)) := by
    intro m _ n _ h; exact entry_injective R hw h
  have := Finset.card_le_card_of_injOn (fun n : Fin L => (R.tile n, R.corner n))
    (fun n _ => hmap n) hinj
  rw [hcard] at this
  simpa [Erdos634.MarchRunObject.runLength, hA] using this

/-! ## Consecutive entries are distinct tiles

This is the fact the junction machinery needs and the filtered object cannot give.  If one tile
served two consecutive steps, it would carry vertices at three consecutive positions — three points
of one line — and its determinant would vanish. -/

/-- **Distinct tiles at consecutive steps.** -/
theorem tile_ne_succ (R : Run D V₀ w L) (m n : Fin L) (h : (n : ℕ) = (m : ℕ) + 1) :
    R.tile m ≠ R.tile n := by
  intro hEq
  set T := D.tile (R.tile m) with hT
  -- the corner of step `n` is the successor of the corner of step `m`
  have hshare : T.pts (R.corner m + 1) = T.pts (R.corner n) := by
    rw [hT, contig R m n h, hEq]
  have hcn : R.corner m + 1 = R.corner n := T.indep.injective hshare
  -- the three consecutive positions are vertices of the one tile
  have h0 : T.pts (R.corner m) = pos V₀ w (m : ℕ) := R.head m
  have h1 : T.pts (R.corner m + 1) = pos V₀ w ((m : ℕ) + 1) := R.foot m
  have h2 : T.pts (R.corner m + 2) = pos V₀ w ((m : ℕ) + 2) := by
    have : R.corner m + 2 = R.corner n + 1 := by rw [← hcn]; abel
    rw [this, hT, hEq]
    have := R.foot n
    rw [this, h]
  -- both edge directions at that corner are multiples of `w`
  have e1 : T.pts (R.corner m + 1) - T.pts (R.corner m) = w := by
    rw [h0, h1, pos_succ]; abel
  have e2 : T.pts (R.corner m + 2) - T.pts (R.corner m) = (2 : ℝ) • w := by
    rw [h0, h2, pos_add]
    push_cast
    abel
  have hcross : cross (T.pts (R.corner m + 1) - T.pts (R.corner m))
      (T.pts (R.corner m + 2) - T.pts (R.corner m)) = 0 := by
    rw [e1, e2, cross_smul_right, cross_self, mul_zero]
  rw [T.det_cyclic] at hcross
  exact T.det_ne_zero hcross

/-! ## The junction, and the orientation word

At the junction between steps `m` and `m+1` two **distinct** tiles meet, each at a vertex of its own
`a`-edge.  `MarchRun.no_two_gammas` then forbids both presenting `γ`, and that is exactly
`MarchMonotone`'s monotonicity hypothesis once the orientation is read as "presents `γ` at the far
end".

The reading needs one shape fact per tile: the run's edge is the tile's strictly shortest side and
the angles are `{α, β, γ}`.  With that, the two ends of the edge carry *different* angles from
`{β, γ}` (`MarchFlank.apex_angle_smallest`), so `β` at one end forces `γ` at the other. -/

/-- **`β` at one end forces `γ` at the other.**  The two corners flanking the shortest side carry
strictly different angles, both in `{β, γ}`. -/
theorem flank_gamma_of_beta (T : Tri) (j : Fin 3) {α β γ : ℝ}
    (h1 : Erdos634.TilePlacement.sideOpp T j < Erdos634.TilePlacement.sideOpp T (j + 1))
    (h2 : Erdos634.TilePlacement.sideOpp T (j + 1) < Erdos634.TilePlacement.sideOpp T (j + 2))
    (hapex : Erdos634.TilePlacement.angleAt T j = α)
    (hmem1 : Erdos634.TilePlacement.angleAt T (j + 1) = α ∨
      Erdos634.TilePlacement.angleAt T (j + 1) = β ∨
      Erdos634.TilePlacement.angleAt T (j + 1) = γ)
    (hmem2 : Erdos634.TilePlacement.angleAt T (j + 2) = α ∨
      Erdos634.TilePlacement.angleAt T (j + 2) = β ∨
      Erdos634.TilePlacement.angleAt T (j + 2) = γ)
    (hβ : T.localAngle (T.pts (j + 1)) = β) :
    T.localAngle (T.pts (j + 2)) = γ := by
  obtain ⟨-, g2⟩ := Erdos634.MarchFlank.presents_beta_or_gamma T j h1 h2 hapex hmem1 hmem2
  obtain ⟨o1, o2⟩ := Erdos634.MarchFlank.apex_angle_smallest T j h1 h2
  have hne : T.localAngle (T.pts (j + 1)) ≠ T.localAngle (T.pts (j + 2)) := by
    rw [Erdos634.Geometry.Tri.localAngle_vertex, Erdos634.Geometry.Tri.localAngle_vertex]
    simpa [Erdos634.TilePlacement.angleAt] using ne_of_lt o2
  rcases g2 with h | h
  · exact absurd (hβ.trans h.symm) hne
  · exact h

/-- The apex of entry `n`: the corner *opposite* the run's edge.  With the edge running
`corner n → corner n + 1`, the apex is `corner n + 2`, and then `apex + 1 = corner n`,
`apex + 2 = corner n + 1`. -/
def apex (R : Run D V₀ w L) (n : Fin L) : Fin 3 := R.corner n + 2

theorem apex_add_one (R : Run D V₀ w L) (n : Fin L) : apex R n + 1 = R.corner n := by
  have : ∀ c : Fin 3, c + 2 + 1 = c := by decide
  simpa [apex] using this (R.corner n)

theorem apex_add_two (R : Run D V₀ w L) (n : Fin L) : apex R n + 2 = R.corner n + 1 := by
  have : ∀ c : Fin 3, c + 2 + 2 = c + 1 := by decide
  simpa [apex] using this (R.corner n)

open Classical in
/-- **The orientation word of the run**, read off the tiles: entry `n` is `BG` — recorded as
`true` — exactly when its tile presents `γ` at the *far* end of its edge, i.e. at the junction with
entry `n+1`. -/
noncomputable def orient (R : Run D V₀ w L) (γ : ℝ) (n : ℕ) : Bool :=
  if h : n < L then
    decide ((D.tile (R.tile ⟨n, h⟩)).localAngle (pos V₀ w (n + 1)) = γ)
  else false

theorem orient_eq_true {R : Run D V₀ w L} {γ : ℝ} {n : ℕ} (h : n < L) :
    orient R γ n = true ↔ (D.tile (R.tile ⟨n, h⟩)).localAngle (pos V₀ w (n + 1)) = γ := by
  classical
  simp [orient, h]

/-- **The word is monotone: no `BG` is followed by a `GB`.**

The junction between entries `m` and `m+1` is the position `pos (m+1)`, a vertex of *both* tiles —
and they are **distinct** tiles (`tile_ne_succ`), which is what the filtered object
`MarchRunObject.aRun` could not supply.  `MarchRun.no_two_gammas` therefore forbids both presenting
`γ` there; the second tile presents `β` or `γ` at that end (`MarchFlank.presents_beta_or_gamma`),
hence `β`, hence `γ` at *its* far end (`flank_gamma_of_beta`).  That is the next letter being `BG`.

Every hypothesis is per-junction data about the configuration — the angle system, the junction
lying on the frontier away from the target's own vertices, and each tile carrying its `a`-edge as
its strictly shortest side.  None of them is contiguity: that is `contig`. -/
theorem orient_mono (R : Run D V₀ w L) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hfront : ∀ n : Fin L, pos V₀ w ((n : ℕ)) ∈ frontier D.target.carrier)
    (hnv : ∀ n : Fin L, pos V₀ w ((n : ℕ)) ∉ Set.range D.target.pts)
    (hvals : ∀ n : Fin L, ∀ i : Fin N,
      (D.tile i).localAngle (pos V₀ w ((n : ℕ))) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hshort1 : ∀ n : Fin L, Erdos634.TilePlacement.sideOpp (D.tile (R.tile n)) (apex R n) <
      Erdos634.TilePlacement.sideOpp (D.tile (R.tile n)) (apex R n + 1))
    (hshort2 : ∀ n : Fin L, Erdos634.TilePlacement.sideOpp (D.tile (R.tile n)) (apex R n + 1) <
      Erdos634.TilePlacement.sideOpp (D.tile (R.tile n)) (apex R n + 2))
    (hapexα : ∀ n : Fin L, Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n) = α)
    (hmem1 : ∀ n : Fin L, Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 1) = α ∨
      Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 1) = β ∨
      Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 1) = γ)
    (hmem2 : ∀ n : Fin L, Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 2) = α ∨
      Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 2) = β ∨
      Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 2) = γ) :
    ∀ i, i + 1 < L → orient R γ i = true → orient R γ (i + 1) = true := by
  classical
  intro i hi hio
  have hiL : i < L := by omega
  set m : Fin L := ⟨i, hiL⟩ with hm
  set n : Fin L := ⟨i + 1, hi⟩ with hn
  -- the junction is the position `i + 1`, a vertex of both tiles
  set J : Plane := pos V₀ w (i + 1) with hJ
  have hJm : (D.tile (R.tile m)).pts (R.corner m + 1) = J := R.foot m
  have hJn : (D.tile (R.tile n)).pts (R.corner n) = J := R.head n
  -- entry `m` presents `γ` at the junction
  have hγm : (D.tile (R.tile m)).localAngle J = γ := (orient_eq_true hiL).mp hio
  -- entry `n` presents `β` or `γ` there
  obtain ⟨gW, gE⟩ := Erdos634.MarchFlank.presents_beta_or_gamma (D.tile (R.tile n)) (apex R n)
    (hshort1 n) (hshort2 n) (hapexα n) (hmem1 n) (hmem2 n)
  rw [apex_add_one R n, hJn] at gW
  -- distinct tiles, so not both `γ`
  have hne : R.tile m ≠ R.tile n := tile_ne_succ R m n (by simp [hm, hn])
  have hβn : (D.tile (R.tile n)).localAngle J = β := by
    rcases gW with h | h
    · exact h
    · exact absurd (Erdos634.MarchRun.no_two_gammas D hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
        hγdef hrel hirr (by simpa [hJ, hn] using hfront n) (by simpa [hJ, hn] using hnv n)
        (by simpa [hJ, hn] using hvals n) (R.tile m) (R.tile n) hne hγm h) not_false
  -- hence `γ` at its far end, which is the next letter
  have hfar : (D.tile (R.tile n)).localAngle
      ((D.tile (R.tile n)).pts (apex R n + 2)) = γ := by
    refine flank_gamma_of_beta (D.tile (R.tile n)) (apex R n) (hshort1 n) (hshort2 n)
      (hapexα n) (hmem1 n) (hmem2 n) ?_
    rw [apex_add_one R n, hJn]; exact hβn
  rw [apex_add_two R n, R.foot n] at hfar
  exact (orient_eq_true hi).mpr (by simpa [hn] using hfar)

/-- **The exceptional junctions of a locally generated run number at most one.**

This is `MarchRunObject.run_exceptional_le_one` with its hypothesis discharged: there the
monotonicity of the orientation word was *assumed*, because the filtered global object had no
junction incidence.  Here it is `orient_mono`, proved from the run's own construction. -/
theorem run_exceptional_le_one (R : Run D V₀ w L) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hfront : ∀ n : Fin L, pos V₀ w ((n : ℕ)) ∈ frontier D.target.carrier)
    (hnv : ∀ n : Fin L, pos V₀ w ((n : ℕ)) ∉ Set.range D.target.pts)
    (hvals : ∀ n : Fin L, ∀ i : Fin N,
      (D.tile i).localAngle (pos V₀ w ((n : ℕ))) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hshort1 : ∀ n : Fin L, Erdos634.TilePlacement.sideOpp (D.tile (R.tile n)) (apex R n) <
      Erdos634.TilePlacement.sideOpp (D.tile (R.tile n)) (apex R n + 1))
    (hshort2 : ∀ n : Fin L, Erdos634.TilePlacement.sideOpp (D.tile (R.tile n)) (apex R n + 1) <
      Erdos634.TilePlacement.sideOpp (D.tile (R.tile n)) (apex R n + 2))
    (hapexα : ∀ n : Fin L, Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n) = α)
    (hmem1 : ∀ n : Fin L, Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 1) = α ∨
      Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 1) = β ∨
      Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 1) = γ)
    (hmem2 : ∀ n : Fin L, Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 2) = α ∨
      Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 2) = β ∨
      Erdos634.TilePlacement.angleAt (D.tile (R.tile n)) (apex R n + 2) = γ) :
    ((Finset.range L).filter
      (fun i => i + 1 < L ∧ orient R γ i ≠ orient R γ (i + 1))).card ≤ 1 :=
  Erdos634.MarchMonotone.transitions_card_le_one (L := L) (orient R γ)
    (orient_mono R hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr
      hfront hnv hvals hshort1 hshort2 hapexα hmem1 hmem2)

end Erdos634.LocalMarchRun
