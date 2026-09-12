import Erdos634.MarchKillsFan
import Erdos634.TranslateDissection
import Erdos634.PinPlumbing
import Erdos634.MarchRunStep
import Erdos634.MarchFlank

/-!
# The layer-1 march as an induction: the configuration, its translation law, and the `a|a` junction step

Written 2026-09-12, after room `data` (`private/ROOM/data/VERDICT.md` §5, `report_experimental.md`
§3, `report_targetA.md`).  The corpus had every *local* fact of the layer-1 march at `e = 1`
(tile `(f, f²−1, f²)`, target `baseBetaTarget 1 f`, base `L = 3f² − 1`) in coordinates
(`MarchCoords`, `MarchKills`, `MarchKillsFan`) but not the *composition*: an induction along the
base saying "if the base layer is the march up to letter `k`, it is the march up to letter
`k + 1`".  This file supplies the `a|a` junction step of that induction as a theorem about a
`CongruentDissection`, the induction that consumes it, and the translation law that says every
block presents the same problem.  Nothing here is a statement about the search.

## Ledger (checked 2026-09-12; nothing below is re-proved)

* The march *count* as an induction over runway length / chirality strings:
  `MarchStep.march_dies`, `MarchFrontier.frontier_induction`, `.noTwoZeros` — abstract strong
  induction schemas over `ℕ → Prop`, no geometry.  `MarchRecurrence.march_counts` is content-free
  (its own audit note, 2026-09-10).
* The run as an object: `MarchRunObject.aRun` selects the `a`-edges on a line; `MarchRun` /
  `MarchMonotone` give "all but one junction is a march junction" for an abstract orientation word;
  `RouteOneStepBridge.Run'` marches a `StepDatum'` along a wall — none produces a coordinate
  configuration, and `GOAL_PRIMES.md:944–1023` records that its `habove` gap is `rem:straddler`.
* The vertex half of the step: `VertexFigureReal.gamma_boundary_figure_real`,
  `JunctionWedge.march_junction_real`, `WedgeExtremal.corner_on_wedge_sides` — the last two take
  the filler's edge directions *in the wedge* (`hφm`, `hψm`) as hypotheses that nothing in the
  corpus discharged (`CornerAnglePerm` only passes them through).
* The coordinate tiles and their kills: `MarchKills.aTileBG/GB`, `flushFiller`, `offsetFiller`,
  `march_confined`, `far_corner_kill` (conditional on **R**, with an exact `Tri` equality),
  `no_bg_then_gb` (exact `Tri` equalities); `MarchKillsFan.c_slot_kill` (conditional on **R_c**),
  `localAngle_of_oppSide`, `base_point_mem_frontier`; the a-letter's apex from distances,
  `MarchRunStep.bg_abscissa`/`gb_abscissa`.
* `rem:marchobl` in Lean terms (`PAPER_MAP.md` rows M-i, M-ii, M-iii): (i) the march's steps land
  on `{α,β,γ}` vertices — PROVED for the junctions of an abstract run, blocked at "the run of a
  hypothetical tiling"; (ii) the two chiralities advance by one and two positions, (iii) both
  reduce to the same problem — HEURISTIC (measured), "blocked at the level of statement".

## What is proved here

**§1–2, the configuration and THE TRANSLATION LEMMA.**  `block t f b` is the set of three
coordinate triangles `{aTileBG t, aTileBG (t+f), filler b t}` (`filler true = flushFiller`,
`filler false = offsetFiller`); `marchConfig t f k s = ⋃_{j<k} block (t + j f) (s j)`.
`block_translate`: `block (t + d) f b = translateTri (d, 0) '' block t f b`, an identity of sets of
`Tri` (hence of point sets, `translateTri_carrier`); `marchConfig_translate`, and
`marchConfig_add`: the `(k+m)`-block configuration is the first `k` blocks together with the
`m`-block configuration of the shifted word `s(· + k)` translated by `(k f, 0)`.  Confinement:
`marchConfig_confined`, every vertex has height in `[0, overshootH f]`; containment,
`marchConfig_subset_target`, for `f/(f²−1) ≤ t` and `t + k f + 2 dBG ≤ L`.  (The lower bound on
`t` is sharp: at `t = 0` the offset filler's overshoot vertex leaves the target, §13.)

**§3–10, THE JUNCTION STEP, proved.**  `junction_step`: for a `CongruentDissection D` of
`baseBetaTarget 1 f` (`f ≥ 2`, model sides `f, f²−1, f²`, angles `0 < α`, `0 < β`, `α ≠ β`, `γ = 2α + β`,
`3α + 2β = π`, `α/π ∉ ℚ` — the bundle `c_slot_kill` uses, inhabited by the model angles), if some
tile of `D` has the vertex set of `aTileBG t f` (**M**) and some tile lays the next letter as an
`a` — has an edge `[t + f, t + 2f]` on the base (**the base word**) — with `0 < t`,
`t + 2f ≤ L`, then

1. the next tile has the vertex set of `aTileBG (t + f) f` — `GB` dies (`gb_after_bg_dies`,
   the vertex-set form of `no_bg_then_gb`: the `GB` apex edge `(dGB, h)` is
   `(1 − 1/f²)·(−f, 0) + 1·(dBG − f, h)`, strictly inside the `BG` corner);
2. exactly one further tile covers the junction `(t + f, 0)` (`junction_alpha_tile`, from the
   boundary trichotomy), it presents `α` there, and **its vertex set is that of `flushFiller t f`
   or of `offsetFiller t f`** — the two chiralities and no third placement.

The step that was open — the filler's edges lie *in* the uncovered wedge — is `edge_in_wedge`:
an edge strictly inside either `a`-tile's corner, or on the base line, can be pushed by `ε` toward
the other edge into a positive combination of both tiles' edge directions, killed by
`MarchOverlap.Dissection.wedge_disjoint_combo` (`combo_dies_pts`).  Extremality is then the
Gram-form lemma `gram_extremal` (two vectors in a closed wedge with the wedge's own Gram data are
the wedge's rays or their reflection in the bisector; proof: Gram determinant `= ±1` and one
polynomial certificate per sign) applied in coordinates (`wedge_extremal_coords`).  Vertex sets,
not `Tri` equalities, throughout: a tile of `D` carries no preferred vertex order.

**§11–13, the induction and the ends.**  `march_step`: `MarchUpTo D f t k → MarchUpTo D f t (k+1)`
when letter `k + 1` is an `a`.  `run_rigid`: if letters `[t + j f, t + (j+1) f]`, `j < n`, are
laid as `a`-edges and the first is laid `BG` (**the base case `M₀`**), every letter of the run is
laid `BG` and every interior junction carries a flush or offset filler.  `far_corner_kill'`: the
march's `BG` tile on `[L − 3f, L − 2f]` plus an `a` on `[L − 2f, L − f]` is a contradiction, with
the `GB` half *derived* (vertex-set form of `MarchKills.far_corner_kill`).  `first_letter_bg`: a
first letter `a` is laid `BG` — the base case for every word beginning with `a`.
`offset_at_corner_junction_outside` / `corner_junction_flush`: at the corner junction `(f, 0)`
only the flush chirality survives (the offset's overshoot vertex is outside the target by
`f/(f²−1)` horizontally) — a small new kill the data cannot see (it never places the corner).

**§14, non-vacuity.**  `block_subset_target`: both chiralities' blocks lie in the target;
`config_f3`: all coordinates at `f = 3`, `t = 1`, blocks `0` and `1` (block `1` = block `0` +
`(3, 0)`), the overshoot vertex at `9h/8 = overshootH 3`; `junction_step_hyps_f3`.

## The composite, and what is NOT proved (the residue of `rem:marchobl`, exactly)

The family theorem does **not** follow.  What is proved is: **the base layer is rigid along every
`a`-run** — `M_k → M_{k+1}` at every `a|a` junction, conditional on the run's first tile being
`BG` (free at the corner).  What remains, each a *named position along the base*:

* **the mixed junctions** `a|b`, `b|a`, `a|c`, `c|a` — (G2)/(G3) of `report_experimental.md`, the
  "slot tiles are transparent" claim.  The run induction stops at the first non-`a` letter; the
  `c`-slot kills (`MarchKillsFan`) start from **R_c**, which the run induction reaches only if the
  `c|a` junction is analysed.  Not touched here.
* **the second-offset kill (K1) at the edge level**: `run_rigid` admits *every* chirality word,
  including two consecutive offsets; the data's `noTwoZeros` constraint is the stub of length
  `c − b = 1` (`MarchStep.offset_terminal_dies` is its arithmetic) whose edge-chain realisation is
  not built.  It is not needed for the induction, only for the count.
* **the base case for words beginning with `c`**: the first `a` after the corner `c`-tile.
* **the far corner** is reached by the run induction only through the mixed junctions.

So `rem:marchobl` stays OPEN; its `a|a` step — obligation (i) for the base run, and (ii)/(iii) in
their coordinate form "flush or offset, translated" — is VERIFIED here.  The e=1 residue is now
exactly the four mixed junction types (plus K1 at edge level and the `c`-first base case), not the
`a|a` junction.  No prime falls; no `/goal` outcome moves.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.MarchInduction

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchCoords Erdos634.BaseBetaTargetCoord
  Erdos634.MarchKills Erdos634.MarchKillsFan Erdos634.TilePlacement Erdos634.DissectionMap
  Erdos634.TranslateDissection

/-! ## 0. Small API on points and triangles -/

theorem plane_ext {u w : Plane} (h0 : u 0 = w 0) (h1 : u 1 = w 1) : u = w := by
  ext i; fin_cases i <;> simpa

theorem mkPt_add (a b c d : ℝ) : mkPt a b + mkPt c d = mkPt (a + c) (b + d) := by
  apply plane_ext <;> simp

theorem mkPt_sub (a b c d : ℝ) : mkPt a b - mkPt c d = mkPt (a - c) (b - d) := by
  apply plane_ext <;> simp

theorem mkPt_inj {a b c d : ℝ} (h : mkPt a b = mkPt c d) : a = c ∧ b = d :=
  ⟨by have := congrArg (fun p : Plane => p 0) h; simpa using this,
   by have := congrArg (fun p : Plane => p 1) h; simpa using this⟩

theorem Tri.ext' {T U : Tri} (h : T.pts = U.pts) : T = U := by
  cases T; cases U; simp only at h; subst h; rfl

theorem range_pts_eq (T : Tri) : Set.range T.pts = {T.pts 0, T.pts 1, T.pts 2} := by
  ext x; constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · intro hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem range_pts_eq_cyclic (T : Tri) (k : Fin 3) :
    Set.range T.pts = {T.pts k, T.pts (k + 1), T.pts (k + 2)} := by
  rw [range_pts_eq]; fin_cases k <;> ext x <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, zero_add, Fin.reduceAdd] <;> tauto

theorem pts_ne_succ (T : Tri) (k : Fin 3) : T.pts k ≠ T.pts (k + 1) := by
  intro h; have h' := T.indep.injective h
  have : ∀ k : Fin 3, k ≠ k + 1 := by decide
  exact this k h'

theorem pts_ne_succ_succ (T : Tri) (k : Fin 3) : T.pts k ≠ T.pts (k + 2) := by
  intro h; have h' := T.indep.injective h
  have : ∀ k : Fin 3, k ≠ k + 2 := by decide
  exact this k h'

theorem pts_succ_ne_succ_succ (T : Tri) (k : Fin 3) : T.pts (k + 1) ≠ T.pts (k + 2) := by
  intro h; have h' := T.indep.injective h
  have : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
  exact this k h'

/-- **Reading a tile's vertex data off its vertex set.**  If the vertex set is `{P, Q, R}` with
`P, Q, R` distinct and `pts k = P`, then the two other vertices in cyclic order from `k` are
`Q, R` or `R, Q`. -/
theorem vertex_data_of_range {T : Tri} {P Q R : Plane}
    (hr : Set.range T.pts = {P, Q, R}) {k : Fin 3} (hk : T.pts k = P) :
    (T.pts (k + 1) = Q ∧ T.pts (k + 2) = R) ∨ (T.pts (k + 1) = R ∧ T.pts (k + 2) = Q) := by
  have h1 : T.pts (k + 1) ∈ ({P, Q, R} : Set Plane) := hr ▸ ⟨_, rfl⟩
  have h2 : T.pts (k + 2) ∈ ({P, Q, R} : Set Plane) := hr ▸ ⟨_, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  have n1 := pts_ne_succ T k
  have n2 := pts_ne_succ_succ T k
  have n12 := pts_succ_ne_succ_succ T k
  rw [hk] at n1 n2
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2
  all_goals first
    | exact absurd h1.symm n1
    | exact absurd h2.symm n2
    | exact absurd (h1.trans h2.symm) n12
    | exact Or.inl ⟨h1, h2⟩
    | exact Or.inr ⟨h1, h2⟩

/-- A vertex of a tile of `D` lies in the target. -/
theorem pts_mem_target {N : ℕ} (D : Dissection N) (i : Fin N) (k : Fin 3) :
    (D.tile i).pts k ∈ D.target.carrier :=
  Erdos634.Geometry.tile_subset_target D i (subset_convexHull ℝ _ ⟨k, rfl⟩)

/-! ## 1. The march configuration and its translation law -/

/-- The filler at the junction `t + f`, by chirality: `true` = flush, `false` = offset. -/
noncomputable def filler (b : Bool) (t f : ℝ) (hf : 1 < f) : Tri :=
  if b then flushFiller t f hf else offsetFiller t f hf

/-- **Block `t`**: the two `BG` `a`-tiles on `[t, t+f]`, `[t+f, t+2f]` and the filler at their
junction `t + f`, in the given chirality. -/
noncomputable def block (t f : ℝ) (hf : 1 < f) (b : Bool) : Set Tri :=
  {aTileBG t f hf, aTileBG (t + f) f hf, filler b t f hf}

/-- **The march configuration after `k` blocks** with chirality word `s`: block `j` sits at
`t + j·f` with chirality `s j`, `j < k`.  Its `a`-tiles are those on letters `0 … k` and its
fillers those at junctions `1 … k`. -/
def marchConfig (t f : ℝ) (hf : 1 < f) (k : ℕ) (s : ℕ → Bool) : Set Tri :=
  {T | ∃ j, j < k ∧ T ∈ block (t + j * f) f hf (s j)}

/-- The chirality words the data admits: no two consecutive offsets (`MarchFrontier.noTwoZeros`). -/
def NoTwoOffsets (s : ℕ → Bool) (k : ℕ) : Prop := ∀ j, j + 1 < k → s j = true ∨ s (j + 1) = true

theorem marchConfig_zero (t f : ℝ) (hf : 1 < f) (s : ℕ → Bool) : marchConfig t f hf 0 s = ∅ := by
  ext T; simp [marchConfig]

theorem marchConfig_succ (t f : ℝ) (hf : 1 < f) (k : ℕ) (s : ℕ → Bool) :
    marchConfig t f hf (k + 1) s = marchConfig t f hf k s ∪ block (t + k * f) f hf (s k) := by
  ext T
  simp only [marchConfig, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨j, hj, hT⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact Or.inl ⟨j, hj, hT⟩
    · exact Or.inr hT
  · rintro (⟨j, hj, hT⟩ | hT)
    · exact ⟨j, by omega, hT⟩
    · exact ⟨k, by omega, hT⟩

/-- Translation of a tile by a vector, as `DissectionMap.mapTri` along `transEquiv`. -/
noncomputable def translateTri (v : Plane) (T : Tri) : Tri :=
  mapTri (transEquiv v).toAffineEquiv T

theorem translateTri_pts (v : Plane) (T : Tri) (i : Fin 3) :
    (translateTri v T).pts i = v + T.pts i := by
  show (transEquiv v).toAffineEquiv (T.pts i) = v + T.pts i
  simp [transEquiv]

theorem translateTri_carrier (v : Plane) (T : Tri) :
    (translateTri v T).carrier = (fun p => v + p) '' T.carrier := by
  unfold translateTri; rw [mapTri_carrier]; rfl

theorem translateTri_mkTri (v₀ v₁ x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (h : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0)
    (h' : det3 (v₀ + x₀) (v₁ + y₀) (v₀ + x₁) (v₁ + y₁) (v₀ + x₂) (v₁ + y₂) ≠ 0) :
    translateTri (mkPt v₀ v₁) (mkTri x₀ y₀ x₁ y₁ x₂ y₂ h)
      = mkTri (v₀ + x₀) (v₁ + y₀) (v₀ + x₁) (v₁ + y₁) (v₀ + x₂) (v₁ + y₂) h' := by
  apply Tri.ext'
  funext i
  rw [translateTri_pts]
  fin_cases i <;> simp [mkTri_pts, mkPt_add]

/-- **The `a`-tiles translate along the run.** -/
theorem aTileBG_translate (t f d : ℝ) (hf : 1 < f) :
    translateTri (mkPt d 0) (aTileBG t f hf) = aTileBG (t + d) f hf := by
  unfold aTileBG
  rw [translateTri_mkTri _ _ _ _ _ _ _ _ _ (by
    have := det_aTileBG (t + d) f hf
    convert this using 2 <;> ring)]
  congr 1 <;> ring

theorem aTileGB_translate (t f d : ℝ) (hf : 1 < f) :
    translateTri (mkPt d 0) (aTileGB t f hf) = aTileGB (t + d) f hf := by
  unfold aTileGB
  rw [translateTri_mkTri _ _ _ _ _ _ _ _ _ (by
    have := det_aTileGB (t + d) f hf
    convert this using 2 <;> ring)]
  congr 1 <;> ring

theorem flushFiller_translate (t f d : ℝ) (hf : 1 < f) :
    translateTri (mkPt d 0) (flushFiller t f hf) = flushFiller (t + d) f hf := by
  unfold flushFiller
  rw [translateTri_mkTri _ _ _ _ _ _ _ _ _ (by
    have := det_flushFiller (t + d) f hf
    convert this using 2 <;> ring)]
  congr 1 <;> ring

theorem offsetFiller_translate (t f d : ℝ) (hf : 1 < f) :
    translateTri (mkPt d 0) (offsetFiller t f hf) = offsetFiller (t + d) f hf := by
  unfold offsetFiller
  rw [translateTri_mkTri _ _ _ _ _ _ _ _ _ (by
    have := det_offsetFiller (t + d) f hf
    convert this using 2 <;> ring)]
  congr 1 <;> ring

theorem filler_translate (b : Bool) (t f d : ℝ) (hf : 1 < f) :
    translateTri (mkPt d 0) (filler b t f hf) = filler b (t + d) f hf := by
  cases b <;> simp [filler, flushFiller_translate, offsetFiller_translate]

/-- **THE TRANSLATION LEMMA, one block.**  The block at `t + d` is the block at `t` translated
by `(d, 0)`, as an identity of sets of triangles (hence of point sets, `translateTri_carrier`). -/
theorem block_translate (t f d : ℝ) (hf : 1 < f) (b : Bool) :
    block (t + d) f hf b = translateTri (mkPt d 0) '' block t f hf b := by
  unfold block
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, aTileBG_translate,
    aTileBG_translate, filler_translate, show t + f + d = t + d + f by ring]

/-- **The translation lemma, whole configuration.**  The configuration started at `t + d` is the
configuration started at `t` translated by `(d, 0)`. -/
theorem marchConfig_translate (t f d : ℝ) (hf : 1 < f) (k : ℕ) (s : ℕ → Bool) :
    marchConfig (t + d) f hf k s = translateTri (mkPt d 0) '' marchConfig t f hf k s := by
  ext T
  simp only [marchConfig, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨j, hj, hT⟩
    rw [show t + d + j * f = t + j * f + d by ring, block_translate] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    exact ⟨U, ⟨j, hj, hU⟩, rfl⟩
  · rintro ⟨U, ⟨j, hj, hU⟩, rfl⟩
    refine ⟨j, hj, ?_⟩
    rw [show t + d + j * f = t + j * f + d by ring, block_translate]
    exact ⟨U, hU, rfl⟩

/-- **The configuration at block `k` with word `s` is the configuration at block `0` with the
shifted word `s(· + k)`, translated by `(k·f, 0)`.**  Stated as the decomposition of the
`(k + m)`-block configuration into its first `k` blocks and the translate of an `m`-block
configuration with the shifted word. -/
theorem marchConfig_add (t f : ℝ) (hf : 1 < f) (k m : ℕ) (s : ℕ → Bool) :
    marchConfig t f hf (k + m) s
      = marchConfig t f hf k s
        ∪ translateTri (mkPt (k * f) 0) '' marchConfig t f hf m (fun j => s (j + k)) := by
  rw [← marchConfig_translate]
  ext T
  simp only [marchConfig, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨j, hj, hT⟩
    by_cases hjk : j < k
    · exact Or.inl ⟨j, hjk, hT⟩
    · refine Or.inr ⟨j - k, by omega, ?_⟩
      have : (t + k * f + ((j - k : ℕ) : ℝ) * f) = t + j * f := by
        rw [Nat.cast_sub (by omega)]; ring
      rw [this, show j - k + k = j by omega]; exact hT
  · rintro (⟨j, hj, hT⟩ | ⟨j, hj, hT⟩)
    · exact ⟨j, by omega, hT⟩
    · refine ⟨j + k, by omega, ?_⟩
      have : t + ((j + k : ℕ) : ℝ) * f = t + k * f + j * f := by push_cast; ring
      rw [this]; exact hT

/-- The block at position `k` of the configuration is block `0` (with chirality `s k`) translated
by `(k·f, 0)`. -/
theorem block_k_eq_translate (t f : ℝ) (hf : 1 < f) (k : ℕ) (s : ℕ → Bool) :
    block (t + k * f) f hf (s k) = translateTri (mkPt (k * f) 0) '' block t f hf (s k) :=
  block_translate t f _ hf _

theorem block_subset_marchConfig (t f : ℝ) (hf : 1 < f) (k : ℕ) (s : ℕ → Bool) :
    block (t + k * f) f hf (s k) ⊆ marchConfig t f hf (k + 1) s := by
  intro T hT; exact ⟨k, by omega, hT⟩

/-! ## 2. Confinement and containment -/

/-- Every vertex of every tile of the configuration has height in `[0, overshootH f]`. -/
theorem marchConfig_confined {f : ℝ} (hf : 2 ≤ f) (t : ℝ) (k : ℕ) (s : ℕ → Bool) :
    ∀ T ∈ marchConfig t f (by linarith) k s, ∀ i, 0 ≤ (T.pts i) 1 ∧ (T.pts i) 1 ≤ overshootH f := by
  have hf1 : 1 < f := by linarith
  have hpos := apexH_pos hf1
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  rintro T ⟨j, -, hT⟩ i
  have hc := march_confined hf (t + j * f) 0
  simp only [block, filler, Set.mem_insert_iff, Set.mem_singleton_iff] at hT
  rcases hT with rfl | rfl | rfl
  · refine ⟨?_, hc.1 i⟩
    fin_cases i <;> simp [aTileBG, mkTri_pts, hpos.le]
  · refine ⟨?_, (march_confined hf (t + j * f + f) 0).1 i⟩
    fin_cases i <;> simp [aTileBG, mkTri_pts, hpos.le]
  · cases s j
    · refine ⟨?_, hc.2.2.2.1 i⟩
      fin_cases i <;> simp [offsetFiller, mkTri_pts] <;> positivity
    · refine ⟨?_, hc.2.2.1 i⟩
      fin_cases i <;> simp [flushFiller, mkTri_pts, hpos.le]

/-- A point of the target has height `≥ 0`. -/
theorem target_height_nonneg {e f : ℝ} (he : 0 < e) (hef : e < f) :
    ∀ q : Plane, q ∈ (baseBetaTarget e f he hef).carrier → 0 ≤ q 1 := by
  have hconv : Convex ℝ {q : Plane | 0 ≤ q 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have : (a • x + b • y) 1 = a * x 1 + b * y 1 := by simp
    rw [this]; positivity
  have hsub : (baseBetaTarget e f he hef).carrier ⊆ {q : Plane | 0 ≤ q 1} := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨k, rfl⟩
    fin_cases k <;> simp [baseBetaTarget, mkTri_pts, mkPt_one, (height_pos he hef).le]
  exact fun q hq => hsub hq

/-- **Membership in the `e = 1` target, at a point of height `μ·h`**: the left and right side
tests reduce to `μ·dBG ≤ a` and `a + μ·dBG ≤ L`. -/
theorem mem_target_at_level {f : ℝ} (hf : 1 < f) {a μ : ℝ} (hμ : 0 ≤ μ)
    (hl : μ * dBG f ≤ a) (hr : a + μ * dBG f ≤ baseLen 1 f) :
    mkPt a (μ * apexH f) ∈ (baseBetaTarget 1 f one_pos hf).carrier := by
  have hH := height_pos one_pos hf
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hL := baseLen_pos one_pos hf
  have hL' := baseLen_one f
  refine mem_carrier_of_dets (target_det_pos one_pos hf) ?_ ?_ ?_
  · have e : det3 a (μ * apexH f) (baseLen 1 f) 0 (baseLen 1 f / 2) (height 1 f)
        = height 1 f * (baseLen 1 f - a - μ * dBG f) := by
      unfold det3 apexH dBG; rw [hL']; field_simp; ring
    rw [e]; exact mul_nonneg hH.le (by linarith)
  · have e : det3 0 0 a (μ * apexH f) (baseLen 1 f / 2) (height 1 f)
        = height 1 f * (a - μ * dBG f) := by
      unfold det3 apexH dBG; rw [hL']; field_simp; ring
    rw [e]; exact mul_nonneg hH.le (by linarith)
  · have e : det3 0 0 (baseLen 1 f) 0 a (μ * apexH f) = baseLen 1 f * (μ * apexH f) := by
      unfold det3; ring
    rw [e]; exact mul_nonneg hL.le (mul_nonneg hμ (apexH_pos hf).le)

/-- A base point `(a, 0)` with `0 ≤ a ≤ L` is in the target. -/
theorem base_mem_target {f : ℝ} (hf : 1 < f) {a : ℝ} (h0 : 0 ≤ a) (hL : a ≤ baseLen 1 f) :
    mkPt a 0 ∈ (baseBetaTarget 1 f one_pos hf).carrier := by
  have := mem_target_at_level hf (a := a) (μ := 0) le_rfl (by simpa) (by simpa)
  simpa using this

theorem dBG_pos {f : ℝ} (hf : 1 < f) : 0 < dBG f := (gb_then_bg_separates f hf).2

theorem dBG_gt_f {f : ℝ} (hf : 1 < f) : f < dBG f := by
  have := (bg_then_gb_straddles f hf).1; linarith

/-- **The configuration lies in the target** for `f/(f²−1) ≤ t` and `t + k·f + 2·dBG ≤ L`.  The
lower bound on `t` is exactly what the offset filler's overshoot vertex at the first junction
needs against the left side (see `offset_at_corner_junction_outside` for what happens at
`t = 0`); the upper bound is the last apex against the right side. -/
theorem marchConfig_subset_target {f : ℝ} (hf : 2 ≤ f) {t : ℝ} (ht : f / (f ^ 2 - 1) ≤ t)
    (k : ℕ) (s : ℕ → Bool) (hk : t + k * f + 2 * dBG f ≤ baseLen 1 f) :
    ∀ T ∈ marchConfig t f (by linarith) k s,
      T.carrier ⊆ (baseBetaTarget 1 f one_pos (by linarith)).carrier := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hq := dBG_pos hf1
  have hqf := dBG_gt_f hf1
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hbc : (f ^ 2 - 1) / f ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hbc0 : 0 ≤ (f ^ 2 - 1) / f ^ 2 := by positivity
  have hcb0 : 0 ≤ f ^ 2 / (f ^ 2 - 1) := by positivity
  -- the overshoot's right-side margin: `(c/b)(2 dBG − f) ≤ 2 dBG`
  have hover : f ^ 2 / (f ^ 2 - 1) * (2 * dBG f - f) ≤ 2 * dBG f := by
    have h2 : 2 * dBG f = (3 * f ^ 2 - 1) / f := by unfold dBG; field_simp
    rw [h2, div_mul_eq_mul_div, div_le_div_iff₀ hb (by positivity)]
    have : (0:ℝ) ≤ f ^ 4 - 3 * f ^ 2 + 1 := by nlinarith [sq_nonneg (f ^ 2 - 2), sq_nonneg f]
    field_simp
    nlinarith [pow_pos hf0 2, pow_pos hf0 3, pow_pos hf0 4]
  -- the overshoot's left-side margin: `t ≥ f/b`
  have hleft : f ^ 2 / (f ^ 2 - 1) * f ≤ t + f := by
    have : f ^ 2 / (f ^ 2 - 1) * f = f + f / (f ^ 2 - 1) := by field_simp; ring
    rw [this]; linarith
  rintro T ⟨j, hj, hT⟩
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ j := by positivity
  refine convexHull_min ?_ (baseBetaTarget 1 f one_pos hf1).convex
  rintro _ ⟨i, rfl⟩
  simp only [block, filler, Set.mem_insert_iff, Set.mem_singleton_iff] at hT
  have base : ∀ a, 0 ≤ a → a ≤ baseLen 1 f → mkPt a 0 ∈ (baseBetaTarget 1 f one_pos hf1).carrier :=
    fun a h0 hL => base_mem_target hf1 h0 hL
  have apex : ∀ a, 0 ≤ a → a + 2 * dBG f ≤ baseLen 1 f →
      mkPt (a + dBG f) (apexH f) ∈ (baseBetaTarget 1 f one_pos hf1).carrier := by
    intro a h0 hL
    have := mem_target_at_level hf1 (a := a + dBG f) (μ := 1) zero_le_one (by linarith) (by linarith)
    simpa using this
  rcases hT with rfl | rfl | rfl
  · fin_cases i <;> simp only [aTileBG, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact base _ (by positivity) (by nlinarith)
    · exact base _ (by positivity) (by nlinarith)
    · exact apex _ (by positivity) (by nlinarith)
  · fin_cases i <;> simp only [aTileBG, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    · exact base _ (by positivity) (by nlinarith)
    · exact base _ (by positivity) (by nlinarith)
    · exact apex _ (by positivity) (by nlinarith)
  · cases s j
    · fin_cases i <;> simp only [offsetFiller, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      · exact base _ (by positivity) (by nlinarith)
      · refine mem_target_at_level hf1 hbc0 ?_ ?_
        · nlinarith
        · nlinarith
      · refine mem_target_at_level hf1 hcb0 ?_ ?_
        · nlinarith
        · nlinarith
    · fin_cases i <;> simp only [flushFiller, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      · exact base _ (by positivity) (by nlinarith)
      · have := apex (t + j * f + f) (by positivity) (by nlinarith)
        convert this using 2
      · exact apex _ (by positivity) (by nlinarith)

/-! ## 3. The open-cone kill: an edge of one tile pointing strictly into another tile's corner -/

/-- **A positive combination of a tile's two edge directions at a shared vertex, equal to
`e + ε e'` for the other tile's edge directions there, is fatal.**  This is
`MarchOverlap.Dissection.wedge_disjoint_combo` with `(α₂, β₂) = (1, ε)`. -/
theorem combo_dies {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {k₁ k₂ : Fin 3}
    (hshare : (D.tile i).pts k₁ = (D.tile j).pts k₂) {ε a b : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (hb : 0 < b)
    (h : ((D.tile j).pts (k₂ + 1) - (D.tile j).pts k₂)
          + ε • ((D.tile j).pts (k₂ + 2) - (D.tile j).pts k₂)
        = a • ((D.tile i).pts (k₁ + 1) - (D.tile i).pts k₁)
          + b • ((D.tile i).pts (k₁ + 2) - (D.tile i).pts k₁)) : False :=
  Erdos634.MarchOverlap.Dissection.wedge_disjoint_combo D hij hshare ha hb one_pos hε h
    (by rw [one_smul])

/-- The same, with every vertex given by its coordinates and both coefficients free: the
combination `ε e + ε' e'` is checked as two real identities. -/
theorem combo_dies_pts {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {k₁ k₂ : Fin 3}
    {v0 v1 X0 X1 Y0 Y1 E0 E1 E0' E1' : ℝ}
    (hv : (D.tile i).pts k₁ = mkPt v0 v1) (hv' : (D.tile j).pts k₂ = mkPt v0 v1)
    (hx : (D.tile i).pts (k₁ + 1) = mkPt X0 X1) (hy : (D.tile i).pts (k₁ + 2) = mkPt Y0 Y1)
    (he : (D.tile j).pts (k₂ + 1) = mkPt E0 E1) (he' : (D.tile j).pts (k₂ + 2) = mkPt E0' E1')
    {ε ε' a b : ℝ} (hε : 0 < ε) (hε' : 0 < ε') (ha : 0 < a) (hb : 0 < b)
    (h0 : ε * (E0 - v0) + ε' * (E0' - v0) = a * (X0 - v0) + b * (Y0 - v0))
    (h1 : ε * (E1 - v1) + ε' * (E1' - v1) = a * (X1 - v1) + b * (Y1 - v1)) : False := by
  refine Erdos634.MarchOverlap.Dissection.wedge_disjoint_combo D hij (hv.trans hv'.symm) ha hb hε hε'
    (v := ε • ((D.tile j).pts (k₂ + 1) - (D.tile j).pts k₂)
      + ε' • ((D.tile j).pts (k₂ + 2) - (D.tile j).pts k₂)) (plane_ext ?_ ?_) rfl
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply, hv, hv', hx, hy, he,
      he', mkPt_zero]; exact h0
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply, hv, hv', hx, hy, he,
      he', mkPt_one]; exact h1

/-! ## 4. Vertex data of the coordinate tiles -/

theorem range_aTileBG (x₀ f : ℝ) (hf : 1 < f) :
    Set.range (aTileBG x₀ f hf).pts
      = {mkPt (x₀ + f) 0, mkPt x₀ 0, mkPt (x₀ + dBG f) (apexH f)} := by
  rw [range_pts_eq]; rfl

theorem range_aTileGB (x₀ f : ℝ) (hf : 1 < f) :
    Set.range (aTileGB x₀ f hf).pts
      = {mkPt x₀ 0, mkPt (x₀ + f) 0, mkPt (x₀ + dGB f) (apexH f)} := by
  rw [range_pts_eq]; rfl

theorem range_flushFiller (t f : ℝ) (hf : 1 < f) :
    Set.range (flushFiller t f hf).pts
      = {mkPt (t + f) 0, mkPt (t + f + dBG f) (apexH f), mkPt (t + dBG f) (apexH f)} := by
  rw [range_pts_eq]; rfl

theorem range_offsetFiller (t f : ℝ) (hf : 1 < f) :
    Set.range (offsetFiller t f hf).pts
      = {mkPt (t + f) 0, mkPt (t + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f),
         mkPt (t + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f)} := by
  rw [range_pts_eq]; rfl

theorem mkPt_ne_of_fst {a b c d : ℝ} (h : a ≠ c) : mkPt a b ≠ mkPt c d :=
  fun he => h (mkPt_inj he).1

theorem mkPt_ne_of_snd {a b c d : ℝ} (h : b ≠ d) : mkPt a b ≠ mkPt c d :=
  fun he => h (mkPt_inj he).2

/-- A tile with the vertex set of `aTileBG x₀ f`, seen from its **right** base corner
`(x₀ + f, 0)`: the other two vertices in cyclic order. -/
theorem bg_data_right {T : Tri} {x₀ f : ℝ} (hf : 1 < f)
    (hr : Set.range T.pts = Set.range (aTileBG x₀ f hf).pts) {k : Fin 3}
    (hk : T.pts k = mkPt (x₀ + f) 0) :
    (T.pts (k + 1) = mkPt x₀ 0 ∧ T.pts (k + 2) = mkPt (x₀ + dBG f) (apexH f)) ∨
    (T.pts (k + 1) = mkPt (x₀ + dBG f) (apexH f) ∧ T.pts (k + 2) = mkPt x₀ 0) := by
  rw [range_aTileBG] at hr
  exact vertex_data_of_range hr hk

/-- The same tile seen from its **left** base corner `(x₀, 0)`. -/
theorem bg_data_left {T : Tri} {x₀ f : ℝ} (hf : 1 < f)
    (hr : Set.range T.pts = Set.range (aTileBG x₀ f hf).pts) {k : Fin 3}
    (hk : T.pts k = mkPt x₀ 0) :
    (T.pts (k + 1) = mkPt (x₀ + f) 0 ∧ T.pts (k + 2) = mkPt (x₀ + dBG f) (apexH f)) ∨
    (T.pts (k + 1) = mkPt (x₀ + dBG f) (apexH f) ∧ T.pts (k + 2) = mkPt (x₀ + f) 0) := by
  rw [range_aTileBG, Set.insert_comm] at hr
  exact vertex_data_of_range hr hk

/-- A tile with the vertex set of `aTileGB x₀ f`, seen from its left base corner `(x₀, 0)`. -/
theorem gb_data_left {T : Tri} {x₀ f : ℝ} (hf : 1 < f)
    (hr : Set.range T.pts = Set.range (aTileGB x₀ f hf).pts) {k : Fin 3}
    (hk : T.pts k = mkPt x₀ 0) :
    (T.pts (k + 1) = mkPt (x₀ + f) 0 ∧ T.pts (k + 2) = mkPt (x₀ + dGB f) (apexH f)) ∨
    (T.pts (k + 1) = mkPt (x₀ + dGB f) (apexH f) ∧ T.pts (k + 2) = mkPt (x₀ + f) 0) := by
  rw [range_aTileGB] at hr
  exact vertex_data_of_range hr hk

theorem mem_range_of_eq {T : Tri} {P : Plane} {S : Set Plane} (hr : Set.range T.pts = S)
    (hP : P ∈ S) : ∃ k, T.pts k = P := by
  rw [← hr] at hP; exact hP

/-! ## 5. `BG` then `GB` on the base is impossible — vertex-set form -/

/-- **`GB` after `BG` dies, for tiles given by their vertex sets.**  The `GB` tile's apex edge
`(dGB, h)` at the junction `(x₀, 0)` is strictly inside the `BG` tile's corner there: it is
`(1 − 1/f²)·(−f, 0) + 1·(dBG − f, h)`.  This is `MarchKills.no_bg_then_gb` freed of the vertex
order. -/
theorem gb_after_bg_dies {N : ℕ} (D : Dissection N) {f : ℝ} (hf : 1 < f) {i j : Fin N}
    (hij : i ≠ j) {x₀ : ℝ}
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG (x₀ - f) f hf).pts)
    (hB : Set.range (D.tile j).pts = Set.range (aTileGB x₀ f hf).pts) : False := by
  have hf0 : (0:ℝ) < f := by linarith
  have hb1 : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hsh : dBG f - dGB f = 2 * f - 1 / f := derived_run_shift f hf0.ne'
  obtain ⟨k₁, hk₁'⟩ := mem_range_of_eq hA (by rw [range_aTileBG]; left; rfl)
  obtain ⟨k₂, hk₂⟩ := mem_range_of_eq hB (by rw [range_aTileGB]; left; rfl)
  have hk₁ : (D.tile i).pts k₁ = mkPt x₀ 0 := by rw [hk₁']; congr 1; ring
  set a₀ : ℝ := 1 - 1 / f ^ 2 with ha₀
  have ha₀pos : 0 < a₀ := by
    rw [ha₀, sub_pos, div_lt_one (by positivity)]; nlinarith
  have hkey : a₀ * f = f - 1 / f := by rw [ha₀]; field_simp
  have hε : (0:ℝ) < 2 * f ^ 2 / (f ^ 2 - 1) := by positivity
  rcases bg_data_right hf hA hk₁' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases gb_data_left hf hB hk₂ with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · -- tile `i`: `(−f, 0)`, `(dBG − f, h)`; tile `j`: `(f, 0)`, `(dGB, h)`
    refine combo_dies_pts D hij hk₁ hk₂ h1 h2 h1' h2'
      (ε := 1) (ε' := 2 * f ^ 2 / (f ^ 2 - 1)) (a := 1) (b := 2 * f ^ 2 / (f ^ 2 - 1))
      one_pos hε one_pos hε ?_ ?_
    · unfold dBG dGB; field_simp; ring
    · ring
  · -- tile `j`: `(dGB, h)`, `(f, 0)`
    refine combo_dies_pts D hij hk₁ hk₂ h1 h2 h1' h2'
      (ε := 1) (ε' := a₀ / 2) (a := a₀ / 2) (b := 1) one_pos (by positivity) (by positivity)
      one_pos ?_ ?_
    · rw [ha₀]; unfold dBG dGB; field_simp; ring
    · ring
  · -- tile `i`: `(dBG − f, h)`, `(−f, 0)`; tile `j`: `(f, 0)`, `(dGB, h)`
    refine combo_dies_pts D hij hk₁ hk₂ h1 h2 h1' h2'
      (ε := 1) (ε' := 2 * f ^ 2 / (f ^ 2 - 1)) (a := 2 * f ^ 2 / (f ^ 2 - 1)) (b := 1)
      one_pos hε hε one_pos ?_ ?_
    · unfold dBG dGB; field_simp; ring
    · ring
  · refine combo_dies_pts D hij hk₁ hk₂ h1 h2 h1' h2'
      (ε := 1) (ε' := a₀ / 2) (a := 1) (b := a₀ / 2) one_pos (by positivity) one_pos
      (by positivity) ?_ ?_
    · rw [ha₀]; unfold dBG dGB; field_simp; ring
    · ring

/-! ## 6. The tile laying an `a`-letter on the base is `BG` or `GB` -/

theorem fin3_cover : ∀ k m n : Fin 3, k ≠ m → k ≠ n → m ≠ n → ∀ i, i = k ∨ i = m ∨ i = n := by
  decide

theorem fin3_third : ∀ k m : Fin 3, k ≠ m → ∃ n, n ≠ k ∧ n ≠ m := by decide

theorem fin3_succ : ∀ k m n : Fin 3, k ≠ m → k ≠ n → m ≠ n →
    (k + 1 = m ∧ k + 2 = n) ∨ (k + 1 = n ∧ k + 2 = m) := by decide

/-- **A tile with two vertices on the line `y = 0` has its third off it.** -/
theorem third_not_on_line (T : Tri) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n) (hmn : m ≠ n)
    (hk : (T.pts k) 1 = 0) (hm : (T.pts m) 1 = 0) : (T.pts n) 1 ≠ 0 := by
  intro hn
  have hall : ∀ i : Fin 3, (T.pts i) 1 = 0 := by
    intro i
    rcases fin3_cover k m n hkm hkn hmn i with rfl | rfl | rfl <;> assumption
  apply T.det_ne_zero
  unfold Tri.det
  simp only [PiLp.sub_apply, hall]; ring

theorem dist_sq_pts (p q : Plane) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem dist_sq_pt_mkPt (p : Plane) (a b : ℝ) :
    dist p (mkPt a b) ^ 2 = (p 0 - a) ^ 2 + (p 1 - b) ^ 2 := by
  have : p = mkPt (p 0) (p 1) := plane_ext (by simp) (by simp)
  conv_lhs => rw [this]
  rw [dist_sq_mkPt]

theorem dist_mkPt_base (a b : ℝ) (h : 0 ≤ b) : dist (mkPt a 0) (mkPt (a + b) 0) = b := by
  refine dist_eq_of_sq_eq ?_ dist_nonneg h
  rw [dist_sq_mkPt]; ring

/-- The model's three side lengths, from `ModelData`. -/
theorem model_dists {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hM : ModelData D f α β γ) :
    dist (D.model.pts 0) (D.model.pts 1) = f ^ 2 ∧ dist (D.model.pts 1) (D.model.pts 2) = f ∧
    dist (D.model.pts 2) (D.model.pts 0) = f ^ 2 - 1 := by
  have h0 := hM.hs0; have h1 := hM.hs1; have h2 := hM.hs2
  simp only [sideOpp] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · simpa using h2
  · simpa using h0
  · simpa using h1

/-- **The sides at the third vertex of an `a`-edge.**  If the edge `k m` of a tile of `D` has
length `a = f`, the third vertex `n` is at distances `{c, b} = {f², f²−1}` from `k, m`, in one of
the two orders. -/
theorem sides_of_a_edge {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) (j : Fin N) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n)
    (hmn : m ≠ n) (hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = f) :
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f ^ 2 - 1) ∨
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ^ 2 - 1 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f ^ 2) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_dists D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = f ^ 2 := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = f := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = f ^ 2 - 1 := by rw [dist_comm]; exact m20
  have hinj := σ.injective
  have hkm' : σ k ≠ σ m := fun h => hkm (hinj h)
  have hkn' : σ k ≠ σ n := fun h => hkn (hinj h)
  have hmn' : σ m ≠ σ n := fun h => hmn (hinj h)
  rw [hσ] at hd; rw [hσ, hσ]
  generalize σ k = sk at hd hkm' hkn' ⊢
  generalize σ m = sm at hd hkm' hmn' ⊢
  generalize σ n = sn at hkn' hmn' ⊢
  have hff : f ^ 2 ≠ f := by nlinarith
  have hff' : f ^ 2 - 1 ≠ f := by nlinarith
  fin_cases sk <;> fin_cases sm <;> fin_cases sn <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, m01, m12, m20, m10, m21, m02,
      dist_self] at hd hkm' hkn' hmn' ⊢ <;>
    first
    | exact absurd rfl hkm'
    | exact absurd rfl hkn'
    | exact absurd rfl hmn'
    | exact absurd hd hff
    | exact absurd hd hff'
    | simp

/-- **A tile laying the `a`-letter `[x₀, x₀ + f]` on the base is `aTileBG x₀` or `aTileGB x₀`**,
as a vertex set.  The third vertex is at distances `{b, c}` from the two ends, above the base
(it is in the target and off the line), so the two circles meet at the model's apex
(`MarchRunStep.bg_abscissa`, `.gb_abscissa`). -/
theorem a_letter_tile {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {j : Fin N} {x₀ : ℝ} {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + f) 0) :
    Set.range (D.tile j).pts = Set.range (aTileBG x₀ f (by linarith)).pts ∨
    Set.range (D.tile j).pts = Set.range (aTileGB x₀ f (by linarith)).pts := by
  have hf1 : 1 < f := by linarith
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = f := by
    rw [hk, hm]; exact dist_mkPt_base _ _ (by linarith)
  have hX0 : 0 ≤ ((D.tile j).pts n) 1 := by
    have := pts_mem_target D.toDissection j n
    rw [htgt] at this
    exact target_height_nonneg one_pos hf1 _ this
  have hXne : ((D.tile j).pts n) 1 ≠ 0 :=
    third_not_on_line (D.tile j) hkm (Ne.symm hnk) (Ne.symm hnm) (by rw [hk]; simp)
      (by rw [hm]; simp)
  have hXpos : 0 < ((D.tile j).pts n) 1 := lt_of_le_of_ne hX0 (Ne.symm hXne)
  have hsq : ((D.tile j).pts n) 1 ^ 2 = h2 f → ((D.tile j).pts n) 1 = apexH f := by
    intro h
    exact (sq_eq_sq₀ hXpos.le (apexH_pos hf1).le).mp (by rw [h, apexH_sq hf1])
  have hcyc := fin3_succ k m n hkm (Ne.symm hnk) (Ne.symm hnm)
  rcases sides_of_a_edge D hf hM j hkm (Ne.symm hnk) (Ne.symm hnm) hd with ⟨hXk, hXm⟩ | ⟨hXk, hXm⟩
  · -- `c` to the left end, `b` to the right: `BG`
    have e1 : (((D.tile j).pts n) 0 - x₀) ^ 2 + ((D.tile j).pts n) 1 ^ 2 = (f ^ 2) ^ 2 := by
      have := congrArg (· ^ 2) hXk; simp only at this
      rw [hk, dist_sq_pt_mkPt] at this; simpa using this
    have e2 : (((D.tile j).pts n) 0 - x₀ - f) ^ 2 + ((D.tile j).pts n) 1 ^ 2 = (f ^ 2 - 1) ^ 2 := by
      have := congrArg (· ^ 2) hXm; simp only at this
      rw [hm, dist_sq_pt_mkPt] at this
      convert this using 2 <;> ring
    have hx := Erdos634.MarchRunStep.bg_abscissa _ _ f hf1 e1 e2
    have hy : ((D.tile j).pts n) 1 = apexH f := by
      apply hsq; have := bg_left f hf0; rw [hx] at e1; linarith
    have hX : (D.tile j).pts n = mkPt (x₀ + dBG f) (apexH f) :=
      plane_ext (by simp; linarith) (by simpa using hy)
    left
    rw [range_pts_eq_cyclic _ k, range_aTileBG]
    rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hk, hm, hX] <;>
      (ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  · -- `b` to the left end, `c` to the right: `GB`
    have e1 : (((D.tile j).pts n) 0 - x₀) ^ 2 + ((D.tile j).pts n) 1 ^ 2 = (f ^ 2 - 1) ^ 2 := by
      have := congrArg (· ^ 2) hXk; simp only at this
      rw [hk, dist_sq_pt_mkPt] at this; simpa using this
    have e2 : (((D.tile j).pts n) 0 - x₀ - f) ^ 2 + ((D.tile j).pts n) 1 ^ 2 = (f ^ 2) ^ 2 := by
      have := congrArg (· ^ 2) hXm; simp only at this
      rw [hm, dist_sq_pt_mkPt] at this
      convert this using 2 <;> ring
    have hx := Erdos634.MarchRunStep.gb_abscissa _ _ f hf1 e1 e2
    have hy : ((D.tile j).pts n) 1 = apexH f := by
      apply hsq; have := gb_left f hf0; rw [hx] at e1; linarith
    have hX : (D.tile j).pts n = mkPt (x₀ + dGB f) (apexH f) :=
      plane_ext (by simp; linarith) (by simpa using hy)
    right
    rw [range_pts_eq_cyclic _ k, range_aTileGB]
    rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hk, hm, hX]
    all_goals (ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)

/-- **The `a`-letter after a `BG` tile is laid `BG`.**  (`a_letter_tile` + `gb_after_bg_dies`.)
This is `prop:orientmono`'s content at one junction, for a tile known only by its base edge. -/
theorem a_letter_after_bg {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {i j : Fin N} (hij : i ≠ j) {x₀ : ℝ}
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG (x₀ - f) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + f) 0) :
    Set.range (D.tile j).pts = Set.range (aTileBG x₀ f (by linarith)).pts := by
  rcases a_letter_tile D hf htgt hM hkm hk hm with h | h
  · exact h
  · exact absurd h (fun h => gb_after_bg_dies D.toDissection (by linarith) hij hA h)

/-! ## 7. The figure at an `a|a` junction: exactly one `α`-tile, distinct from the two `a`-tiles -/

theorem dist_apex_left {f : ℝ} (hf : 1 < f) (x₀ : ℝ) :
    dist (mkPt x₀ 0) (mkPt (x₀ + dBG f) (apexH f)) = f ^ 2 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
  rw [dist_sq_mkPt, show (x₀ - (x₀ + dBG f)) ^ 2 = dBG f ^ 2 by ring,
    show (0 - apexH f) ^ 2 = apexH f ^ 2 by ring, apexH_sq hf]
  exact bg_left f hf0

theorem dist_apex_right {f : ℝ} (hf : 1 < f) (x₀ : ℝ) :
    dist (mkPt (x₀ + f) 0) (mkPt (x₀ + dBG f) (apexH f)) = f ^ 2 - 1 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by nlinarith)
  rw [dist_sq_mkPt, show (x₀ + f - (x₀ + dBG f)) ^ 2 = (dBG f - f) ^ 2 by ring,
    show (0 - apexH f) ^ 2 = apexH f ^ 2 by ring, apexH_sq hf]
  exact bg_right f hf0

/-- **A tile with the vertex set of `aTileBG x₀ f` presents `γ` at its right base corner.** -/
theorem bg_localAngle_right {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {x₀ : ℝ}
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG x₀ f (by linarith)).pts) :
    (D.tile i).localAngle (mkPt (x₀ + f) 0) = γ := by
  have hf1 : 1 < f := by linarith
  obtain ⟨k, hk⟩ := mem_range_of_eq hA (by rw [range_aTileBG]; left; rfl)
  rw [← hk]
  refine (localAngle_of_oppSide D hf hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' i k).2.2 ?_
  rcases bg_data_right hf1 hA hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact dist_apex_left hf1 x₀
  · rw [dist_comm]; exact dist_apex_left hf1 x₀

/-- **… and `β` at its left base corner.** -/
theorem bg_localAngle_left {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {x₀ : ℝ}
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG x₀ f (by linarith)).pts) :
    (D.tile i).localAngle (mkPt x₀ 0) = β := by
  have hf1 : 1 < f := by linarith
  obtain ⟨k, hk⟩ := mem_range_of_eq hA (by rw [range_aTileBG]; right; left; rfl)
  rw [← hk]
  refine (localAngle_of_oppSide D hf hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' i k).2.1 ?_
  rcases bg_data_left hf1 hA hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact dist_apex_right hf1 x₀
  · rw [dist_comm]; exact dist_apex_right hf1 x₀

/-- **At an `a|a` junction of two `BG` tiles there is exactly one further tile, and it presents
`α`.**  The junction `(x₀, 0)` is a straight boundary point; the left tile presents `γ`, the
right one `β`; the trichotomy `TileAt.congruentDissection_boundary_figure_cases` leaves only the
figure `{α, β, γ}`. -/
theorem junction_alpha_tile {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f) {i j : Fin N}
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG (x₀ - f) f (by linarith)).pts)
    (hB : Set.range (D.tile j).pts = Set.range (aTileBG x₀ f (by linarith)).pts) :
    ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = α ∧
      ∀ l', (D.tile l').localAngle (mkPt x₀ 0) = α → l' = l := by
  classical
  have hf1 : 1 < f := by linarith
  obtain ⟨hαβ', hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ := distinct_of_pos_ne hα hβpos hαβ hγdef hrel
  have hv : mkPt x₀ 0 ∈ frontier D.target.carrier := by
    rw [htgt]; exact base_point_mem_frontier hf1 hx0.le hxL.le
  have hnv : mkPt x₀ 0 ∉ Set.range D.target.pts := by
    rw [htgt]; exact base_point_not_vertex hf1 hx0 hxL
  have hiγ : (D.tile i).localAngle (mkPt x₀ 0) = γ := by
    have := bg_localAngle_right D hf hM hA
    rwa [show x₀ - f + f = x₀ by ring] at this
  have hjβ : (D.tile j).localAngle (mkPt x₀ 0) = β := bg_localAngle_left D hf hM hB
  have hγpos : 0 < ({m | (D.tile m).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨i, by simp [hiγ]⟩
  rcases Erdos634.Geometry.Dissection.congruentDissection_boundary_figure_cases D α β γ hαβ' hαγ
      hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hM.hα' hM.hβ' hM.hγ' hv hnv with
    ⟨_, _, _, hG⟩ | ⟨_, _, hG⟩ | ⟨hAc, _, _⟩
  · omega
  · omega
  · obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hAc
    have hlmem : l ∈ ({m | (D.tile m).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)) := by
      rw [hl]; exact Finset.mem_singleton_self l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlmem
    refine ⟨l, ?_, ?_, hlmem, ?_⟩
    · rintro rfl; rw [hlmem] at hiγ; exact hαγ hiγ
    · rintro rfl; rw [hlmem] at hjβ; exact hαβ' hjβ
    · intro l' hl'
      have : l' ∈ ({m | (D.tile m).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)) := by
        simp [hl']
      rw [hl] at this; exact Finset.mem_singleton.mp this

/-! ## 8. The `α`-tile has its corner at the junction with sides `{b, c}` -/

/-- **A tile presenting `α` at `v` has a vertex there, opposite side `a = f`, adjacent sides
`{b, c}`.** -/
theorem alpha_corner_data {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) {l : Fin N} {v : Plane}
    (hl : (D.tile l).localAngle v = α) :
    ∃ k : Fin 3, (D.tile l).pts k = v ∧
      dist ((D.tile l).pts (k + 1)) ((D.tile l).pts (k + 2)) = f ∧
      ((dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = f ^ 2 ∧
        dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = f ^ 2 - 1) ∨
       (dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = f ^ 2 - 1 ∧
        dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = f ^ 2)) := by
  have hπ := Real.pi_pos
  have hαπ : α < Real.pi := by nlinarith
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile l) v with ⟨k, hk, hang⟩ | h | h | h
  · rw [hang] at hl
    -- the opposite side is `f`: the corner angle `α` is the model's angle at vertex `0`
    obtain ⟨k', hk'ang, hk'd⟩ :=
      Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent l).symm k
    rw [hl] at hk'ang
    have hk'0 : k' = 0 := by
      by_contra hne
      have hαγ : α ≠ γ := by rw [hγdef]; intro h; linarith
      fin_cases k'
      · exact hne rfl
      · exact hαβ (hk'ang.trans hM.hβ')
      · exact hαγ (hk'ang.trans hM.hγ')
    subst hk'0
    have hopp : dist ((D.tile l).pts (k + 1)) ((D.tile l).pts (k + 2)) = f := by
      rw [← hk'd]; exact (model_dists D hM).2.1
    refine ⟨k, hk.symm, hopp, ?_⟩
    have hne1 : k + 1 ≠ k + 2 := by
      have : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
      exact this k
    have hne2 : k + 1 ≠ k := by
      have : ∀ k : Fin 3, k + 1 ≠ k := by decide
      exact this k
    have hne3 : k + 2 ≠ k := by
      have : ∀ k : Fin 3, k + 2 ≠ k := by decide
      exact this k
    rcases sides_of_a_edge D hf hM l hne1 hne2 hne3 hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
  · rw [h] at hl; linarith
  · rw [h] at hl; linarith
  · rw [h] at hl; linarith

/-! ## 9. The `α`-tile's edges lie in the closed uncovered wedge -/

/-- The nondegeneracy of a tile at a vertex, as a cross product of its edge vectors. -/
theorem cross_edges_ne_zero (T : Tri) (k : Fin 3) :
    ((T.pts (k + 1)) 0 - (T.pts k) 0) * ((T.pts (k + 2)) 1 - (T.pts k) 1)
      - ((T.pts (k + 1)) 1 - (T.pts k) 1) * ((T.pts (k + 2)) 0 - (T.pts k) 0) ≠ 0 := by
  have := T.det_ne_zero
  rw [← T.det_cyclic k] at this
  simpa [cross] using this

/-- A convenient `ε` for pushing a direction off the boundary of an open cone: for `δ > 0` and any
`m`, the number `ε = δ / (2(|m| + 1))` is positive and satisfies `ε m < δ`. -/
theorem push_eps {δ m : ℝ} (hδ : 0 < δ) :
    0 < δ / (2 * (|m| + 1)) ∧ δ / (2 * (|m| + 1)) * m < δ := by
  have hm : 0 < |m| + 1 := by positivity
  refine ⟨by positivity, ?_⟩
  have h1 : δ / (2 * (|m| + 1)) * m ≤ δ / (2 * (|m| + 1)) * |m| :=
    mul_le_mul_of_nonneg_left (le_abs_self m) (by positivity)
  have h2 : δ / (2 * (|m| + 1)) * |m| < δ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg m]
  linarith

/-- **The `α`-tile's edge at the junction lies in the closed wedge.**  Let `l` be a tile with
vertex `k` at `v = (x₀, 0)` whose two edges there go to `E` and `E'` (in either cyclic order), and
let `i`, `j` be the tiles with the vertex sets of `aTileBG (x₀ − f)`, `aTileBG x₀`.  Then, with
`p = dBG − f`, `q = dBG`, `h = apexH f`, the edge vector `E − v = (u, w)` satisfies
`p·w ≤ h·u ≤ q·w`: it is not strictly inside the left tile's corner (`h u < p w`, `w > 0`) nor
the right tile's (`h u > q w`, `w > 0`), and it is not on the base line (`w = 0`), because in each
case a small push toward the other edge lands a positive combination of both tiles' edges
(`combo_dies_pts`). -/
theorem edge_in_wedge {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    {x₀ : ℝ} {i j l : Fin N} (hli : l ≠ i) (hlj : l ≠ j)
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG (x₀ - f) f (by linarith)).pts)
    (hB : Set.range (D.tile j).pts = Set.range (aTileBG x₀ f (by linarith)).pts)
    {k : Fin 3} (hk : (D.tile l).pts k = mkPt x₀ 0) {E E' : Plane}
    (hEE' : ((D.tile l).pts (k + 1) = E ∧ (D.tile l).pts (k + 2) = E') ∨
            ((D.tile l).pts (k + 1) = E' ∧ (D.tile l).pts (k + 2) = E)) :
    (dBG f - f) * (E 1) ≤ apexH f * (E 0 - x₀) ∧ apexH f * (E 0 - x₀) ≤ dBG f * (E 1) := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hh := apexH_pos hf1
  set p := dBG f - f with hp
  set q := dBG f with hq
  set h := apexH f with hh'
  have hpq : q - p = f := by rw [hp]; ring
  -- heights of the two edge points are `≥ 0`
  have hE1 : 0 ≤ E 1 := by
    have h1 := pts_mem_target D.toDissection l (k + 1)
    have h2 := pts_mem_target D.toDissection l (k + 2)
    rw [htgt] at h1 h2
    rcases hEE' with ⟨h, -⟩ | ⟨-, h⟩
    · rw [h] at h1; exact target_height_nonneg one_pos hf1 _ h1
    · rw [h] at h2; exact target_height_nonneg one_pos hf1 _ h2
  have hE1' : 0 ≤ E' 1 := by
    have h1 := pts_mem_target D.toDissection l (k + 1)
    have h2 := pts_mem_target D.toDissection l (k + 2)
    rw [htgt] at h1 h2
    rcases hEE' with ⟨-, h⟩ | ⟨h, -⟩
    · rw [h] at h2; exact target_height_nonneg one_pos hf1 _ h2
    · rw [h] at h1; exact target_height_nonneg one_pos hf1 _ h1
  -- nondegeneracy: `E − v` and `E' − v` are not parallel
  have hcross : (E 0 - x₀) * (E' 1) - (E 1) * (E' 0 - x₀) ≠ 0 := by
    have := cross_edges_ne_zero (D.tile l) k
    rw [hk] at this
    simp only [mkPt_zero, mkPt_one, sub_zero] at this
    rcases hEE' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at this; exact this
    · rw [h1, h2] at this; intro hc; apply this; linear_combination -hc
  -- the two tiles' vertices at `v`
  obtain ⟨kA, hkA'⟩ := mem_range_of_eq hA (by rw [range_aTileBG]; left; rfl)
  have hkA : (D.tile i).pts kA = mkPt x₀ 0 := by rw [hkA']; congr 1; ring
  obtain ⟨kB, hkB⟩ := mem_range_of_eq hB (by rw [range_aTileBG]; right; left; rfl)
  have hEpt : E = mkPt (E 0) (E 1) := plane_ext (by simp) (by simp)
  have hEpt' : E' = mkPt (E' 0) (E' 1) := plane_ext (by simp) (by simp)
  -- the pushed height is positive
  have hw : ∀ ε : ℝ, 0 < ε → 0 < E 1 + ε * E' 1 := by
    intro ε hε
    rcases lt_or_eq_of_le hE1 with h1 | h1
    · positivity
    · rcases lt_or_eq_of_le hE1' with h2 | h2
      · rw [← h1]; simp; positivity
      · exfalso; apply hcross; rw [← h1, ← h2]; ring
  constructor
  · -- not strictly inside the left tile's corner
    by_contra hlt
    have hlt := not_le.mp hlt
    set δ := p * E 1 - h * (E 0 - x₀) with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨hε, hεm⟩ := push_eps (m := h * (E' 0 - x₀) - p * E' 1) hδpos
    set ε := δ / (2 * (|h * (E' 0 - x₀) - p * E' 1| + 1)) with hεdef
    have hwpos := hw ε hε
    -- the coefficients on the left tile's edges `(−f, 0)`, `(p, h)`
    have hb : 0 < (E 1 + ε * E' 1) / h := by positivity
    have ha : 0 < (p * (E 1 + ε * E' 1) - h * (E 0 - x₀ + ε * (E' 0 - x₀))) / (f * h) := by
      apply div_pos _ (by positivity)
      nlinarith
    rcases bg_data_right hf1 hA hkA' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hEE' with ⟨hE, hE'⟩ | ⟨hE, hE'⟩
    · refine combo_dies_pts D.toDissection (Ne.symm hli) hkA hk h1 h2 (hE.trans hEpt) (hE'.trans hEpt')
        (ε := 1) (ε' := ε) one_pos hε ha hb ?_ ?_
      · rw [hp]; field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hli) hkA hk h1 h2 (hE.trans hEpt') (hE'.trans hEpt)
        (ε := ε) (ε' := 1) hε one_pos ha hb ?_ ?_
      · rw [hp]; field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hli) hkA hk h1 h2 (hE.trans hEpt) (hE'.trans hEpt')
        (ε := 1) (ε' := ε) one_pos hε hb ha ?_ ?_
      · rw [hp]; field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hli) hkA hk h1 h2 (hE.trans hEpt') (hE'.trans hEpt)
        (ε := ε) (ε' := 1) hε one_pos hb ha ?_ ?_
      · rw [hp]; field_simp; ring
      · field_simp; ring
  · -- not strictly inside the right tile's corner
    by_contra hlt
    have hlt := not_le.mp hlt
    set δ := h * (E 0 - x₀) - q * E 1 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨hε, hεm⟩ := push_eps (m := q * E' 1 - h * (E' 0 - x₀)) hδpos
    set ε := δ / (2 * (|q * E' 1 - h * (E' 0 - x₀)| + 1)) with hεdef
    have hwpos := hw ε hε
    -- the coefficients on the right tile's edges `(f, 0)`, `(q, h)`
    have hb : 0 < (E 1 + ε * E' 1) / h := by positivity
    have ha : 0 < (h * (E 0 - x₀ + ε * (E' 0 - x₀)) - q * (E 1 + ε * E' 1)) / (f * h) := by
      apply div_pos _ (by positivity)
      nlinarith
    rcases bg_data_left hf1 hB hkB with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hEE' with ⟨hE, hE'⟩ | ⟨hE, hE'⟩
    · refine combo_dies_pts D.toDissection (Ne.symm hlj) hkB hk h1 h2 (hE.trans hEpt) (hE'.trans hEpt')
        (ε := 1) (ε' := ε) one_pos hε ha hb ?_ ?_
      · field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hlj) hkB hk h1 h2 (hE.trans hEpt') (hE'.trans hEpt)
        (ε := ε) (ε' := 1) hε one_pos ha hb ?_ ?_
      · field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hlj) hkB hk h1 h2 (hE.trans hEpt) (hE'.trans hEpt')
        (ε := 1) (ε' := ε) one_pos hε hb ha ?_ ?_
      · field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hlj) hkB hk h1 h2 (hE.trans hEpt') (hE'.trans hEpt)
        (ε := ε) (ε' := 1) hε one_pos hb ha ?_ ?_
      · field_simp; ring
      · field_simp; ring

/-! ## 10. Extremality: two edges spanning the full opening of a wedge are its boundary rays -/

/-- **The Gram-form extremal lemma.**  Let `r₁, r₂` span a wedge, with Gram data
`|r₁|² = B`, `|r₂|² = C`, `⟨r₁, r₂⟩ = κ`, `BC − κ² > 0`.  Two vectors `e₁ = a₁r₁ + b₁r₂`,
`e₂ = a₂r₁ + b₂r₂` in the closed wedge (`a, b ≥ 0`) with the *same* Gram data are the pair
`(r₁, r₂)` itself or its reflection in the bisector, `(√(B/C)·r₂, √(C/B)·r₁)`.  The proof is the
Gram determinant identity (`det X = ±1`) and one polynomial certificate per sign. -/
theorem gram_extremal {B C κ a₁ b₁ a₂ b₂ : ℝ} (hB : 0 < B) (hC : 0 < C) (hκ : 0 < κ)
    (hdet : 0 < B * C - κ ^ 2)
    (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂)
    (G1 : a₁ ^ 2 * B + 2 * a₁ * b₁ * κ + b₁ ^ 2 * C = B)
    (G2 : a₂ ^ 2 * B + 2 * a₂ * b₂ * κ + b₂ ^ 2 * C = C)
    (G3 : a₁ * a₂ * B + (a₁ * b₂ + a₂ * b₁) * κ + b₁ * b₂ * C = κ) :
    (a₁ = 1 ∧ b₁ = 0 ∧ a₂ = 0 ∧ b₂ = 1) ∨
    (a₁ = 0 ∧ b₂ = 0 ∧ b₁ ^ 2 * C = B ∧ a₂ ^ 2 * B = C) := by
  have hgram : (a₁ * b₂ - a₂ * b₁) ^ 2 * (B * C - κ ^ 2) = 1 * (B * C - κ ^ 2) := by
    have e : (a₁ ^ 2 * B + 2 * a₁ * b₁ * κ + b₁ ^ 2 * C) * (a₂ ^ 2 * B + 2 * a₂ * b₂ * κ + b₂ ^ 2 * C)
        - (a₁ * a₂ * B + (a₁ * b₂ + a₂ * b₁) * κ + b₁ * b₂ * C) ^ 2
        = (a₁ * b₂ - a₂ * b₁) ^ 2 * (B * C - κ ^ 2) := by ring
    rw [G1, G2, G3] at e; linarith
  have hd2 : (a₁ * b₂ - a₂ * b₁) ^ 2 = 1 := mul_right_cancel₀ hdet.ne' hgram
  have hfac : (a₁ * b₂ - a₂ * b₁ - 1) * (a₁ * b₂ - a₂ * b₁ + 1) = 0 := by linear_combination hd2
  rcases mul_eq_zero.mp hfac with h | h
  · -- rotation: `det = 1`
    have Gd : a₁ * b₂ - a₂ * b₁ = 1 := by linarith
    have hsum : a₂ * B + b₁ * C = 0 := by
      linear_combination b₂ * G3 - (b₂ * κ + a₂ * B) * Gd - b₁ * G2
    have ha₂0 : a₂ = 0 := by nlinarith [mul_nonneg ha₂ hB.le, mul_nonneg hb₁ hC.le]
    have hb₁0 : b₁ = 0 := by nlinarith [mul_nonneg ha₂ hB.le, mul_nonneg hb₁ hC.le]
    subst ha₂0; subst hb₁0
    have h1 : a₁ ^ 2 = 1 := by
      have : (a₁ ^ 2 - 1) * B = 0 := by linear_combination G1
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hB.ne'
    have h2 : b₂ ^ 2 = 1 := by
      have : (b₂ ^ 2 - 1) * C = 0 := by linear_combination G2
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hC.ne'
    left
    refine ⟨?_, rfl, rfl, ?_⟩
    · exact (sq_eq_sq₀ ha₁ zero_le_one).mp (by rw [h1]; norm_num)
    · exact (sq_eq_sq₀ hb₂ zero_le_one).mp (by rw [h2]; norm_num)
  · -- reflection: `det = −1`
    have Gd : a₁ * b₂ - a₂ * b₁ = -1 := by linarith
    have h1 : b₁ * C = a₂ * B - 2 * a₁ * κ := by
      linear_combination a₂ * G1 - a₁ * G3 + (a₁ * κ + b₁ * C) * Gd
    have h2 : a₂ * B = b₁ * C - 2 * b₂ * κ := by
      linear_combination b₁ * G2 - b₂ * G3 + (b₂ * κ + a₂ * B) * Gd
    have hsum : 2 * κ * (a₁ + b₂) = 0 := by linear_combination h1 + h2
    have hab : a₁ + b₂ = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · linarith
      · exact h
    have ha₁0 : a₁ = 0 := by linarith
    have hb₂0 : b₂ = 0 := by linarith
    subst ha₁0; subst hb₂0
    right
    refine ⟨rfl, rfl, by linear_combination G1, by linear_combination G2⟩

/-- **Extremality in the junction's coordinates.**  With `p = dBG − f`, `q = dBG`, `h = apexH f`
(so the wedge's rays are `r₁ = (p, h)` of length `b` and `r₂ = (q, h)` of length `c`): two
vectors `(u, w)`, `(u', w')` in the closed wedge `p·w ≤ h·u ≤ q·w`, of lengths `b` and `c`, at
distance `a = f` from each other, are `(r₁, r₂)` — the flush filler's edges — or
`((b/c)·r₂, (c/b)·r₁)` — the offset filler's. -/
theorem wedge_extremal_coords {f : ℝ} (hf : 1 < f) {u w u' w' : ℝ}
    (hw1 : (dBG f - f) * w ≤ apexH f * u) (hw2 : apexH f * u ≤ dBG f * w)
    (hw1' : (dBG f - f) * w' ≤ apexH f * u') (hw2' : apexH f * u' ≤ dBG f * w')
    (hb : u ^ 2 + w ^ 2 = (f ^ 2 - 1) ^ 2) (hc : u' ^ 2 + w' ^ 2 = (f ^ 2) ^ 2)
    (ha : (u - u') ^ 2 + (w - w') ^ 2 = f ^ 2) :
    (u = dBG f - f ∧ w = apexH f ∧ u' = dBG f ∧ w' = apexH f) ∨
    (u = (f ^ 2 - 1) / f ^ 2 * dBG f ∧ w = (f ^ 2 - 1) / f ^ 2 * apexH f ∧
     u' = f ^ 2 / (f ^ 2 - 1) * (dBG f - f) ∧ w' = f ^ 2 / (f ^ 2 - 1) * apexH f) := by
  have hf0 : (0:ℝ) < f := by linarith
  have hfne : f ≠ 0 := hf0.ne'
  have hb1 : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  obtain ⟨p, hp⟩ : ∃ p, p = dBG f - f := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = dBG f := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h, h = apexH f := ⟨_, rfl⟩
  have hppos : 0 < p := by rw [hp]; linarith [dBG_gt_f hf]
  have hqpos : 0 < q := by rw [hq]; exact dBG_pos hf
  have hh : 0 < h := by rw [hhdef]; exact apexH_pos hf
  have hqp : q - p = f := by rw [hp, hq]; ring
  have hB : p ^ 2 + h ^ 2 = (f ^ 2 - 1) ^ 2 := by
    rw [hhdef, apexH_sq hf, hp]; exact bg_right f hfne
  have hC : q ^ 2 + h ^ 2 = (f ^ 2) ^ 2 := by
    rw [hhdef, apexH_sq hf, hq]; exact bg_left f hfne
  rw [← hp] at hw1 hw1' ⊢
  rw [← hq] at hw2 hw2' ⊢
  rw [← hhdef] at hw1 hw2 hw1' hw2' ⊢
  -- the wedge coordinates of `(u, w)` and `(u', w')`
  obtain ⟨a₁, ha₁⟩ : ∃ a, a = (q * w - h * u) / (h * f) := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b, b = (h * u - p * w) / (h * f) := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a, a = (q * w' - h * u') / (h * f) := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b, b = (h * u' - p * w') / (h * f) := ⟨_, rfl⟩
  have ha₁0 : 0 ≤ a₁ := by rw [ha₁]; exact div_nonneg (by linarith) (by positivity)
  have hb₁0 : 0 ≤ b₁ := by rw [hb₁]; exact div_nonneg (by linarith) (by positivity)
  have ha₂0 : 0 ≤ a₂ := by rw [ha₂]; exact div_nonneg (by linarith) (by positivity)
  have hb₂0 : 0 ≤ b₂ := by rw [hb₂]; exact div_nonneg (by linarith) (by positivity)
  have hhf : h * f ≠ 0 := by positivity
  have eu : u = a₁ * p + b₁ * q := by
    rw [ha₁, hb₁]; field_simp; rw [← hqp]; ring
  have ew : w = (a₁ + b₁) * h := by
    rw [ha₁, hb₁]; field_simp; rw [← hqp]; ring
  have eu' : u' = a₂ * p + b₂ * q := by
    rw [ha₂, hb₂]; field_simp; rw [← hqp]; ring
  have ew' : w' = (a₂ + b₂) * h := by
    rw [ha₂, hb₂]; field_simp; rw [← hqp]; ring
  -- the Gram data of the wedge
  have hκ : p * q + h ^ 2 = ((f ^ 2 - 1) ^ 2 + (f ^ 2) ^ 2 - f ^ 2) / 2 := by
    rw [← hB, ← hC, ← hqp]; ring
  have hκpos : 0 < p * q + h ^ 2 := by positivity
  have hdet : 0 < (p ^ 2 + h ^ 2) * (q ^ 2 + h ^ 2) - (p * q + h ^ 2) ^ 2 := by
    have : (p ^ 2 + h ^ 2) * (q ^ 2 + h ^ 2) - (p * q + h ^ 2) ^ 2 = h ^ 2 * (q - p) ^ 2 := by ring
    rw [this, hqp]; positivity
  -- the Gram equations of `(u, w)`, `(u', w')`
  have hb' := hb; rw [eu, ew] at hb'
  have hc' := hc; rw [eu', ew'] at hc'
  have hinner : u * u' + w * w' = ((f ^ 2 - 1) ^ 2 + (f ^ 2) ^ 2 - f ^ 2) / 2 := by
    linear_combination (1/2 : ℝ) * hb + (1/2 : ℝ) * hc - (1/2 : ℝ) * ha
  rw [eu, ew, eu', ew'] at hinner
  have G1 : a₁ ^ 2 * (p ^ 2 + h ^ 2) + 2 * a₁ * b₁ * (p * q + h ^ 2) + b₁ ^ 2 * (q ^ 2 + h ^ 2)
      = p ^ 2 + h ^ 2 := by
    have key : a₁ ^ 2 * (p ^ 2 + h ^ 2) + 2 * a₁ * b₁ * (p * q + h ^ 2) + b₁ ^ 2 * (q ^ 2 + h ^ 2)
        = (a₁ * p + b₁ * q) ^ 2 + ((a₁ + b₁) * h) ^ 2 := by ring
    rw [key, hb']; exact hB.symm
  have G2 : a₂ ^ 2 * (p ^ 2 + h ^ 2) + 2 * a₂ * b₂ * (p * q + h ^ 2) + b₂ ^ 2 * (q ^ 2 + h ^ 2)
      = q ^ 2 + h ^ 2 := by
    have key : a₂ ^ 2 * (p ^ 2 + h ^ 2) + 2 * a₂ * b₂ * (p * q + h ^ 2) + b₂ ^ 2 * (q ^ 2 + h ^ 2)
        = (a₂ * p + b₂ * q) ^ 2 + ((a₂ + b₂) * h) ^ 2 := by ring
    rw [key, hc']; exact hC.symm
  have G3 : a₁ * a₂ * (p ^ 2 + h ^ 2) + (a₁ * b₂ + a₂ * b₁) * (p * q + h ^ 2)
      + b₁ * b₂ * (q ^ 2 + h ^ 2) = p * q + h ^ 2 := by
    have key : a₁ * a₂ * (p ^ 2 + h ^ 2) + (a₁ * b₂ + a₂ * b₁) * (p * q + h ^ 2)
        + b₁ * b₂ * (q ^ 2 + h ^ 2)
        = (a₁ * p + b₁ * q) * (a₂ * p + b₂ * q) + (a₁ + b₁) * h * ((a₂ + b₂) * h) := by ring
    rw [key, hinner]; exact hκ.symm
  rcases gram_extremal (by positivity) (by positivity) hκpos hdet ha₁0 hb₁0 ha₂0 hb₂0 G1 G2 G3 with
    ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    rw [eu, ew, eu', ew', h1, h2, h3, h4]
    refine ⟨by ring, by ring, by ring, by ring⟩
  · right
    have hb₁v : b₁ = (f ^ 2 - 1) / f ^ 2 := by
      have hsq : b₁ ^ 2 = ((f ^ 2 - 1) / f ^ 2) ^ 2 := by
        rw [hB, hC] at h3; field_simp; linear_combination h3
      exact (sq_eq_sq₀ hb₁0 (by positivity)).mp hsq
    have ha₂v : a₂ = f ^ 2 / (f ^ 2 - 1) := by
      have hsq : a₂ ^ 2 = (f ^ 2 / (f ^ 2 - 1)) ^ 2 := by
        rw [hB, hC] at h4; field_simp; linear_combination h4
      exact (sq_eq_sq₀ ha₂0 (by positivity)).mp hsq
    rw [eu, ew, eu', ew', h1, h2, hb₁v, ha₂v]
    refine ⟨by ring, by ring, by ring, by ring⟩

/-- **The `α`-tile at an `a|a` junction is the flush or the offset filler**, as a vertex set. -/
theorem alpha_tile_is_filler {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    {x₀ : ℝ} {i j l : Fin N} (hli : l ≠ i) (hlj : l ≠ j)
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG (x₀ - f) f (by linarith)).pts)
    (hB : Set.range (D.tile j).pts = Set.range (aTileBG x₀ f (by linarith)).pts)
    (hl : (D.tile l).localAngle (mkPt x₀ 0) = α) :
    Set.range (D.tile l).pts = Set.range (flushFiller (x₀ - f) f (by linarith)).pts ∨
    Set.range (D.tile l).pts = Set.range (offsetFiller (x₀ - f) f (by linarith)).pts := by
  have hf1 : 1 < f := by linarith
  obtain ⟨k, hk, hopp, hsides⟩ := alpha_corner_data D hf hM hα hβpos hαβ hγdef hrel hl
  have hw1 := edge_in_wedge D hf htgt hli hlj hA hB hk
    (E := (D.tile l).pts (k + 1)) (E' := (D.tile l).pts (k + 2)) (Or.inl ⟨rfl, rfl⟩)
  have hw2 := edge_in_wedge D hf htgt hli hlj hA hB hk
    (E := (D.tile l).pts (k + 2)) (E' := (D.tile l).pts (k + 1)) (Or.inr ⟨rfl, rfl⟩)
  set E := (D.tile l).pts (k + 1) with hE
  set E' := (D.tile l).pts (k + 2) with hE'
  have hEpt : E = mkPt (E 0) (E 1) := plane_ext (by simp) (by simp)
  have hEpt' : E' = mkPt (E' 0) (E' 1) := plane_ext (by simp) (by simp)
  -- squared distances
  have hd1 : dist ((D.tile l).pts k) E ^ 2 = (E 0 - x₀) ^ 2 + E 1 ^ 2 := by
    rw [dist_comm, hk, dist_sq_pt_mkPt]; ring
  have hd2 : dist ((D.tile l).pts k) E' ^ 2 = (E' 0 - x₀) ^ 2 + E' 1 ^ 2 := by
    rw [dist_comm, hk, dist_sq_pt_mkPt]; ring
  have hd12 : dist E E' ^ 2 = ((E 0 - x₀) - (E' 0 - x₀)) ^ 2 + (E 1 - E' 1) ^ 2 := by
    rw [dist_sq_pts]; ring
  have hopp2 : ((E 0 - x₀) - (E' 0 - x₀)) ^ 2 + (E 1 - E' 1) ^ 2 = f ^ 2 := by
    rw [← hd12, hopp]
  have hrange : Set.range (D.tile l).pts = {mkPt x₀ 0, E, E'} := by
    rw [range_pts_eq_cyclic _ k, hk]
  rcases hsides with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
  · -- `|E − v| = c`, `|E' − v| = b`: apply extremality to `(E', E)`
    have hb' : (E' 0 - x₀) ^ 2 + E' 1 ^ 2 = (f ^ 2 - 1) ^ 2 := by rw [← hd2, hs2]
    have hc' : (E 0 - x₀) ^ 2 + E 1 ^ 2 = (f ^ 2) ^ 2 := by rw [← hd1, hs1]
    have ha' : ((E' 0 - x₀) - (E 0 - x₀)) ^ 2 + (E' 1 - E 1) ^ 2 = f ^ 2 := by
      rw [← hopp2]; ring
    rcases wedge_extremal_coords hf1 hw2.1 hw2.2 hw1.1 hw1.2 hb' hc' ha' with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · left
      rw [hrange, range_flushFiller, hEpt, hEpt', h2, h4,
        show E 0 = x₀ - f + f + dBG f by linarith, show E' 0 = x₀ - f + dBG f by linarith,
        show x₀ - f + f = x₀ by ring]
    · right
      rw [hrange, range_offsetFiller, hEpt, hEpt', h2, h4,
        show E 0 = x₀ - f + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f) by linarith,
        show E' 0 = x₀ - f + f + (f ^ 2 - 1) / f ^ 2 * dBG f by linarith,
        show x₀ - f + f = x₀ by ring]
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · -- `|E − v| = b`, `|E' − v| = c`: apply extremality to `(E, E')`
    have hb' : (E 0 - x₀) ^ 2 + E 1 ^ 2 = (f ^ 2 - 1) ^ 2 := by rw [← hd1, hs1]
    have hc' : (E' 0 - x₀) ^ 2 + E' 1 ^ 2 = (f ^ 2) ^ 2 := by rw [← hd2, hs2]
    rcases wedge_extremal_coords hf1 hw1.1 hw1.2 hw2.1 hw2.2 hb' hc' hopp2 with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · left
      rw [hrange, range_flushFiller, hEpt, hEpt', h2, h4,
        show E 0 = x₀ - f + dBG f by linarith, show E' 0 = x₀ - f + f + dBG f by linarith,
        show x₀ - f + f = x₀ by ring]
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    · right
      rw [hrange, range_offsetFiller, hEpt, hEpt', h2, h4,
        show E 0 = x₀ - f + f + (f ^ 2 - 1) / f ^ 2 * dBG f by linarith,
        show E' 0 = x₀ - f + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f) by linarith,
        show x₀ - f + f = x₀ by ring]

/-! ## 11. THE JUNCTION STEP -/

/-- Two tiles of `D` are distinct if one has a vertex the other's vertex set lacks. -/
theorem ne_of_vertex {N : ℕ} (D : Dissection N) {i j : Fin N} {S : Set Plane}
    (hi : Set.range (D.tile i).pts = S) {k : Fin 3} {P : Plane} (hk : (D.tile j).pts k = P)
    (hP : P ∉ S) : i ≠ j := by
  rintro rfl
  exact hP (hi ▸ hk ▸ ⟨k, rfl⟩)

theorem next_letter_ne {N : ℕ} (D : Dissection N) {f : ℝ} (hf : 1 < f) {i j : Fin N} {t : ℝ}
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG t f hf).pts) {m : Fin 3}
    (hm : (D.tile j).pts m = mkPt (t + f + f) 0) : i ≠ j := by
  refine ne_of_vertex D hA hm ?_
  rw [range_aTileBG]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  have hpos := apexH_pos hf
  refine ⟨mkPt_ne_of_fst (by linarith), mkPt_ne_of_fst (by linarith), mkPt_ne_of_snd hpos.ne⟩

/-- **THE `a|a` JUNCTION STEP.**  Let `D` be a congruent dissection of the `e = 1` target in
normal position, with model sides `f, f²−1, f²` and angles `0 < α`, `0 < β`, `α ≠ β`, `γ = 2α + β`,
`3α + 2β = π`, `α/π ∉ ℚ`.  Suppose

* (**M**) some tile `i` of `D` is the march's `BG` tile on the letter `[t, t + f]` (as a vertex
  set), and
* (**the base word**) the next letter is an `a`: some tile `j` has an edge `[t + f, t + 2f]` on
  the base,

with `0 < t` and `t + 2f ≤ L`.  Then

1. tile `j` is the `BG` tile on `[t + f, t + 2f]`, and
2. the junction `(t + f, 0)` is covered by exactly one further tile `l`, and `l` is the flush
   filler or the offset filler at `t` — the two chiralities, and nothing else.

Every hypothesis is satisfiable (`junction_step_config_in_target`, `junction_step_f3`); no
hypothesis is about the search. -/
theorem junction_step {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {t : ℝ} (ht : 0 < t) (htL : t + 2 * f ≤ baseLen 1 f) {i j : Fin N}
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG t f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt (t + f) 0) (hm : (D.tile j).pts m = mkPt (t + f + f) 0) :
    Set.range (D.tile j).pts = Set.range (aTileBG (t + f) f (by linarith)).pts ∧
    ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt (t + f) 0) = α ∧
      (∀ l', (D.tile l').localAngle (mkPt (t + f) 0) = α → l' = l) ∧
      (Set.range (D.tile l).pts = Set.range (flushFiller t f (by linarith)).pts ∨
       Set.range (D.tile l).pts = Set.range (offsetFiller t f (by linarith)).pts) := by
  have hf1 : 1 < f := by linarith
  have hij : i ≠ j := next_letter_ne D.toDissection hf1 hA hm
  have hA' : Set.range (D.tile i).pts = Set.range (aTileBG (t + f - f) f hf1).pts := by
    rw [show t + f - f = t by ring]; exact hA
  have hB : Set.range (D.tile j).pts = Set.range (aTileBG (t + f) f hf1).pts :=
    a_letter_after_bg D hf htgt hM hij hA' hkm hk hm
  refine ⟨hB, ?_⟩
  obtain ⟨l, hli, hlj, hl, huniq⟩ := junction_alpha_tile D hf htgt hM hα hβpos hαβ hγdef hrel hirr
    (by linarith) (by linarith) hA' hB
  refine ⟨l, hli, hlj, hl, huniq, ?_⟩
  have := alpha_tile_is_filler D hf htgt hM hα hβpos hαβ hγdef hrel hli hlj hA' hB hl
  rwa [show t + f - f = t by ring] at this

/-! ## 12. The induction along an `a`-run -/

/-- **An `a`-run laid on the base**: for each `j < n`, some tile of `D` has the edge
`[t + jf, t + (j+1)f]` on the base.  This is the base-word hypothesis restricted to a run. -/
def LaysARun {N : ℕ} (D : CongruentDissection N) (f t : ℝ) (n : ℕ) : Prop :=
  ∀ j, j < n → ∃ (i : Fin N) (k m : Fin 3), k ≠ m ∧
    (D.tile i).pts k = mkPt (t + j * f) 0 ∧ (D.tile i).pts m = mkPt (t + j * f + f) 0

/-- **The march condition `M_k`**: every letter `j ≤ k` of the run is laid by the `BG` tile, and
every junction `1 … k` carries a chirality filler. -/
def MarchUpTo {N : ℕ} (D : CongruentDissection N) (f : ℝ) (hf : 1 < f) (t : ℝ) (k : ℕ) : Prop :=
  (∀ j, j ≤ k → ∃ i, Set.range (D.tile i).pts = Set.range (aTileBG (t + j * f) f hf).pts) ∧
  (∀ j, j < k → ∃ l, Set.range (D.tile l).pts = Set.range (flushFiller (t + j * f) f hf).pts ∨
    Set.range (D.tile l).pts = Set.range (offsetFiller (t + j * f) f hf).pts)

/-- **`M_k → M_{k+1}`**, given that letter `k + 1` is an `a`. -/
theorem march_step {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {t : ℝ} (ht : 0 < t) {k : ℕ} (hkL : t + (k + 2) * f ≤ baseLen 1 f)
    (hrun : ∃ (i : Fin N) (k' m : Fin 3), k' ≠ m ∧
      (D.tile i).pts k' = mkPt (t + (k + 1) * f) 0 ∧
      (D.tile i).pts m = mkPt (t + (k + 1) * f + f) 0)
    (hMk : MarchUpTo D f (by linarith) t k) : MarchUpTo D f (by linarith) t (k + 1) := by
  obtain ⟨i, hi⟩ := hMk.1 k le_rfl
  obtain ⟨j, k', m, hk'm, hk', hm⟩ := hrun
  have hk'' : (D.tile j).pts k' = mkPt (t + k * f + f) 0 := by rw [hk']; congr 1; ring
  have hm' : (D.tile j).pts m = mkPt (t + k * f + f + f) 0 := by rw [hm]; congr 1; ring
  obtain ⟨hB, l, -, -, -, -, hl⟩ := junction_step D hf htgt hM hα hβpos hαβ hγdef hrel hirr
    (t := t + k * f) (by positivity) (by linarith) hi hk'm hk'' hm'
  refine ⟨fun j' hj' => ?_, fun j' hj' => ?_⟩
  · rcases Nat.lt_or_ge j' (k + 1) with h | h
    · exact hMk.1 j' (by omega)
    · have : j' = k + 1 := by omega
      subst this
      exact ⟨j, by rw [hB]; congr 3; push_cast; ring⟩
  · rcases Nat.lt_or_ge j' k with h | h
    · exact hMk.2 j' h
    · have : j' = k := by omega
      subst this
      exact ⟨l, hl⟩

/-- **THE RUN INDUCTION.**  If the letters `[t + jf, t + (j+1)f]`, `j < n`, are all `a` (the run is
laid), the first of them is laid `BG` (**the base case `M_0`**), `0 < t` and `t + nf ≤ L`, then
every letter of the run is laid `BG` and every interior junction carries a flush or offset
filler: `M_{n-1}`.  Conditional on nothing but the base case and the bundle. -/
theorem run_rigid {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hnL : t + n * f ≤ baseLen 1 f)
    (hrun : LaysARun D f t n)
    (hbase : ∃ i, Set.range (D.tile i).pts = Set.range (aTileBG t f (by linarith)).pts) :
    ∀ k, k + 1 ≤ n → MarchUpTo D f (by linarith) t k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun j hj => ?_, fun j hj => absurd hj (by omega)⟩
    have : j = 0 := by omega
    subst this
    obtain ⟨i, hi⟩ := hbase
    exact ⟨i, by rw [hi]; congr 3; ring⟩
  | succ k ih =>
    intro hk
    have hf0 : (0:ℝ) < f := by linarith
    have hkn : ((k : ℝ) + 2) ≤ n := by exact_mod_cast (by omega : k + 2 ≤ n)
    refine march_step D hf htgt hM hα hβpos hαβ hγdef hrel hirr ht (k := k) ?_ ?_ (ih (by omega))
    · nlinarith
    · obtain ⟨i, k', m, hk'm, hk', hm⟩ := hrun (k + 1) (by omega)
      exact ⟨i, k', m, hk'm, by rw [hk']; congr 3; push_cast; ring,
        by rw [hm]; congr 3; push_cast; ring⟩

/-! ## 13. The far corner, in vertex-set form, and the first letter -/

/-- **The far-corner kill.**  If the march's `BG` tile sits on the third-to-last letter
`[L − 3f, L − 2f]` and the second-to-last letter is an `a`, no dissection exists: the tile laying
it is forced `BG` (`a_letter_after_bg`) and its apex `(L − 2f + dBG, h)` lies outside the target
(`MarchKills.bg_apex_second_to_last_outside`).  Vertex-set form of `MarchKills.far_corner_kill`,
with the `GB` half discharged by the junction analysis rather than assumed. -/
theorem far_corner_kill' {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {i j : Fin N}
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG (baseLen 1 f - 3 * f) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt (baseLen 1 f - 2 * f) 0)
    (hm : (D.tile j).pts m = mkPt (baseLen 1 f - 2 * f + f) 0) : False := by
  have hf1 : 1 < f := by linarith
  have hA' : Set.range (D.tile i).pts
      = Set.range (aTileBG (baseLen 1 f - 2 * f - f) f hf1).pts := by
    rw [show baseLen 1 f - 2 * f - f = baseLen 1 f - 3 * f by ring]; exact hA
  have hij : i ≠ j := by
    refine ne_of_vertex D.toDissection hA hm ?_
    rw [range_aTileBG]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    have hpos := apexH_pos hf1
    exact ⟨mkPt_ne_of_fst (by linarith), mkPt_ne_of_fst (by linarith), mkPt_ne_of_snd hpos.ne⟩
  have hB := a_letter_after_bg D hf htgt hM hij hA' hkm hk hm
  obtain ⟨n, hn⟩ := mem_range_of_eq hB (by rw [range_aTileBG]; right; right; rfl)
  have hmem := pts_mem_target D.toDissection j n
  rw [hn, htgt] at hmem
  exact bg_apex_second_to_last_outside hf1 hmem

/-- **The first letter, if it is an `a`, is laid `BG`**: the `GB` apex `(dGB, h)` has `dGB < 0`,
outside the target.  This is the base case `M_0` for every base word beginning with `a`. -/
theorem first_letter_bg {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {j : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt 0 0) (hm : (D.tile j).pts m = mkPt (0 + f) 0) :
    Set.range (D.tile j).pts = Set.range (aTileBG 0 f (by linarith)).pts := by
  have hf1 : 1 < f := by linarith
  rcases a_letter_tile D hf htgt hM hkm hk hm with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := mem_range_of_eq h (by rw [range_aTileGB]; right; right; rfl)
    have hmem := pts_mem_target D.toDissection j n
    rw [hn, htgt] at hmem
    have := leftFunctional_carrier one_pos hf1 _ hmem
    simp only [mkPt_zero, mkPt_one, zero_add] at this
    have hH := height_pos one_pos hf1
    have hL := baseLen_pos one_pos hf1
    have hpos := apexH_pos hf1
    have hneg : dGB f < 0 := (bg_then_gb_straddles f hf1).2.1
    nlinarith [mul_pos hL hpos]

/-- **The offset chirality is impossible at the corner junction.**  The offset filler at `t = 0`
has its overshoot vertex `(f + (c/b)(dBG − f), (c/b)h)` outside the target: its left-side
functional is `−f·H/(f² − 1) < 0`. -/
theorem offset_at_corner_junction_outside {f : ℝ} (hf : 1 < f) :
    (offsetFiller 0 f hf).pts 2 ∉ (baseBetaTarget 1 f one_pos hf).carrier := by
  intro hmem
  have := leftFunctional_carrier one_pos hf _ hmem
  simp only [offsetFiller, mkTri_pts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    mkPt_zero, mkPt_one, zero_add] at this
  have hH := height_pos one_pos hf
  have hf0 : (0:ℝ) < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hL' := baseLen_one f
  have e : (f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) * height 1 f
      - baseLen 1 f / 2 * (f ^ 2 / (f ^ 2 - 1) * apexH f) = -(f / (f ^ 2 - 1)) * height 1 f := by
    unfold apexH dBG; rw [hL']; field_simp; ring
  rw [e] at this
  have : 0 < f / (f ^ 2 - 1) * height 1 f := by positivity
  linarith

/-- **At the corner junction only the flush chirality survives.**  With the corner tile laying
`a` on `[0, f]` and the second letter an `a`, the junction `(f, 0)` is covered by the flush filler
`flushFiller 0 f` — the offset one has a vertex outside the target. -/
theorem corner_junction_flush {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hL : 2 * f ≤ baseLen 1 f)
    {i j : Fin N}
    (hA : Set.range (D.tile i).pts = Set.range (aTileBG 0 f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt (0 + f) 0) (hm : (D.tile j).pts m = mkPt (0 + f + f) 0) :
    ∃ l : Fin N, Set.range (D.tile l).pts = Set.range (flushFiller 0 f (by linarith)).pts := by
  have hf1 : 1 < f := by linarith
  -- the junction step needs `0 < t`; at `t = 0` the junction `(f, 0)` is still a base point and
  -- the left tile still presents `γ` there, so the argument goes through verbatim with `x₀ = f`
  have hij : i ≠ j := next_letter_ne D.toDissection hf1 hA hm
  have hA' : Set.range (D.tile i).pts = Set.range (aTileBG (0 + f - f) f hf1).pts := by
    rw [show (0:ℝ) + f - f = 0 by ring]; exact hA
  have hB : Set.range (D.tile j).pts = Set.range (aTileBG (0 + f) f hf1).pts :=
    a_letter_after_bg D hf htgt hM hij hA' hkm hk hm
  obtain ⟨l, hli, hlj, hl, -⟩ := junction_alpha_tile D hf htgt hM hα hβpos hαβ hγdef hrel hirr
    (by linarith) (by linarith) hA' hB
  rcases alpha_tile_is_filler D hf htgt hM hα hβpos hαβ hγdef hrel hli hlj hA' hB hl with h | h
  · exact ⟨l, by rw [h, show (0:ℝ) + f - f = 0 by ring]⟩
  · exfalso
    rw [show (0:ℝ) + f - f = 0 by ring] at h
    obtain ⟨n, hn⟩ := mem_range_of_eq h ⟨2, rfl⟩
    have hmem := pts_mem_target D.toDissection l n
    rw [hn, htgt] at hmem
    exact offset_at_corner_junction_outside hf1 hmem

/-! ## 14. Non-vacuity: the configurations the hypotheses name exist inside the target -/

/-- **A whole block, in either chirality, lies in the target** for `f/(f²−1) ≤ t` and
`t + f + 2·dBG ≤ L`.  So the tiles named by the hypotheses and conclusion of `junction_step`
(`aTileBG t`, `aTileBG (t + f)`, `flushFiller t` / `offsetFiller t`) are actual placements
inside `baseBetaTarget 1 f`; what is not exhibited — and cannot be, the theorem being that none
exists — is a dissection extending them. -/
theorem block_subset_target {f : ℝ} (hf : 2 ≤ f) {t : ℝ} (ht : f / (f ^ 2 - 1) ≤ t)
    (hL : t + f + 2 * dBG f ≤ baseLen 1 f) (b : Bool) :
    ∀ T ∈ block t f (by linarith) b, T.carrier ⊆ (baseBetaTarget 1 f one_pos (by linarith)).carrier := by
  intro T hT
  refine marchConfig_subset_target hf ht 1 (fun _ => b) (by simpa using hL) T ⟨0, by omega, ?_⟩
  simpa using hT

/-- **The configuration at `f = 3`, `t = 1`, blocks `0` and `1`, in numbers.**  Tile `(3, 8, 9)`,
`L = 26`, `dBG = 13/3`, `h = apexH 3 = 4√35/3`.  Block `0`: `a`-tiles on `[1,4]`, `[4,7]` with
apexes `(16/3, h)`, `(25/3, h)`; the flush filler `(4,0), (25/3, h), (16/3, h)`; the offset filler
`(4,0), (212/27, 8h/9), (11/2, 9h/8)`, whose third vertex attains the strip height
`overshootH 3 = 9h/8`.  Block `1` is block `0` translated by `(3, 0)`.  The containment hypotheses
of `marchConfig_subset_target` hold for `k = 2`: `3/8 ≤ 1` and `1 + 6 + 26/3 ≤ 26`. -/
theorem config_f3 :
    dBG 3 = 13 / 3 ∧ baseLen 1 3 = 26 ∧ overshootH 3 = 9 / 8 * apexH 3 ∧
    (aTileBG 1 3 (by norm_num)).pts 0 = mkPt 4 0 ∧
    (aTileBG 1 3 (by norm_num)).pts 1 = mkPt 1 0 ∧
    (aTileBG 1 3 (by norm_num)).pts 2 = mkPt (16 / 3) (apexH 3) ∧
    (aTileBG (1 + 3) 3 (by norm_num)).pts 2 = mkPt (25 / 3) (apexH 3) ∧
    (flushFiller 1 3 (by norm_num)).pts 0 = mkPt 4 0 ∧
    (flushFiller 1 3 (by norm_num)).pts 1 = mkPt (25 / 3) (apexH 3) ∧
    (flushFiller 1 3 (by norm_num)).pts 2 = mkPt (16 / 3) (apexH 3) ∧
    (offsetFiller 1 3 (by norm_num)).pts 1 = mkPt (212 / 27) (8 / 9 * apexH 3) ∧
    (offsetFiller 1 3 (by norm_num)).pts 2 = mkPt (11 / 2) (9 / 8 * apexH 3) ∧
    (3 : ℝ) / (3 ^ 2 - 1) ≤ 1 ∧ (1 : ℝ) + 2 * 3 + 2 * dBG 3 ≤ baseLen 1 3 ∧
    block (1 + 3) 3 (by norm_num) true
      = translateTri (mkPt 3 0) '' block 1 3 (by norm_num) true := by
  have hd : dBG 3 = 13 / 3 := by unfold dBG; norm_num
  have hL : baseLen 1 3 = 26 := by rw [baseLen_one]; norm_num
  refine ⟨hd, hL, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num, ?_, ?_⟩
  · unfold overshootH; norm_num
  · show mkPt (1 + 3) 0 = _; norm_num
  · show mkPt (1 + dBG 3) (apexH 3) = _; rw [hd]; norm_num
  · show mkPt (1 + 3 + dBG 3) (apexH 3) = _; rw [hd]; norm_num
  · show mkPt (1 + 3) 0 = _; norm_num
  · show mkPt (1 + 3 + dBG 3) (apexH 3) = _; rw [hd]; norm_num
  · show mkPt (1 + dBG 3) (apexH 3) = _; rw [hd]; norm_num
  · show mkPt (1 + 3 + (3 ^ 2 - 1) / 3 ^ 2 * dBG 3) ((3 ^ 2 - 1) / 3 ^ 2 * apexH 3) = _
    rw [hd]; norm_num
  · show mkPt (1 + 3 + 3 ^ 2 / (3 ^ 2 - 1) * (dBG 3 - 3)) (3 ^ 2 / (3 ^ 2 - 1) * apexH 3) = _
    rw [hd]; norm_num
  · rw [hd, hL]; norm_num
  · exact block_translate 1 3 3 (by norm_num) true

/-- **The junction-step hypotheses at `f = 3`, `t = 1`, in numbers**: `0 < 1`, `1 + 2·3 ≤ 26`,
and the angle bundle is inhabited by the model angles (`MarchKillsFan.angle_bundle_nonvacuous_f3`).
-/
theorem junction_step_hyps_f3 :
    (0 : ℝ) < 1 ∧ (1 : ℝ) + 2 * 3 ≤ baseLen 1 3 ∧
    ∃ α β γ : ℝ, γ = 2 * α + β ∧ 3 * α + 2 * β = Real.pi ∧
      (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ 0 < α ∧ α < β := by
  refine ⟨one_pos, ?_, angle_bundle_nonvacuous_f3⟩
  rw [baseLen_one]; norm_num

/-! ## 15. Axiom audit -/

#print axioms block_translate
#print axioms marchConfig_translate
#print axioms marchConfig_add
#print axioms marchConfig_confined
#print axioms marchConfig_subset_target
#print axioms combo_dies_pts
#print axioms gb_after_bg_dies
#print axioms a_letter_tile
#print axioms a_letter_after_bg
#print axioms junction_alpha_tile
#print axioms alpha_corner_data
#print axioms edge_in_wedge
#print axioms gram_extremal
#print axioms wedge_extremal_coords
#print axioms alpha_tile_is_filler
#print axioms junction_step
#print axioms march_step
#print axioms run_rigid
#print axioms far_corner_kill'
#print axioms first_letter_bg
#print axioms offset_at_corner_junction_outside
#print axioms corner_junction_flush
#print axioms block_subset_target
#print axioms config_f3

end Erdos634.MarchInduction
