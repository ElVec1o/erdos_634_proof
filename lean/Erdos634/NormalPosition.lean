import Erdos634.Ladder
import Erdos634.RouteOneBoundaryA

/-!
# Normal position: a dissection whose target is *congruent* to the model can be moved onto it

Written 2026-09-11, directly after `RouteOneBoundaryA.lean`, whose closing note names two
remaining hypotheses of `flank_at_route1uniform`.  This file discharges the second of them —
**normal position**, `htgt : D.target = baseBetaTarget e f` — as a genuine reduction.  It does
**not** touch the first (`hwall`), which is the open content of Route 1 (`rem:routeoneopen`).

## The obstruction, precisely

`Tri.Congruent` is congruence under an *arbitrary* isometry **and an arbitrary relabelling of the
three vertices** (`Congruence.lean`: `∃ (f : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3)), ∀ k,
f (T.pts k) = U.pts (σ k)`).  A real base-`β` dissection has a target that is congruent to
`baseBetaTarget e f`, never literally equal to it.  Two separate mismatches must be removed:

1. the **isometry** — handled by `DissectionMap.mapDissection` along `Ladder.isoAff f`
   (Mazur–Ulam makes the isometry affine), which is already in the corpus and is reused verbatim
   rather than rebuilt;
2. the **permutation** — *not* handled by anything in the corpus.  `mapTri (isoAff f) T` has
   `pts = f ∘ T.pts = U.pts ∘ σ`, which is `U` only up to relabelling, and `Tri` is a structure
   whose `pts` field is a function, so `mapTri (isoAff f) T = U` is **false** in general.
   `Ladder.ladder`, the one existing consumer of this pattern, sidesteps it by only ever needing
   *carrier* equality (`CongruentArea.image_carrier_of_congruent`); a hypothesis of the form
   `D.target = baseBetaTarget e f` needs equality of the structure.

The fix for (2) is `relabelTri`/`relabelTarget`: permuting a triangle's vertices leaves its carrier
alone (`Set.range` is insensitive to precomposition with an equiv), so it leaves `Dissection`'s two
fields alone; pre-composing with `σ⁻¹` and *then* transporting lands on `U.pts` on the nose.

## What is proved

* `relabelTri`, `relabelTri_carrier`, `relabelTarget` — vertex relabelling of the target of a
  dissection, a `Dissection` again.
* `mapTri_relabel_eq` — the placement identity: `mapTri (isoAff f) (relabelTri T σ⁻¹) = U`, an
  equality of `Tri`, from a congruence witness `(f, σ)`.
* `normalize` / `normalizeC` — the transported `Dissection` / `CongruentDissection`, with
  `normalize_target : (normalize D f σ).target = M` and `normalize_tile` (`rfl`).  `normalizeC`
  keeps the **same model tile**: the tile shape is not disturbed, so a base-`β` dissection stays a
  base-`β` dissection.
* `exists_normal_position` — the reduction as a bare existence statement.
* `flank_at_route1uniform_of_congruent` — **the composition.**  For a dissection `D` whose target
  is merely *congruent* to `baseBetaTarget e f`, with the congruence's own isometry `g`, all of
  `RouteOneBoundaryA.flank_at_route1uniform`'s hypotheses stated for `D`'s **own** tiles read
  through `g`, the conclusion is a statement about `D`'s own tiles: some tile of `D` has a vertex
  that `g` sends to `V`, with an edge there that `g` sends to a horizontal rightward one.
  `htgt` does not appear.

## What is **not** claimed

Not one of the three `/goal` outcomes.  `conj:advance` remains CONJECTURE, `e = 1` is not closed,
`e ≥ 2` is untouched, the prime case is not advanced, no Rule 0 label moves, and **no base-`β`
dissection is exhibited** (none can be — that is the point of the argument).  In particular
`hwall` — the local wall — is completely untouched and remains an assumed statement about a
hypothetical tiling; everything here is a change of coordinates, and a change of coordinates
proves nothing about whether the configuration exists.

Two honest caveats about what "normal position" buys, in the spirit of `thm:ladder`'s lesson that
closing an infrastructure gap need not move its consumers:

* The `α`-tile bundle (`hjseg`, `habovej`, `hjleft`) is still **assumed**, and is still witnessed
  only at `Tri` level (`RouteOneWallOnly.alpha_tile_witness`), not at `Dissection` level.  This
  file does not produce it; it only lets it be stated about a general `D`.
* The conclusion is transported through `g`, not stated in `D`'s own frame.  That is not a
  weakness of the transport — `V` is a point of the *model*, so "which point of `D`" is exactly
  `g⁻¹ V`, and the statement says so — but it does mean the conclusion is only as concrete as the
  placement `g` is.
* **Orientation is not preserved, and that is a real limitation to name rather than hide.**  The
  congruence's isometry `g` may be orientation-reversing, and the relabelling `σ` may be odd, so
  `normalize` can flip the sign of `Tri.det` on the target and on every tile.  `Tri.Congruent` and
  hence `normalizeC`'s `tiles_congruent` are indifferent to this, but `Tri.Unreflected` /
  `Tri.Reflected` (`Congruence.lean`) are **not**: a consumer that assumes a particular chirality
  of the tiles — `StripRigid`'s layer predicate, say — cannot be composed with `normalize` without
  first deciding the sign.  All tiles flip together, so the damage is a single global bit, but the
  bit is not fixed here.  Nothing in Route 1's flank chain uses it, which is why the composition
  below goes through; this is flagged because a *different* consumer of normal position would hit
  it immediately.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.NormalPosition

open Erdos634.Geometry Erdos634.DissectionMap Erdos634.Ladder
open Erdos634.CertCoord Erdos634.BaseBetaTargetCoord

/-! ## 1. `Tri` equality is `pts` equality -/

/-- `Tri`'s second field is a `Prop`, so two triangles with the same vertex map are equal. -/
theorem tri_eq_of_pts {T U : Tri} (h : T.pts = U.pts) : T = U := by
  cases T; cases U; cases h; rfl

/-! ## 2. Relabelling the vertices -/

/-- **Relabelling a triangle's vertices.**  `(relabelTri T σ).pts = T.pts ∘ σ`. -/
noncomputable def relabelTri (T : Tri) (σ : Equiv.Perm (Fin 3)) : Tri where
  pts := T.pts ∘ σ
  indep := T.indep.comp_embedding σ.toEmbedding

@[simp] theorem relabelTri_pts (T : Tri) (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelTri T σ).pts k = T.pts (σ k) := rfl

/-- **Relabelling does not move the triangle.**  `Set.range` is insensitive to precomposition with
an equivalence, and `carrier` is the convex hull of the range. -/
@[simp] theorem relabelTri_carrier (T : Tri) (σ : Equiv.Perm (Fin 3)) :
    (relabelTri T σ).carrier = T.carrier := by
  simp only [Tri.carrier, relabelTri]
  rw [Set.range_comp, σ.surjective.range_eq, Set.image_univ]

/-- **Relabelling the target of a dissection.**  Both `Dissection` fields see only carriers, so
this is a `Dissection` with the *same* tiles. -/
noncomputable def relabelTarget {N : ℕ} (D : Dissection N) (σ : Equiv.Perm (Fin 3)) :
    Dissection N where
  target := relabelTri D.target σ
  tile := D.tile
  covers := by rw [D.covers, relabelTri_carrier]
  interiors_disjoint := D.interiors_disjoint

@[simp] theorem relabelTarget_tile {N : ℕ} (D : Dissection N) (σ : Equiv.Perm (Fin 3))
    (i : Fin N) : (relabelTarget D σ).tile i = D.tile i := rfl

@[simp] theorem relabelTarget_target {N : ℕ} (D : Dissection N) (σ : Equiv.Perm (Fin 3)) :
    (relabelTarget D σ).target = relabelTri D.target σ := rfl

/-! ## 3. The placement identity -/

/-- **The placement identity.**  Given a congruence witness `(f, σ)` from `T` to `U` — an isometry
`f` and a vertex relabelling `σ` with `f (T.pts k) = U.pts (σ k)` — relabelling `T` by `σ⁻¹` and
then transporting along `f` gives `U` **literally**, as an equality of `Tri`.

This is the step `Tri.Congruent` does not give on its own: a congruence yields an isometry onto `U`
only up to the permutation, and `Ladder.ladder`, the corpus's one existing consumer, needs only
carrier equality, so nothing in the corpus produced this. -/
theorem mapTri_relabel_eq {T U : Tri} {f : Plane ≃ᵢ Plane} {σ : Equiv.Perm (Fin 3)}
    (hf : ∀ k, f (T.pts k) = U.pts (σ k)) :
    mapTri (isoAff f) (relabelTri T σ.symm) = U := by
  refine tri_eq_of_pts (funext fun k => ?_)
  show f (T.pts (σ.symm k)) = U.pts k
  rw [hf (σ.symm k), Equiv.apply_symm_apply]

/-! ## 4. Normal position -/

/-- **A dissection placed in normal position.**  Relabel the target by `σ⁻¹`, then transport
everything along the congruence's isometry. -/
noncomputable def normalize {N : ℕ} (D : Dissection N) (f : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) : Dissection N :=
  mapDissection (isoAff f) (relabelTarget D σ.symm)

@[simp] theorem normalize_tile {N : ℕ} (D : Dissection N) (f : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) (i : Fin N) :
    (normalize D f σ).tile i = mapTri (isoAff f) (D.tile i) := rfl

/-- **The target is the model, on the nose.** -/
theorem normalize_target {N : ℕ} (D : Dissection N) {U : Tri} {f : Plane ≃ᵢ Plane}
    {σ : Equiv.Perm (Fin 3)} (hf : ∀ k, f (D.target.pts k) = U.pts (σ k)) :
    (normalize D f σ).target = U :=
  mapTri_relabel_eq hf

/-- The vertices of a placed tile are the images of the original's. -/
@[simp] theorem normalize_tile_pts {N : ℕ} (D : Dissection N) (f : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) (i : Fin N) (m : Fin 3) :
    ((normalize D f σ).tile i).pts m = f ((D.tile i).pts m) := rfl

/-- The carrier of a placed tile is the image of the original's. -/
theorem normalize_tile_carrier {N : ℕ} (D : Dissection N) (f : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) (i : Fin N) :
    ((normalize D f σ).tile i).carrier = f '' (D.tile i).carrier := by
  rw [normalize_tile, mapTri_carrier]; rfl

/-- **A `CongruentDissection` placed in normal position, with the same model tile.**  The tile
shape is untouched, so a dissection into copies of `t` stays a dissection into copies of `t`; only
the ambient placement changes. -/
noncomputable def normalizeC {N : ℕ} (D : CongruentDissection N) (f : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) : CongruentDissection N where
  toDissection := normalize D.toDissection f σ
  model := D.model
  tiles_congruent := fun i =>
    (congruent_mapTri f (D.tile i)).symm.trans (D.tiles_congruent i)

@[simp] theorem normalizeC_model {N : ℕ} (D : CongruentDissection N) (f : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) : (normalizeC D f σ).model = D.model := rfl

@[simp] theorem normalizeC_toDissection {N : ℕ} (D : CongruentDissection N) (f : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) :
    (normalizeC D f σ).toDissection = normalize D.toDissection f σ := rfl

/-- **The reduction, as an existence statement.**  Any dissection whose target is *congruent* to
`U` is carried by an isometry of the plane to a dissection whose target *is* `U`, with each tile
the isometric image of the corresponding original tile. -/
theorem exists_normal_position {N : ℕ} (D : Dissection N) {U : Tri}
    (h : D.target.Congruent U) :
    ∃ (g : Plane ≃ᵢ Plane) (D' : Dissection N),
      D'.target = U ∧ ∀ i m, (D'.tile i).pts m = g ((D.tile i).pts m) := by
  obtain ⟨f, σ, hf⟩ := h
  exact ⟨f, normalize D f σ, normalize_target D hf, fun _ _ => rfl⟩

/-- The same for a `CongruentDissection`, keeping the model tile. -/
theorem exists_normal_position_congruent {N : ℕ} (D : CongruentDissection N) {U : Tri}
    (h : D.target.Congruent U) :
    ∃ (g : Plane ≃ᵢ Plane) (D' : CongruentDissection N),
      D'.target = U ∧ D'.model = D.model ∧
      ∀ i m, (D'.tile i).pts m = g ((D.tile i).pts m) := by
  obtain ⟨f, σ, hf⟩ := h
  exact ⟨f, normalizeC D f σ, normalize_target D.toDissection hf, rfl, fun _ _ => rfl⟩

/-! ## 5. The composition at `rem:route1uniform`, without normal position assumed -/

/-- **Route 1's flank at `rem:route1uniform`, for a dissection whose target is only *congruent* to
the base-`β` model.**

`g` is the congruence's isometry and `σ` its vertex relabelling (`hg`); every hypothesis is stated
for `D`'s **own** tiles, read through `g`, and so is the conclusion.  Compared with
`RouteOneBoundaryA.flank_at_route1uniform` the normal-position hypothesis
`htgt : D.target = baseBetaTarget e f` is **gone**, replaced by the congruence data that a real
base-`β` dissection actually supplies.

What is still assumed is exactly what was still assumed there: the `α`-tile's placement
(`hjseg`, `habovej`, `hjleft`) and the local wall `hwall`, the latter being the open content of
Route 1 (`rem:routeoneopen`, OPEN).  Nothing here bears on either. -/
theorem flank_at_route1uniform_of_congruent {N : ℕ} (D : Dissection N) {e f : ℝ}
    (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f)
    (g : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3))
    (hg : ∀ k, g (D.target.pts k) = (baseBetaTarget e f (by linarith) hef).pts (σ k))
    (j : Fin N) (mj : Fin 3)
    (hjseg : openSegment ℝ (mkPt (escapeV e f).1 (escapeV e f).2)
        (mkPt (sideA e f).1 (sideA e f).2)
      ⊆ openSegment ℝ (g ((D.tile j).pts (mj + 1))) (g ((D.tile j).pts (mj + 2))))
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier →
      0 ≤ (g q - mkPt (escapeV e f).1 (escapeV e f).2) 1)
    (hjleft : ∀ q : Plane, q ∈ (D.tile j).carrier →
      (g q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : Fin N,
      (∃ q : Plane, q ∈ (D.tile k).carrier ∧
        0 < (g q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ∧
        0 < (g q - mkPt (escapeV e f).1 (escapeV e f).2) 1 ∧
        dist (g q) (mkPt (escapeV e f).1 (escapeV e f).2) < ρ) →
      ∀ q : Plane, q ∈ (D.tile k).carrier →
        0 ≤ (g q - mkPt (escapeV e f).1 (escapeV e f).2) 1) :
    ∃ (i : Fin N) (m : Fin 3),
      g ((D.tile i).pts m) = mkPt (escapeV e f).1 (escapeV e f).2 ∧
      ((g ((D.tile i).pts (m + 1)) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < (g ((D.tile i).pts (m + 1)) - mkPt (escapeV e f).1 (escapeV e f).2) 0 ∨
       (g ((D.tile i).pts (m + 2)) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < (g ((D.tile i).pts (m + 2)) - mkPt (escapeV e f).1 (escapeV e f).2) 0) := by
  -- transport `D` into normal position; every hypothesis is the transported one, `rfl`-equal
  have hcar : ∀ k : Fin N, ((normalize D g σ).tile k).carrier = g '' (D.tile k).carrier :=
    fun k => normalize_tile_carrier D g σ k
  refine Erdos634.RouteOneBoundaryA.flank_at_route1uniform (normalize D g σ) he hef hf2
    (normalize_target D hg) j mj hjseg ?_ ?_ ?_
  · intro q hq
    rw [hcar] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact habovej p hp
  · intro q hq
    rw [hcar] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact hjleft p hp
  · obtain ⟨ρ, hρ, hw⟩ := hwall
    refine ⟨ρ, hρ, fun k hex q hq => ?_⟩
    obtain ⟨q₀, hq₀, h1, h2, h3⟩ := hex
    rw [hcar] at hq₀ hq
    obtain ⟨p₀, hp₀, rfl⟩ := hq₀
    obtain ⟨p, hp, rfl⟩ := hq
    exact hw k ⟨p₀, hp₀, h1, h2, h3⟩ p hp

/-! ## 6. Non-vacuity: the new statement *contains* the old one

The hypothesis bundle of `flank_at_route1uniform_of_congruent` is not stronger than the one it
replaces: taking `g = id`, `σ = id` recovers `RouteOneBoundaryA.flank_at_route1uniform` verbatim
from it.  So the added `hg` cannot have made the theorem vacuous — it is strictly weaker than the
`htgt` it replaced, and `exists_placement_data` says a `Tri.Congruent` target supplies it.

(This is the check `CLAUDE.md` requires and is all that is available here: the *whole* bundle's
satisfiability is not established, because it contains `hwall`, which is open, and no base-`β`
dissection is exhibited.  What is established is that this file adds no unsatisfiable hypothesis.)
-/

/-- The congruence data `hg` is exactly what `Tri.Congruent` provides — no extra content. -/
theorem exists_placement_data {N : ℕ} (D : Dissection N) {U : Tri} (h : D.target.Congruent U) :
    ∃ (g : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3)),
      ∀ k, g (D.target.pts k) = U.pts (σ k) := h

/-- **The generalisation is faithful**: `RouteOneBoundaryA.flank_at_route1uniform` is the
`g = id`, `σ = id` case of `flank_at_route1uniform_of_congruent`. -/
theorem flank_at_route1uniform_recovered {N : ℕ} (D : Dissection N) {e f : ℝ}
    (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f)
    (htgt : D.target = baseBetaTarget e f (by linarith) hef)
    (j : Fin N) (mj : Fin 3)
    (hjseg : openSegment ℝ (mkPt (escapeV e f).1 (escapeV e f).2)
        (mkPt (sideA e f).1 (sideA e f).2)
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier →
      0 ≤ (q - mkPt (escapeV e f).1 (escapeV e f).2) 1)
    (hjleft : ∀ q : Plane, q ∈ (D.tile j).carrier →
      (q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : Fin N,
      (∃ q : Plane, q ∈ (D.tile k).carrier ∧
        0 < (q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ∧
        0 < (q - mkPt (escapeV e f).1 (escapeV e f).2) 1 ∧
        dist q (mkPt (escapeV e f).1 (escapeV e f).2) < ρ) →
      ∀ q : Plane, q ∈ (D.tile k).carrier →
        0 ≤ (q - mkPt (escapeV e f).1 (escapeV e f).2) 1) :
    ∃ (i : Fin N) (m : Fin 3),
      (D.tile i).pts m = mkPt (escapeV e f).1 (escapeV e f).2 ∧
      ((((D.tile i).pts (m + 1) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < ((D.tile i).pts (m + 1) - mkPt (escapeV e f).1 (escapeV e f).2) 0) ∨
       (((D.tile i).pts (m + 2) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < ((D.tile i).pts (m + 2) - mkPt (escapeV e f).1 (escapeV e f).2) 0)) :=
  flank_at_route1uniform_of_congruent D he hef hf2 (IsometryEquiv.refl Plane) (Equiv.refl _)
    (fun k => by rw [htgt]; rfl) j mj hjseg habovej hjleft hwall

/-! ## 7. Axiom audit -/

#print axioms mapTri_relabel_eq
#print axioms normalize_target
#print axioms exists_normal_position
#print axioms exists_normal_position_congruent
#print axioms flank_at_route1uniform_of_congruent
#print axioms flank_at_route1uniform_recovered

end Erdos634.NormalPosition
