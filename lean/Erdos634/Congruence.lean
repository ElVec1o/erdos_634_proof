import Erdos634.Dissection

/-!
# The congruence layer

`Dissection N` carries `tile : Fin N → Tri` with **no constraint that the tiles are
congruent copies of one tile** — `volume_target_of_congruent` takes equal area as a
hypothesis instead.  That omission is why `StripRigid` records its blocker as needing "a
formalization of tilings that this project does not have": the predicate its
`layer_induction` schema quantifies over, *"tile `j` is unreflected"*, could not even be
**stated**, because "unreflected" means "direct isometry image of the tile" and no isometry
was in the picture.

This file supplies the missing layer, on top of what `Dissection` already has.  Nothing
here is new geometry; it is the connective tissue.

* `Tri.sideSq` — squared side lengths.
* `Tri.Congruent` — an isometry of the plane carrying vertices to vertices, up to a
  permutation.  An equivalence relation (`Congruent.refl/symm/trans`), and it preserves all
  pairwise distances with a single permutation (`Congruent.dist_eq`) — the SSS content, and
  the bridge to the `congOK` side-multiset test that `Tiling28`/`44`/`77`/`99` already use
  in their bespoke `ℤ[√d]` certificates.
* `Tri.Unreflected` / `Tri.Reflected` — orientation agreement with a model tile, via the
  sign of `Tri.det`.  These are a genuine dichotomy (`unreflected_or_reflected`) with no
  extra hypothesis, because `Dissection` already proves `Tri.det_ne_zero`.
* `CongruentDissection` — a dissection all of whose tiles are congruent to a model.
* `layer_all_unreflected` — `StripRigid.layer_induction`, now instantiated at the actual
  geometric predicate rather than at an abstract `U : ℕ → Prop`.

## What this does and does not unblock

It makes the predicate stateable, so `StripRigid`'s two pointwise exclusions can be aimed
at something real.  It does **not** discharge those exclusions' geometric content, and it
does not by itself assemble the fan facts.  (An earlier version of this paragraph cited
`Dissection` lines 396–402 as an open gap — "Mathlib cannot lift a mod-`2π` angle sum to a
real-valued one".  That is **stale**: `HasAngleSums` was discharged on 2026-08-16 by
`Dissection.hasAngleSums`, via the area route in `VertexSector.lean`, which sidesteps the
mod-`2π` lift entirely.  Corrected here.)  Fan arguments — which is what `prop:a2branch` is,
end to end — are carried here as hypotheses, in the style of `Dissection.HasAngleSums`; note
that carrying one of those predicates now means carrying a *provable* fact, not an open one.
Reach 4 is not closed by this file.
-/

namespace Erdos634.Geometry

/-- The squared length of edge `k`, from `pts k` to `pts (k+1)`. -/
noncomputable def Tri.sideSq (T : Tri) (k : Fin 3) : ℝ :=
  dist (T.pts k) (T.pts (k + 1)) ^ 2

/-- **Congruence**: an isometry of the plane carrying the vertices of `T` onto those of `U`,
up to a relabelling of the three vertices. -/
def Tri.Congruent (T U : Tri) : Prop :=
  ∃ (f : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3)), ∀ k, f (T.pts k) = U.pts (σ k)

theorem Tri.Congruent.refl (T : Tri) : T.Congruent T := by
  refine ⟨IsometryEquiv.refl Plane, Equiv.refl _, fun k => ?_⟩
  simp [IsometryEquiv.refl]

theorem Tri.Congruent.symm {T U : Tri} (h : T.Congruent U) : U.Congruent T := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨f.symm, σ.symm, fun k => ?_⟩
  have hk := hf (σ.symm k)
  rw [Equiv.apply_symm_apply] at hk
  rw [← hk, IsometryEquiv.symm_apply_apply]

theorem Tri.Congruent.trans {T U V : Tri} (h₁ : T.Congruent U) (h₂ : U.Congruent V) :
    T.Congruent V := by
  obtain ⟨f, σ, hf⟩ := h₁
  obtain ⟨g, τ, hg⟩ := h₂
  exact ⟨f.trans g, σ.trans τ, fun k => by simp [hf k, hg (σ k)]⟩

/-- **Congruence is SSS.**  A single permutation of the vertices matches *every* pairwise
distance, hence in particular the three side lengths.  This is the bridge to the squared
side-multiset test `congOK` used by the explicit `Tiling28/44/77/99` certificates. -/
theorem Tri.Congruent.dist_eq {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts (σ i)) (U.pts (σ j)) := by
  obtain ⟨f, σ, hf⟩ := h
  exact ⟨σ, fun i j => by rw [← hf i, ← hf j, f.dist_eq]⟩

/-- The tile is positively oriented. -/
def Tri.Pos (T : Tri) : Prop := 0 < T.det

/-- **Orientation is a strict dichotomy**, with no nondegeneracy hypothesis needed:
`Dissection` already proves `Tri.det_ne_zero`. -/
theorem Tri.det_pos_or_neg (T : Tri) : 0 < T.det ∨ T.det < 0 :=
  (lt_or_gt_of_ne T.det_ne_zero).symm

/-- `T` has the same orientation as the model. -/
def Tri.Unreflected (T model : Tri) : Prop := (0 < T.det) ↔ (0 < model.det)

/-- `T` has the opposite orientation to the model. -/
def Tri.Reflected (T model : Tri) : Prop := (0 < T.det) ↔ (model.det < 0)

/-- **Every tile is unreflected or reflected.**  This is the dichotomy `rem:straddler`'s
"exactly two label assignments" lives in, and `StripRigid`'s exclusions rule out one side of
it. -/
theorem Tri.unreflected_or_reflected (T model : Tri) : T.Unreflected model ∨ T.Reflected model := by
  rcases T.det_pos_or_neg with hT | hT <;> rcases model.det_pos_or_neg with hm | hm
  · exact Or.inl ⟨fun _ => hm, fun _ => hT⟩
  · exact Or.inr ⟨fun _ => hm, fun _ => hT⟩
  · exact Or.inr ⟨fun h => absurd h (asymm hT), fun h => absurd h (asymm hm)⟩
  · exact Or.inl ⟨fun h => absurd h (asymm hT), fun h => absurd h (asymm hm)⟩

/-- **A dissection into congruent copies of one tile.**  This is the structure the problem
is actually about, and the one `Dissection` alone does not express. -/
structure CongruentDissection (N : ℕ) extends Dissection N where
  /-- The tile every piece is a copy of. -/
  model : Tri
  /-- Every piece is congruent to it. -/
  tiles_congruent : ∀ i, (tile i).Congruent model

namespace CongruentDissection

variable {N : ℕ}

/-- The predicate `StripRigid.layer_induction` is meant to quantify over. -/
def UnreflectedAt (D : CongruentDissection N) (i : Fin N) : Prop :=
  (D.tile i).Unreflected D.model

/-- Each tile is unreflected or reflected — the dichotomy, now stated about an actual
dissection into congruent copies. -/
theorem unreflected_or_reflected (D : CongruentDissection N) (i : Fin N) :
    D.UnreflectedAt i ∨ (D.tile i).Reflected D.model :=
  Tri.unreflected_or_reflected _ _

/-- **The link, now stateable.**  `StripRigid.layer_induction` instantiated at the real
geometric predicate along an indexing of a layer: if the first tile of the layer is
unreflected and an unreflected tile forces its successor to be, every tile of the layer is
unreflected.

`StripRigid` proves the two pointwise exclusions that are meant to supply `base` and `step`;
supplying them *from* those exclusions is geometric work this file does not do. -/
theorem layer_all_unreflected (D : CongruentDissection N) (idx : ℕ → Fin N)
    (base : D.UnreflectedAt (idx 0))
    (step : ∀ j, D.UnreflectedAt (idx j) → D.UnreflectedAt (idx (j + 1))) :
    ∀ j, D.UnreflectedAt (idx j) :=
  fun j => Nat.rec base step j

end CongruentDissection

end Erdos634.Geometry
