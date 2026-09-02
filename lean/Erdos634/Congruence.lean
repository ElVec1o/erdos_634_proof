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

/-- **Congruent triangles have the same side-length multiset.** The specific vertex
correspondence `σ` need not be known — for the bridge from "the corner tile is congruent to the
model" to "the corner tile's own edges have the model's side lengths" (`TilePlacement
.c_corner_side_a`'s `hmul` hypothesis), only the *unordered* set of three side lengths matters. -/
theorem Tri.Congruent.sideMultiset_eq {T U : Tri} (h : T.Congruent U) :
    ({dist (T.pts 0) (T.pts 1), dist (T.pts 2) (T.pts 0), dist (T.pts 1) (T.pts 2)} : Multiset ℝ)
    = {dist (U.pts 0) (U.pts 1), dist (U.pts 2) (U.pts 0), dist (U.pts 1) (U.pts 2)} := by
  obtain ⟨σ, hσ⟩ := h.dist_eq
  have h0 := hσ 0 1
  have h1 := hσ 2 0
  have h2 := hσ 1 2
  have hinj := σ.injective
  have hne01 : σ 0 ≠ σ 1 := fun he => by simpa using hinj he
  have hne02 : σ 0 ≠ σ 2 := fun he => by simpa using hinj he
  have hne12 : σ 1 ≠ σ 2 := fun he => by simpa using hinj he
  have hall : σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2
            ∨ σ 0 = 0 ∧ σ 1 = 2 ∧ σ 2 = 1
            ∨ σ 0 = 1 ∧ σ 1 = 0 ∧ σ 2 = 2
            ∨ σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0
            ∨ σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1
            ∨ σ 0 = 2 ∧ σ 1 = 1 ∧ σ 2 = 0 := by
    have h30 : σ 0 = 0 ∨ σ 0 = 1 ∨ σ 0 = 2 := by omega
    have h31 : σ 1 = 0 ∨ σ 1 = 1 ∨ σ 1 = 2 := by omega
    have h32 : σ 2 = 0 ∨ σ 2 = 1 ∨ σ 2 = 2 := by omega
    rcases h30 with h30 | h30 | h30 <;> rcases h31 with h31 | h31 | h31 <;>
      rcases h32 with h32 | h32 | h32 <;>
      simp_all
  rw [h0, h1, h2]
  rcases hall with ⟨e0,e1,e2⟩|⟨e0,e1,e2⟩|⟨e0,e1,e2⟩|⟨e0,e1,e2⟩|⟨e0,e1,e2⟩|⟨e0,e1,e2⟩ <;>
    rw [e0, e1, e2] <;>
    simp only [dist_comm (U.pts 1) (U.pts 0), dist_comm (U.pts 2) (U.pts 0),
      dist_comm (U.pts 2) (U.pts 1)] <;>
    show ({_, _, _} : Multiset ℝ) = {_, _, _} <;>
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add] <;>
    simp only [add_comm, add_assoc, add_left_comm]

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

/-- **Relabelling a tile's vertices by a permutation** — the same triangle, same carrier, just a
different `pts : Fin 3 → Plane` indexing. Needed because a `CongruentDissection`'s `model`'s vertex
order is whatever a certificate happened to produce, and matching it against an external
convention (e.g. `TilePlacement.sideOpp`'s side-`j`-opposite-vertex-`j` labelling) may need a
different order. -/
noncomputable def Tri.relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : Tri where
  pts := T.pts ∘ τ
  indep := T.indep.comp_embedding τ.toEmbedding

theorem Tri.relabel_pts (T : Tri) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel τ).pts k = T.pts (τ k) := rfl

/-- **A relabelling is congruent to the original** — trivially, via the identity isometry and the
permutation itself. -/
theorem Tri.congruent_relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : T.Congruent (T.relabel τ) := by
  refine ⟨IsometryEquiv.refl Plane, τ.symm, fun k => ?_⟩
  show T.pts k = (T.relabel τ).pts (τ.symm k)
  simp [Tri.relabel_pts]

/-- Congruence composes through a relabelling of the target. -/
theorem Tri.Congruent.relabel {T U : Tri} (h : T.Congruent U) (τ : Equiv.Perm (Fin 3)) :
    T.Congruent (U.relabel τ) :=
  h.trans (U.congruent_relabel τ)

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

/-- **The same `CongruentDissection`, with its model relabelled by a permutation.** Every tile is
still congruent (relabelling composes with the existing witness), and the target/tiles are
untouched — only which index of `model` names which vertex changes. Useful for matching a
certificate-produced model's vertex order against an external convention. -/
noncomputable def relabelModel (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) :
    CongruentDissection N where
  toDissection := D.toDissection
  model := D.model.relabel τ
  tiles_congruent := fun i => (D.tiles_congruent i).relabel τ

theorem relabelModel_model_pts (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (D.relabelModel τ).model.pts k = D.model.pts (τ k) := rfl

end CongruentDissection

end Erdos634.Geometry
