import Erdos634.LayerLink

/-!
# The `base` hypothesis of `interior_rigidity_of_predecessor` is a gauge choice, not geometry

`StripIteration.interior_rigidity_of_predecessor` carries one named gap: its hypothesis

```
base : ¬ (D.tile (idx 0)).Reflected D.model
```

recorded there as "a local statement about one tile", to be settled by geometry — e.g. by
pinning the base corner tile with `CornerBaseEdgesReal` / `ApexEdgesReal`.

**That cannot work, and it does not need to.**  This file proves both halves.

## Why no geometry can prove `base`

`Tri.Reflected T model` is `(0 < T.det) ↔ (model.det < 0)`: it compares the tile's orientation
with *the model's*.  But `CongruentDissection.model` is constrained only by
`tiles_congruent : ∀ i, (tile i).Congruent model`, and `Tri.Congruent` (`Congruence.lean:52`)
quantifies over **all** `Plane ≃ᵢ Plane`, orientation-reversing ones included.  So the very same
`Dissection` — same target, same tiles, same combinatorics — underlies two `CongruentDissection`
structures whose models are mirror images, and every tile's `Reflected` status differs between
them (`reflected_flips_under_mirror_model`).  No property of the target or of the tiles can decide
`base`, because `base` is not a property of the target or of the tiles.  In particular the corner
theorems (`TileAt.congruentDissection_base_corner_tile_vertex`, `CornerBaseEdgesReal`) pin the
corner tile's *vertex and edge lengths*, which are exactly the mirror-invariant data, so they are
provably the wrong tool for this hypothesis.

## Why `base` is nevertheless free

Because the model's orientation is unconstrained, it can be *chosen*.  `atModel` rebuilds the
dissection with `model := tile i` for any index `i`, changing nothing else; `atModel_not_reflected`
then discharges `base` outright, and `atModel_unreflectedAt_iff` says what the conclusion means
afterwards: "same orientation as tile `i`", which is model-free.

`interior_rigidity_base_free` is the payoff — `interior_rigidity_of_predecessor` with `base`
**removed**, concluding that every tile of the run has the orientation of the run's leftmost tile.

## What this does and does not close

It closes `base`, honestly and completely: the descent iteration needs no base case.  It does
**not** close the iteration, and it makes the remaining burden sharper rather than smaller: the
surviving hypothesis `step` must now be supplied *relative to the run's own leftmost tile*, i.e.
in the model-free form "adjacent tiles of the run are never oppositely oriented"
(`Tri.OppOrient`).  That is the pairwise form of the overlap exclusion, and it is where the
geometry actually lives.  `interior_rigidity_of_adjacent` states the iteration in exactly that
form, with no model and no base case at all.

Date: 2026-09-09.
-/

namespace Erdos634.Geometry

variable {N : ℕ}

/-! ## Orientation, compared between two tiles rather than against a model -/

/-- **Two tiles have opposite orientations.**  Model-free: unlike `Tri.Reflected`, this mentions
no `model`, so it is invariant under the choice of model in a `CongruentDissection`. -/
def Tri.OppOrient (T U : Tri) : Prop := (0 < T.det) ↔ (U.det < 0)

/-- **Two tiles have the same orientation.**  The model-free counterpart of `Tri.Unreflected`. -/
def Tri.EqOrient (T U : Tri) : Prop := (0 < T.det) ↔ (0 < U.det)

theorem Tri.EqOrient.refl (T : Tri) : T.EqOrient T := Iff.rfl

theorem Tri.EqOrient.symm {T U : Tri} (h : T.EqOrient U) : U.EqOrient T := Iff.symm h

theorem Tri.EqOrient.trans {T U V : Tri} (h₁ : T.EqOrient U) (h₂ : U.EqOrient V) : T.EqOrient V :=
  Iff.trans h₁ h₂

/-- `Tri.Unreflected` is `EqOrient` against the model — definitional, recorded to make the
translation between the model-relative and model-free languages explicit. -/
theorem Tri.unreflected_iff_eqOrient (T model : Tri) : T.Unreflected model ↔ T.EqOrient model :=
  Iff.rfl

/-- `Tri.Reflected` is `OppOrient` against the model. -/
theorem Tri.reflected_iff_oppOrient (T model : Tri) : T.Reflected model ↔ T.OppOrient model :=
  Iff.rfl

/-- **The dichotomy, model-free.**  Two tiles are equally or oppositely oriented; nondegeneracy
comes from `Tri.det_ne_zero`, so there is no hypothesis. -/
theorem Tri.eqOrient_or_oppOrient (T U : Tri) : T.EqOrient U ∨ T.OppOrient U :=
  Tri.unreflected_or_reflected T U

/-- **Not oppositely oriented means equally oriented.** -/
theorem Tri.eqOrient_of_not_oppOrient {T U : Tri} (h : ¬ T.OppOrient U) : T.EqOrient U :=
  (Tri.eqOrient_or_oppOrient T U).resolve_right h

/-! ## The gauge: re-choosing the model -/

/-- **The same dissection, with the model taken to be tile `i`.**  Legitimate because
`Tri.Congruent` is an equivalence relation, so every tile is congruent to any one tile.  The
underlying `Dissection` — target, tiles, coverage, disjointness — is untouched. -/
def CongruentDissection.atModel (D : CongruentDissection N) (i : Fin N) :
    CongruentDissection N where
  toDissection := D.toDissection
  model := D.tile i
  tiles_congruent := fun k => (D.tiles_congruent k).trans (D.tiles_congruent i).symm

@[simp] theorem CongruentDissection.atModel_tile (D : CongruentDissection N) (i k : Fin N) :
    (D.atModel i).tile k = D.tile k := rfl

@[simp] theorem CongruentDissection.atModel_model (D : CongruentDissection N) (i : Fin N) :
    (D.atModel i).model = D.tile i := rfl

/-- **`base` is discharged by the gauge choice.**  A triangle is never oppositely oriented to
itself, so after re-modelling at tile `i`, tile `i` is unreflected — with no geometry used. -/
theorem CongruentDissection.atModel_not_reflected (D : CongruentDissection N) (i : Fin N) :
    ¬ ((D.atModel i).tile i).Reflected (D.atModel i).model := by
  intro h
  rcases (D.tile i).det_pos_or_neg with hp | hn
  · exact absurd (h.mp hp) (asymm hp)
  · exact absurd (h.mpr hn) (asymm hn)

/-- **What the conclusion means after the gauge choice**: `UnreflectedAt` relative to the
re-chosen model is exactly "same orientation as tile `i`", a model-free statement. -/
theorem CongruentDissection.atModel_unreflectedAt_iff (D : CongruentDissection N) (i k : Fin N) :
    (D.atModel i).UnreflectedAt k ↔ (D.tile k).EqOrient (D.tile i) := Iff.rfl

/-- **No property of the tiles can decide `base`.**  If `model'` is oriented oppositely to
`model`, then a tile is `Reflected` against exactly one of the two.  Since `Tri.Congruent` admits
orientation-reversing isometries, both are legitimate models for the *same* dissection, so
`Reflected … model` is not determined by the dissection. -/
theorem Tri.reflected_flips_under_mirror_model (T model model' : Tri)
    (h : model.OppOrient model') : T.Reflected model ↔ T.Unreflected model' := by
  simp only [Tri.Reflected, Tri.Unreflected, Tri.OppOrient] at *
  rcases T.det_pos_or_neg with hT | hT <;> rcases model.det_pos_or_neg with hM | hM <;>
    rcases model'.det_pos_or_neg with hM' | hM' <;>
    simp_all [asymm hT, asymm hM, asymm hM']

/-! ## The iteration, with the base case removed -/

/-- **Interior rigidity with no base case.**  If no two adjacent tiles of the run are oppositely
oriented, every tile of the run has the orientation of the run's leftmost tile.

This is `StripIteration.interior_rigidity_of_predecessor` with its hypothesis `base` deleted and
its model eliminated.  Both were gauge, not geometry; the whole burden is the adjacency
hypothesis, which is the pairwise form of the overlap exclusion. -/
theorem interior_rigidity_of_adjacent (D : CongruentDissection N) (idx : ℕ → Fin N)
    (adj : ∀ j, ¬ (D.tile (idx (j + 1))).OppOrient (D.tile (idx j))) :
    ∀ j, (D.tile (idx j)).EqOrient (D.tile (idx 0)) := by
  intro j
  induction j with
  | zero => exact Tri.EqOrient.refl _
  | succ n ih => exact Tri.EqOrient.trans (Tri.eqOrient_of_not_oppOrient (adj n)) ih

/-- **`interior_rigidity_of_predecessor`, base hypothesis discharged.**  Same `step` shape as the
original, now taken relative to the run's own leftmost tile — where it is exactly the pairwise
overlap exclusion — and the conclusion is unconditional. -/
theorem interior_rigidity_base_free (D : CongruentDissection N) (idx : ℕ → Fin N)
    (step : ∀ j, (D.atModel (idx 0)).UnreflectedAt (idx j) →
      ¬ ((D.atModel (idx 0)).tile (idx (j + 1))).Reflected (D.atModel (idx 0)).model) :
    ∀ j, (D.atModel (idx 0)).UnreflectedAt (idx j) :=
  layer_rigid_of_exclusions (D.atModel (idx 0)) idx
    (D.atModel_not_reflected (idx 0)) step

/-! ## Non-vacuity

Project rule: exhibit a witness for every hypothesis.  `CongruentDissection` is inhabited
(`Tiling44Bridge.dissection`, `CollarCongruentM4.delta4CongruentDissection`), and the adjacency
hypothesis of `interior_rigidity_of_adjacent` is satisfiable — a triangle is never oppositely
oriented to itself, so any constant indexing satisfies it. -/

theorem Tri.not_oppOrient_self (T : Tri) : ¬ T.OppOrient T := by
  intro h
  rcases T.det_pos_or_neg with hp | hn
  · exact absurd (h.mp hp) (asymm hp)
  · exact absurd (h.mpr hn) (asymm hn)

/-- A witness that `interior_rigidity_of_adjacent`'s hypothesis is satisfiable. -/
theorem adjacent_hypothesis_satisfiable (D : CongruentDissection N) (i : Fin N) :
    ∀ j, ¬ (D.tile ((fun _ => i : ℕ → Fin N) (j + 1))).OppOrient
      (D.tile ((fun _ => i : ℕ → Fin N) j)) :=
  fun _ => Tri.not_oppOrient_self _

end Erdos634.Geometry
