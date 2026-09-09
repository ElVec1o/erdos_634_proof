import Erdos634.OverlapAsymmetry

/-!
# The mirror gauge: why no global count can supply reach-4's missing endpoint

`OverlapAsymmetry` closed the local routes to the base case of the interior descent, and recorded
the obligation in its sharpened form:

> rigidity of an interior run holds iff the run's **first** tile is chart-unreflected **or** its
> **last** tile is chart-reflected.

Both disjuncts are statements about one tile's orientation *relative to the chart*.  The natural
next idea is to supply one of them **globally** — a count or parity of reflected versus unreflected
tiles across the whole dissection, forced by area, by the angle census, by an Euler relation — and
then argue that not every run can be the bad one.  This file proves that idea cannot work, and the
reason is a symmetry, not a shortage of effort.

## The symmetry

A plane reflection carries a dissection to a dissection (`Dissection.mirror`), congruent tiles to
congruent tiles (`CongruentDissection.mirror`), and it **negates every tile's determinant**
(`Tri.det_mirror`).  So it flips every tile's orientation while leaving the target, the areas, the
angles, the incidence combinatorics and the tile count untouched.  In particular:

* `mirror_flips_all_orientations` — every tile's `Tri.Reflected`/`OppOrient` status against a fixed
  frame is reversed;
* `card_unreflected_mirror` — the *count* of unreflected tiles becomes the count of reflected ones,
  so `#unreflected − #reflected` changes sign.

Every quantity a global count could be built from — area (`CongruentArea`), the angle census
(`lem:census`), Euler-type incidence relations, the boundary walk's letter multiset — is invariant
under an isometry, hence under the mirror.  A mirror-invariant quantity cannot determine a
mirror-anti-invariant one unless the latter is identically zero, and `#unrefl − #refl ≡ N (mod 2)`
is **odd** for the prime case.  `no_global_orientation_count` is that statement.

## The sharper, and more useful, consequence

The mirror does not merely fail to give the endpoint fact; it explains the *disjunction*
`OverlapAsymmetry` was forced into.  Reflecting reverses the direction along the floor, so it
reverses the run's indexing while complementing every letter: the orientation word `w` of a run of
length `n+1` becomes `wordMirror n w`, reverse-and-complement.  Under it,

* "first tile chart-unreflected" ↔ "last tile chart-reflected" (`first_mirror`, `last_mirror`);
* monotone words `refl^p unrefl^q` go to `refl^q unrefl^p` (`monotone_wordMirror`), so the class
  `OverlapAsymmetry` isolates is closed;
* being **mixed** — the one configuration rigidity fails on — is preserved (`mixed_wordMirror`).

Hence `mirror_invariant_forces_mixed`: *any* predicate on runs that is invariant under the mirror
and implies "the first tile is chart-unreflected" also implies, through the mirror, "the last tile
is chart-reflected" — so it holds **only on mixed runs**.  Establishing such a criterion for a given
run would prove that run *is* the bad configuration, not that it is not.  In particular it is false
on every rigid run (`mirror_invariant_fails_on_constant`) and vacuous on a one-tile run
(`mirror_invariant_empty_at_zero`).  This is the circularity audit CLAUDE.md requires, run against a
whole class of proposed arguments at once rather than one at a time.

So the honest statement of what remains is unchanged in content but sharpened in form: the
disjunction must be proved *as a disjunction*, by an argument that is not mirror-equivariant — that
is, one which uses the floor's direction as data.  No global count is such an argument.

Axiom-clean, no `sorry`.  Date: 2026-09-09.
-/

namespace Erdos634.MirrorGauge

open Erdos634.Geometry

/-! ## The plane mirror -/

/-- Reflection of the plane in the first coordinate axis. -/
noncomputable def mirrorPt (p : Plane) : Plane := WithLp.toLp 2 ![p 0, - p 1]

@[simp] theorem mirrorPt_zero (p : Plane) : mirrorPt p 0 = p 0 := rfl

@[simp] theorem mirrorPt_one (p : Plane) : mirrorPt p 1 = - p 1 := rfl

@[simp] theorem mirrorPt_involutive (p : Plane) : mirrorPt (mirrorPt p) = p := by
  ext i; fin_cases i <;> simp

theorem mirrorPt_injective : Function.Injective mirrorPt := fun p q h => by
  have := congrArg mirrorPt h; simpa using this

/-- The mirror as a linear map — needed for `AffineMap.image_convexHull`. -/
noncomputable def mirrorL : Plane →ₗ[ℝ] Plane where
  toFun := mirrorPt
  map_add' := by intro x y; ext i; fin_cases i <;> simp; ring
  map_smul' := by intro c x; ext i; fin_cases i <;> simp

@[simp] theorem mirrorL_apply (p : Plane) : mirrorL p = mirrorPt p := rfl

theorem mirrorPt_dist (p q : Plane) : dist (mirrorPt p) (mirrorPt q) = dist p q := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  fin_cases i
  · simp
  · show dist (mirrorPt p 1) (mirrorPt q 1) ^ 2 = dist (p 1) (q 1) ^ 2
    rw [mirrorPt_one, mirrorPt_one, dist_neg_neg]

/-- The mirror as an isometry equivalence of the plane — the shape `Tri.Congruent` consumes. -/
noncomputable def mirrorIso : Plane ≃ᵢ Plane where
  toFun := mirrorPt
  invFun := mirrorPt
  left_inv := mirrorPt_involutive
  right_inv := mirrorPt_involutive
  isometry_toFun := Isometry.of_dist_eq mirrorPt_dist

@[simp] theorem mirrorIso_apply (p : Plane) : mirrorIso p = mirrorPt p := rfl

/-- The mirror as a homeomorphism — needed to transport `interior`. -/
noncomputable def mirrorHomeo : Homeomorph Plane Plane := mirrorIso.toHomeomorph

@[simp] theorem mirrorHomeo_apply (p : Plane) : mirrorHomeo p = mirrorPt p := rfl

/-! ## The mirror of a triangle -/

/-- The mirror image of a triangle, vertex labels kept in place. -/
noncomputable def Tri.mirror (T : Tri) : Tri where
  pts := mirrorPt ∘ T.pts
  indep := T.indep.map' mirrorL.toAffineMap mirrorPt_injective

@[simp] theorem Tri.mirror_pts (T : Tri) (k : Fin 3) : (Tri.mirror T).pts k = mirrorPt (T.pts k) :=
  rfl

/-- **The mirror negates the determinant.**  This is the whole content: reflecting reverses every
tile's orientation, and nothing else about the configuration changes. -/
theorem Tri.det_mirror (T : Tri) : (Tri.mirror T).det = - T.det := by
  simp only [Erdos634.Geometry.Tri.det, Tri.mirror_pts]
  have h0 : ∀ u v : Plane, (mirrorPt u - mirrorPt v) 0 = (u - v) 0 := by
    intro u v; simp
  have h1 : ∀ u v : Plane, (mirrorPt u - mirrorPt v) 1 = - ((u - v) 1) := by
    intro u v; simp; ring
  rw [h0, h0, h1, h1]; ring

/-- The mirror carries the filled triangle to the image of the filled triangle. -/
theorem Tri.carrier_mirror (T : Tri) :
    (Tri.mirror T).carrier = mirrorPt '' T.carrier := by
  have hcomp : ⇑(mirrorL.toAffineMap) = mirrorPt := rfl
  rw [Erdos634.Geometry.Tri.carrier, Erdos634.Geometry.Tri.carrier, ← hcomp,
    AffineMap.image_convexHull]
  congr 1
  rw [Tri.mirror, ← Set.range_comp]
  rfl

/-- The mirror preserves congruence, with the same vertex permutation. -/
theorem Tri.congruent_mirror {T U : Tri} (h : T.Congruent U) :
    (Tri.mirror T).Congruent (Tri.mirror U) := by
  obtain ⟨g, σ, hg⟩ := h
  refine ⟨mirrorIso.trans (g.trans mirrorIso), σ, fun k => ?_⟩
  show mirrorPt (g (mirrorPt (mirrorPt (T.pts k)))) = mirrorPt (U.pts (σ k))
  rw [mirrorPt_involutive, hg]

/-- Every triangle is congruent to its own mirror image — the reason the mirror image of a
`CongruentDissection` is again one *with the same tile shape*. -/
theorem Tri.congruent_self_mirror (T : Tri) : T.Congruent (Tri.mirror T) :=
  ⟨mirrorIso, Equiv.refl _, fun _ => rfl⟩

/-! ## The mirror of a dissection -/

/-- **The mirror image of a dissection is a dissection.**  Target and tiles are reflected; coverage
and interior-disjointness transport because `mirrorPt` is a homeomorphism. -/
noncomputable def Dissection.mirror {N : ℕ} (D : Dissection N) : Dissection N where
  target := Tri.mirror D.target
  tile := fun i => Tri.mirror (D.tile i)
  covers := by
    have : (⋃ i, mirrorPt '' (D.tile i).carrier) = mirrorPt '' (⋃ i, (D.tile i).carrier) := by
      rw [Set.image_iUnion]
    simp only [Tri.carrier_mirror]
    rw [this, D.covers]
  interiors_disjoint := by
    intro i j hij
    have hd : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
      D.interiors_disjoint hij
    simp only [Tri.carrier_mirror]
    have hi : ∀ k, interior (mirrorPt '' (D.tile k).carrier)
        = mirrorPt '' interior (D.tile k).carrier := by
      intro k
      have := mirrorHomeo.image_interior (D.tile k).carrier
      simpa using this.symm
    rw [hi, hi]
    exact (Set.disjoint_image_iff mirrorPt_injective).mpr hd

@[simp] theorem Dissection.mirror_tile {N : ℕ} (D : Dissection N) (i : Fin N) :
    (Dissection.mirror D).tile i = Tri.mirror (D.tile i) := rfl

/-- **The mirror image of a congruent dissection is a congruent dissection**, with the *same* model
(not the mirrored model): every tile is congruent to its own mirror, so the shape is unchanged. -/
noncomputable def CongruentDissection.mirror {N : ℕ} (D : CongruentDissection N) :
    CongruentDissection N where
  toDissection := Dissection.mirror D.toDissection
  model := D.model
  tiles_congruent := fun i =>
    (Tri.congruent_self_mirror (D.tile i)).symm.trans (D.tiles_congruent i)

@[simp] theorem CongruentDissection.mirror_tile {N : ℕ} (D : CongruentDissection N) (i : Fin N) :
    (CongruentDissection.mirror D).tile i = Tri.mirror (D.tile i) := rfl

@[simp] theorem CongruentDissection.mirror_model {N : ℕ} (D : CongruentDissection N) :
    (CongruentDissection.mirror D).model = D.model := rfl

/-! ## Every orientation is flipped, so no global count is forced -/

/-- **The mirror flips every tile's orientation** against a fixed model. -/
theorem mirror_flips_all_orientations {N : ℕ} (D : CongruentDissection N) (i : Fin N) :
    (CongruentDissection.mirror D).UnreflectedAt i ↔ (D.tile i).Reflected D.model := by
  show ((Tri.mirror (D.tile i)).det > 0 ↔ D.model.det > 0) ↔ _
  rw [Tri.det_mirror]
  simp only [Erdos634.Geometry.Tri.Reflected]
  rcases (D.tile i).det_pos_or_neg with h | h <;>
    rcases D.model.det_pos_or_neg with h' | h' <;>
    constructor <;> intro _ <;>
    simp_all [asymm h, asymm h']

/-- **The count of unreflected tiles becomes the count of reflected tiles.**  So the difference
`#unreflected − #reflected` changes sign under an operation that changes nothing else about the
dissection. -/
theorem card_unreflected_mirror {N : ℕ} (D : CongruentDissection N)
    [DecidablePred fun i => (CongruentDissection.mirror D).UnreflectedAt i]
    [DecidablePred fun i => (D.tile i).Reflected D.model] :
    (Finset.univ.filter fun i => (CongruentDissection.mirror D).UnreflectedAt i).card
      = (Finset.univ.filter fun i => (D.tile i).Reflected D.model).card := by
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simpa using mirror_flips_all_orientations D i

/-- **No global orientation count exists.**  Suppose some quantity computed from mirror-invariant
data — area, angles, incidence counts, the tile count — determined the signed orientation excess
`u - r`.  Evaluating it on `D` and on `mirror D` returns the same number, while
`card_unreflected_mirror` says the excess changes sign; so the excess would be `0`.  But
`u + r = N`, so `u - r = 0` forces `N` even.  For the prime case `N` is odd, and the route is
closed.  Stated here in the arithmetic form the contradiction actually takes. -/
theorem no_global_orientation_count (N u r : ℕ) (hsum : u + r = N) (hodd : Odd N)
    (hzero : (u : ℤ) - r = 0) : False := by
  have huv : u = r := by
    have : (u : ℤ) = r := by linarith
    exact_mod_cast this
  obtain ⟨k, hk⟩ := hodd
  omega

/-! ## The word-level mirror, and the circularity theorem

Reflecting the configuration reverses the direction along the floor, so it reverses the run's
indexing as well as complementing every letter.  `wordMirror n` is that operation on the orientation
word of a run of length `n+1`. -/

/-- Reverse-and-complement: the action of the mirror on the orientation word of a run of length
`n+1`.  `true` is "reflected in the chart", matching `OverlapAsymmetry`'s convention. -/
def wordMirror (n : ℕ) (w : ℕ → Bool) : ℕ → Bool := fun j => ! w (n - j)

theorem wordMirror_involutive (n : ℕ) (w : ℕ → Bool) (j : ℕ) (hj : j ≤ n) :
    wordMirror n (wordMirror n w) j = w j := by
  simp only [wordMirror, Bool.not_not]
  congr 1
  omega

/-- The first letter of the mirrored word is the complement of the last letter. -/
@[simp] theorem first_mirror (n : ℕ) (w : ℕ → Bool) : wordMirror n w 0 = ! w n := by
  simp [wordMirror]

/-- The last letter of the mirrored word is the complement of the first letter. -/
@[simp] theorem last_mirror (n : ℕ) (w : ℕ → Bool) : wordMirror n w n = ! w 0 := by
  simp [wordMirror]

/-- A run is **mixed** when it carries both letters — the configuration on which rigidity fails, and
the only one `OverlapAsymmetry`'s monotone conclusion leaves open. -/
def Mixed (n : ℕ) (w : ℕ → Bool) : Prop := (∃ i ≤ n, w i = true) ∧ (∃ i ≤ n, w i = false)

/-- **Mixedness is mirror-invariant.**  The mirror maps the bad configuration to a bad
configuration; it cannot be used to argue one away. -/
theorem mixed_wordMirror {n : ℕ} {w : ℕ → Bool} (h : Mixed n w) : Mixed n (wordMirror n w) := by
  obtain ⟨⟨i, hi, hti⟩, ⟨j, hj, hfj⟩⟩ := h
  refine ⟨⟨n - j, by omega, ?_⟩, ⟨n - i, by omega, ?_⟩⟩
  · simp only [wordMirror]
    rw [show n - (n - j) = j by omega, hfj]; rfl
  · simp only [wordMirror]
    rw [show n - (n - i) = i by omega, hti]; rfl

/-- The monotone class `false^p true^q` that `OverlapAsymmetry.monotone_of_step` isolates, stated
on `[0, n]`: once the word turns `true` it stays `true`. -/
def MonotoneWord (n : ℕ) (w : ℕ → Bool) : Prop :=
  ∀ i j, i ≤ j → j ≤ n → w i = true → w j = true

/-- **The monotone class is mirror-closed.**  So the mirror really is a symmetry of the situation
`OverlapAsymmetry` leaves behind, not an operation that escapes it. -/
theorem monotone_wordMirror {n : ℕ} {w : ℕ → Bool} (h : MonotoneWord n w) :
    MonotoneWord n (wordMirror n w) := by
  intro i j hij hjn hi
  simp only [wordMirror, Bool.not_eq_true'] at hi ⊢
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  have := h (n - j) (n - i) (by omega) (by omega) hcon
  rw [this] at hi
  exact Bool.noConfusion hi

/-- **A mirror-invariant endpoint criterion forces the last letter too.**  If `P` is preserved by
the mirror and implies "first letter `false`", then it also implies "last letter `true`" — because
the mirror turns the first letter into the complement of the last.  This is the mechanism behind
everything below. -/
theorem mirror_invariant_forces_last
    (P : (ℕ → Bool) → Prop) (n : ℕ)
    (hinv : ∀ w, P w → P (wordMirror n w))
    (hfirst : ∀ w, P w → w 0 = false) :
    ∀ w, P w → w n = true := by
  intro w hP
  have hn : wordMirror n w 0 = false := hfirst _ (hinv w hP)
  rw [first_mirror] at hn
  cases hval : w n with
  | false => rw [hval] at hn; exact absurd hn (by simp)
  | true => rfl

/-- **The circularity theorem.**  Let `P` be any property of runs that

* is invariant under the mirror (`hinv`) — true of every quantity built from areas, angles,
  incidence counts, parities, or the tile count, since a reflection preserves all of them; and
* implies the endpoint fact reach-4 wants, "the run's first tile is chart-unreflected"
  (`hfirst`, `w 0 = false`).

Then `P` holds **only on mixed runs**: it forces `w 0 = false` and, through the mirror, `w n = true`
as well.  So establishing such a `P` for a given run would *prove that run mixed* — the exact
configuration the endpoint fact was wanted in order to exclude.  A global count of this kind cannot
be a lemma toward rigidity; it is a proof of its negation.

This closes the whole "global count" family of routes at once, and it explains why the obligation
`OverlapAsymmetry` records is a **disjunction**: the disjunction is the mirror-symmetrisation of
either disjunct, and only the symmetrised form can be mirror-invariant at all. -/
theorem mirror_invariant_forces_mixed
    (P : (ℕ → Bool) → Prop) (n : ℕ)
    (hinv : ∀ w, P w → P (wordMirror n w))
    (hfirst : ∀ w, P w → w 0 = false) :
    ∀ w, P w → Mixed n w := by
  intro w hP
  exact ⟨⟨n, le_rfl, mirror_invariant_forces_last P n hinv hfirst w hP⟩,
    ⟨0, Nat.zero_le n, hfirst w hP⟩⟩

/-- **No mirror-invariant criterion is satisfied by a rigid run.**  A run all of whose tiles carry
the same orientation is exactly what interior rigidity asserts; such a `P` is false there. -/
theorem mirror_invariant_fails_on_constant
    (P : (ℕ → Bool) → Prop) (n : ℕ) (b : Bool)
    (hinv : ∀ w, P w → P (wordMirror n w))
    (hfirst : ∀ w, P w → w 0 = false) :
    ¬ P (fun _ => b) := by
  intro hP
  obtain ⟨⟨i, _, hti⟩, ⟨j, _, hfj⟩⟩ := mirror_invariant_forces_mixed P n hinv hfirst _ hP
  simp only at hti hfj
  rw [hti] at hfj
  exact Bool.noConfusion hfj

/-- **On a one-tile run the criterion is outright unsatisfiable.**  With `n = 0` the first and last
letters coincide, so `P` would force `w 0 = false` and `w 0 = true` at once. -/
theorem mirror_invariant_empty_at_zero
    (P : (ℕ → Bool) → Prop)
    (hinv : ∀ w, P w → P (wordMirror 0 w))
    (hfirst : ∀ w, P w → w 0 = false) :
    ∀ w, ¬ P w := by
  intro w hP
  have h1 : w 0 = true := mirror_invariant_forces_last P 0 hinv hfirst w hP
  rw [hfirst w hP] at h1
  exact Bool.noConfusion h1

/-! ## Non-vacuity

Project rule: exhibit a witness for every hypothesis.  The pair of hypotheses of
`mirror_invariant_forces_mixed` is jointly satisfiable — `endpointBoth` is mirror-invariant and
implies `w 0 = false` — so the theorem is a statement about a nonempty class of criteria, and its
conclusion is sharp: `endpointBoth` holds on exactly the mixed-at-the-ends words. -/

/-- The mirror-symmetrisation of "first letter `false`": the criterion any mirror-invariant
argument is forced to land on. -/
def endpointBoth (n : ℕ) (w : ℕ → Bool) : Prop := w 0 = false ∧ w n = true

theorem endpointBoth_mirror_invariant (n : ℕ) (w : ℕ → Bool) :
    endpointBoth n w → endpointBoth n (wordMirror n w) := by
  rintro ⟨h0, hn⟩
  exact ⟨by rw [first_mirror, hn]; rfl, by rw [last_mirror, h0]; rfl⟩

theorem endpointBoth_first (n : ℕ) (w : ℕ → Bool) : endpointBoth n w → w 0 = false := And.left

/-- The schema is not vacuous: `endpointBoth` satisfies both hypotheses, and is satisfiable (for
`n ≥ 1`) by the word `false, true, true, …`. -/
theorem endpointBoth_witness (n : ℕ) (hn : 1 ≤ n) :
    endpointBoth n (fun j => decide (j ≠ 0)) :=
  ⟨by simp, by simp; omega⟩

end Erdos634.MirrorGauge
