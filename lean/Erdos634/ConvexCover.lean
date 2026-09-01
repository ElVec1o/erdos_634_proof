import Erdos634.Dissection

/-!
# Covering from area: building a `Dissection` without proving the union pointwise

Erdős #634 — the **certified-search bridge**'s missing step.

Every certificate this project produces (`Tiling44`, `Tiling99`, `CevianTiling63`,
`PgramTiling22`, …) checks four things by `decide`, in exact arithmetic:

* **(C1)** each piece is congruent to the tile (squared side multiset);
* **(C2)** each piece lies in the closed target;
* **(C3)** the pieces have pairwise disjoint interiors (an explicit separating line per pair);
* **(C4)** the signed areas sum to the target's.

What `Dissection` asks for instead is the *pointwise* covering `⋃ᵢ (tile i).carrier = target.carrier`,
which no certificate checks and which the `PAPER_MAP` rows for `thm:44`, `thm:63`, `cor:elevenm`,
`thm:frontier`–`thm:frontier4` and `thm:eq105` all cite as the reason they stay `PROVED`: "the
bridge from a checked certificate to a `Dissection`".

This file supplies exactly that bridge. **(C2) + (C3) + (C4) imply the covering**, with no further
geometric input, by a measure argument:

* the union is closed (a finite union of compacts), so its complement in the target is *relatively
  open*;
* a triangle is the closure of its interior (`Convex.closure_interior_eq_closure_of_nonempty_interior`),
  so a nonempty relatively open subset of the target meets the target's interior, hence contains a
  nonempty *open* set, hence has **positive** volume;
* but disjoint interiors make the pieces a.e. disjoint (`Tri.volume_frontier`), so the union's
  volume is the sum, which is the target's; a positive-volume subset of the target disjoint from
  the union would push the target's volume strictly above itself.

The conclusion is `covers_of_volume`, and `ofCertificate` packages it as a genuine `Dissection`.
Note the hypotheses are exactly (C2), (C3), (C4) — nothing here needs (C1), which is the separate
congruence datum a `CongruentDissection` carries.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ConvexCover

open Erdos634.Geometry MeasureTheory

variable {N : ℕ}

/-- **Disjoint interiors give a.e. disjointness**, for a bare family of triangles. This is
`Dissection.aedisjoint`'s argument, stated before a `Dissection` exists: a common point of two
pieces is interior to at most one of them, so it lies on a frontier, and frontiers are null. -/
theorem aedisjoint_of_interiors {t₁ t₂ : Tri}
    (h : Disjoint (interior t₁.carrier) (interior t₂.carrier)) :
    AEDisjoint volume t₁.carrier t₂.carrier := by
  have hsub : t₁.carrier ∩ t₂.carrier ⊆ frontier t₁.carrier ∪ frontier t₂.carrier := by
    rintro x ⟨hx₁, hx₂⟩
    by_cases h1 : x ∈ interior t₁.carrier
    · by_cases h2 : x ∈ interior t₂.carrier
      · exact absurd h2 (Set.disjoint_left.mp h h1)
      · exact Or.inr ⟨subset_closure hx₂, h2⟩
    · exact Or.inl ⟨subset_closure hx₁, h1⟩
  exact measure_mono_null hsub (measure_union_null t₁.volume_frontier t₂.volume_frontier)

/-- **A nonempty subset of a triangle that is open in the ambient plane has positive volume.** -/
theorem volume_pos_of_isOpen {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < volume U :=
  hU.measure_pos volume hne

/-- **The union of the pieces has the sum of their volumes**, given pairwise disjoint interiors. -/
theorem volume_iUnion_eq_sum (tile : Fin N → Tri)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)) :
    volume (⋃ i, (tile i).carrier) = ∑ i, volume (tile i).carrier := by
  rw [measure_iUnion₀ (fun i j hij => aedisjoint_of_interiors (hdisj hij))
    (fun i => (tile i).nullMeasurableSet), tsum_fintype]

/-- **The covering follows from containment, disjoint interiors and the area identity.**

This is the certified-search bridge: a certificate checks (C2) `hsub`, (C3) `hdisj` and (C4)
`hvol`, and this theorem produces the pointwise covering that `Dissection` requires. -/
theorem covers_of_volume (target : Tri) (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume target.carrier) :
    (⋃ i, (tile i).carrier) = target.carrier := by
  classical
  set U : Set Plane := ⋃ i, (tile i).carrier with hUdef
  have hUsub : U ⊆ target.carrier := Set.iUnion_subset hsub
  have hUvol : volume U = volume target.carrier := by
    rw [hUdef, volume_iUnion_eq_sum tile hdisj, hvol]
  -- the union is closed, being a finite union of compacts
  have hUclosed : IsClosed U := by
    rw [hUdef]
    exact isClosed_iUnion_of_finite fun i => (tile i).isCompact.isClosed
  refine Set.Subset.antisymm hUsub ?_
  -- suppose some target point is uncovered
  by_contra hcon
  obtain ⟨x, hxT, hxU⟩ : ∃ x, x ∈ target.carrier ∧ x ∉ U := by
    by_contra hall
    push_neg at hall
    exact hcon fun x hx => hall x hx
  -- `Uᶜ` is an open neighbourhood of `x`, and `x` is in the closure of the target's interior
  have hVopen : IsOpen (Uᶜ) := hUclosed.isOpen_compl
  have hxcl : x ∈ closure (interior target.carrier) := by
    have hconv : Convex ℝ target.carrier := by
      rw [Erdos634.Geometry.Tri.carrier]; exact convex_convexHull ℝ _
    have hclosed : IsClosed target.carrier := target.isCompact.isClosed
    have := hconv.closure_interior_eq_closure_of_nonempty_interior target.interior_nonempty
    rw [this, hclosed.closure_eq]
    exact hxT
  -- so the open set `Uᶜ` meets the target's interior
  obtain ⟨y, hyV, hyI⟩ : ∃ y, y ∈ Uᶜ ∧ y ∈ interior target.carrier :=
    mem_closure_iff.mp hxcl (Uᶜ) hVopen hxU
  -- `W` is a nonempty open subset of the target, disjoint from the union
  set W : Set Plane := Uᶜ ∩ interior target.carrier with hWdef
  have hWopen : IsOpen W := hVopen.inter isOpen_interior
  have hWne : W.Nonempty := ⟨y, hyV, hyI⟩
  have hWpos : 0 < volume W := volume_pos_of_isOpen hWopen hWne
  have hWsub : W ⊆ target.carrier := fun z hz => interior_subset hz.2
  have hWdisj : Disjoint U W := Set.disjoint_right.mpr fun z hz => hz.1
  -- the target then has volume strictly above its own
  have hsum : volume U + volume W ≤ volume target.carrier := by
    have hunion : volume (U ∪ W) = volume U + volume W :=
      measure_union₀ hWopen.measurableSet.nullMeasurableSet hWdisj.aedisjoint
    rw [← hunion]
    exact measure_mono (Set.union_subset hUsub hWsub)
  rw [hUvol] at hsum
  have hfin : volume target.carrier ≠ ⊤ := target.volume_ne_top
  have : volume target.carrier + 0 < volume target.carrier + volume W :=
    ENNReal.add_lt_add_left hfin hWpos
  simp only [add_zero] at this
  exact absurd hsum (not_le.mpr this)

/-- **A `Dissection` from a certificate.** Containment, disjoint interiors and the area identity —
exactly the certificates' (C2), (C3), (C4) — build the structure. -/
noncomputable def ofCertificate (target : Tri) (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume target.carrier) :
    Dissection N where
  target := target
  tile := tile
  covers := covers_of_volume target tile hsub hdisj hvol
  interiors_disjoint := hdisj

end Erdos634.ConvexCover
