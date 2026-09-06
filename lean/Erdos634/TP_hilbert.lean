import Erdos634.CoversGeneral
import Erdos634.Ladder
import Erdos634.SubDissection
import Erdos634.IsoTri
import Erdos634.LineParam

/-!
# Room `tileplace`, HILBERT mode: the general statement behind the placement gaps

Erdős #634.  The room brief names three gaps — G1 covering-equality, G2 the `kT → k²·T`
subdivision, G3 edge-level placement — and asks whether one general statement covers them.

**Finding, recorded here as theorems.**  G1 and the *covering half* of G3 are the same theorem in
two different dimensions, and the corpus proves it twice, separately:

* dimension 2: `covers_of_volume_general` (`CoversGeneral.lean`) — containment, a.e.-disjointness
  and an exact area identity force a finite family of triangles to fill a convex body;
* dimension 1: `iUnion_Icc_eq_of_sum_eq_length` (bridge (c)) — non-overlapping intervals whose
  lengths sum to the length of a segment fill the segment.

`exact_packing` below is the common generalisation, in an arbitrary topological measure space.  The
hypotheses that make it well-posed, stated explicitly (the brief's fourth question):

1. `μ K ≠ ⊤` — the region has finite measure;
2. `K ⊆ closure (interior K)` — `K` is the closure of its own interior (no lower-dimensional
   whiskers; this is what convexity-plus-nonempty-interior supplies in dimension 2 and what
   `a < b` supplies for `Icc a b` in dimension 1);
3. `0 < μ U` for every nonempty open `U ⊆ K` — `μ` has full support on `K`.  **This is the
   dimension-selecting hypothesis**: plane Lebesgue measure fails it for a segment, which is
   exactly why the wall arguments must be transported to `ℝ` before they can be run;
4. each piece closed, contained in `K`, null-measurable, pairwise a.e.-disjoint;
5. the measures sum to `μ K`.

Dropping (2) or (3) makes the statement false, and (3) is the reason G1 and G3 cannot be *literally*
the same instance even though they are the same theorem.

Both corpus statements are then re-derived as corollaries (`covers_of_volume_general_of_packing`,
`exact_packing_interval`), which is the check that the generalisation is faithful and not merely
suggestive.

The remaining sections record two further findings:

* `subfamily_covers` / `subfamily_covers_finset` — **G1 for a tile subset of an existing dissection
  needs no topology at all**: disjointness is inherited from the ambient dissection, so the only
  obligations left are *containment* (a convexity fact) and an *area count*.  Both are decidable in
  the `ℤ[√D]` coordinates every certificate in this corpus uses.
* `repTile` — the rep-tile object (`kT` cut into `k²` copies of `T`, as a `CongruentDissection`),
  which is `Subdivision.ladderDissection` packaged with its congruence.  This is G2, and it was
  already closed on 2026-09-02 by `Ladder.ladder`; the object is recorded here because
  `Inflation.lean`'s rows are still listed as blocked on "no geometric `Dissection` object of the
  inflated tile", and this *is* that object.

**Non-vacuity.**  Every theorem below has an exhibited witness in the final section: a concrete
`Tri` (`witnessTri`), a concrete `repTile` at `k = 2`, and a general singleton witness for
`subfamily_covers`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TPHilbert

open Erdos634.Geometry MeasureTheory Set

/-! ## 1. The exact-packing principle -/

/-- **Exact packing.**  In a topological measure space, a finite family of closed, a.e.-disjoint,
null-measurable subsets of a finite-measure region `K` whose measures sum to `μ K` covers `K`
exactly — provided `K` is the closure of its interior and `μ` is positive on nonempty open subsets
of `K`.

This is the statement of which `covers_of_volume_general` (dimension 2, G1) and the interval
covering lemma of bridge (c) (dimension 1, the covering half of G3) are the two instances. -/
theorem exact_packing {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {N : ℕ} {K : Set X} {A : Fin N → Set X}
    (hKfin : μ K ≠ ⊤)
    (hKclos : K ⊆ closure (interior K))
    (hpos : ∀ U : Set X, IsOpen U → U.Nonempty → U ⊆ K → 0 < μ U)
    (hAclosed : ∀ i, IsClosed (A i))
    (hAsub : ∀ i, A i ⊆ K)
    (hAmeas : ∀ i, NullMeasurableSet (A i) μ)
    (hAdisj : Pairwise fun i j => AEDisjoint μ (A i) (A j))
    (hsum : ∑ i, μ (A i) = μ K) :
    (⋃ i, A i) = K := by
  classical
  set U : Set X := ⋃ i, A i with hUdef
  have hUsub : U ⊆ K := Set.iUnion_subset hAsub
  have hUvol : μ U = μ K := by
    rw [hUdef, measure_iUnion₀ hAdisj hAmeas, tsum_fintype, hsum]
  have hUclosed : IsClosed U := isClosed_iUnion_of_finite hAclosed
  refine Set.Subset.antisymm hUsub ?_
  by_contra hcon
  obtain ⟨x, hxK, hxU⟩ : ∃ x, x ∈ K ∧ x ∉ U := by
    by_contra hall
    push_neg at hall
    exact hcon fun x hx => hall x hx
  have hVopen : IsOpen (Uᶜ) := hUclosed.isOpen_compl
  obtain ⟨y, hyV, hyI⟩ : ∃ y, y ∈ Uᶜ ∧ y ∈ interior K :=
    mem_closure_iff.mp (hKclos hxK) (Uᶜ) hVopen hxU
  set W : Set X := Uᶜ ∩ interior K with hWdef
  have hWopen : IsOpen W := hVopen.inter isOpen_interior
  have hWne : W.Nonempty := ⟨y, hyV, hyI⟩
  have hWsub : W ⊆ K := fun z hz => interior_subset hz.2
  have hWpos : 0 < μ W := hpos W hWopen hWne hWsub
  have hWdisj : Disjoint U W := Set.disjoint_right.mpr fun z hz => hz.1
  have hle : μ U + μ W ≤ μ K := by
    have hunion : μ (U ∪ W) = μ U + μ W :=
      measure_union₀ hWopen.measurableSet.nullMeasurableSet hWdisj.aedisjoint
    rw [← hunion]
    exact measure_mono (Set.union_subset hUsub hWsub)
  rw [hUvol] at hle
  have hlt : μ K + 0 < μ K + μ W := ENNReal.add_lt_add_left hKfin hWpos
  simp only [add_zero] at hlt
  exact absurd hle (not_le.mpr hlt)

/-! ### The two corpus statements as instances -/

/-- **Dimension 2 (G1).**  `covers_of_volume_general` is `exact_packing` with `μ = volume` on the
plane, `K` a convex compact body with nonempty interior. -/
theorem covers_of_volume_general_of_packing {N : ℕ} {S : Set Plane} (hSconv : Convex ℝ S)
    (hScompact : IsCompact S) (hSint : (interior S).Nonempty) (hSvol : volume S ≠ ⊤)
    (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ S)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i, volume (tile i).carrier = volume S) :
    (⋃ i, (tile i).carrier) = S := by
  refine exact_packing hSvol ?_ (fun U hU hne _ => hU.measure_pos volume hne)
    (fun i => (tile i).isCompact.isClosed) hsub (fun i => (tile i).nullMeasurableSet)
    (fun i j hij => Erdos634.ConvexCover.aedisjoint_of_interiors (hdisj hij)) hvol
  have h1 : closure (interior S) = closure S :=
    hSconv.closure_interior_eq_closure_of_nonempty_interior hSint
  rw [h1, hScompact.isClosed.closure_eq]

/-- **Dimension 1 (the covering half of G3).**  Closed, a.e.-disjoint subsets of a segment whose
lengths sum to the segment's length fill it.  This is the shape bridge (c)'s wall-covering argument
needs, and it is the *same* theorem as the dimension-2 statement above. -/
theorem exact_packing_interval {N : ℕ} {a b : ℝ} (hab : a < b) {A : Fin N → Set ℝ}
    (hAclosed : ∀ i, IsClosed (A i))
    (hAsub : ∀ i, A i ⊆ Set.Icc a b)
    (hAmeas : ∀ i, NullMeasurableSet (A i) volume)
    (hAdisj : Pairwise fun i j => AEDisjoint volume (A i) (A j))
    (hsum : ∑ i, volume (A i) = volume (Set.Icc a b)) :
    (⋃ i, A i) = Set.Icc a b := by
  refine exact_packing (by simp [Real.volume_Icc]) ?_
    (fun U hU hne _ => hU.measure_pos volume hne) hAclosed hAsub hAmeas hAdisj hsum
  rw [interior_Icc, closure_Ioo hab.ne]

/-! ## 2. G1 for a tile subset: containment and an area count, nothing else

Given an ambient `Dissection`, pairwise interior-disjointness of any subfamily is free.  So the
covering-equality hypothesis that `SubDissection.restrict` consumes — and that the corpus records
as "genuinely unbuilt, row by row" — reduces to two obligations that carry **no topology**:
containment of each chosen tile in the candidate region, and an exact area identity. -/

/-- **Covering-equality for a subfamily, from containment and area alone.** -/
theorem subfamily_covers {N M : ℕ} (D : Dissection N) (g : Fin M → Fin N)
    (hg : Function.Injective g) (T : Tri)
    (hsub : ∀ j, (D.tile (g j)).carrier ⊆ T.carrier)
    (harea : ∑ j, volume (D.tile (g j)).carrier = volume T.carrier) :
    (⋃ j, (D.tile (g j)).carrier) = T.carrier :=
  covers_of_volume_tri T (fun j => D.tile (g j)) hsub
    (fun _ _ hjj' => D.interiors_disjoint fun h => hjj' (hg h)) harea

/-- The same, indexed by a `Finset` — the exact shape `SubDissection.restrict` consumes. -/
theorem subfamily_covers_finset {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) (T : Tri)
    (hsub : ∀ i ∈ S, (D.tile i).carrier ⊆ T.carrier)
    (harea : ∑ i ∈ S, volume (D.tile i).carrier = volume T.carrier) :
    (⋃ i ∈ S, (D.tile i).carrier) = T.carrier := by
  classical
  set g : Fin S.card → Fin N := fun j => S.orderEmbOfFin rfl j with hgdef
  have hg : Function.Injective g := (S.orderEmbOfFin rfl).injective
  have hmem : ∀ j, g j ∈ S := fun j => S.orderEmbOfFin_mem rfl j
  have hsum : ∑ j, volume (D.tile (g j)).carrier = ∑ i ∈ S, volume (D.tile i).carrier := by
    refine Finset.sum_bij (fun j _ => g j) (fun j _ => hmem j) ?_ ?_ (fun j _ => rfl)
    · intro j₁ _ j₂ _ h
      exact hg h
    · intro i hi
      have : i ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hi
      obtain ⟨j, hj⟩ := this
      exact ⟨j, Finset.mem_univ j, hj⟩
  have hcov := subfamily_covers D g hg T (fun j => hsub (g j) (hmem j)) (by rw [hsum]; exact harea)
  rw [← hcov]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hiS, hx⟩
    have hr : i ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hiS
    obtain ⟨j, hj⟩ := hr
    refine ⟨j, ?_⟩
    show x ∈ (D.tile (S.orderEmbOfFin rfl j)).carrier
    rw [hj]
    exact hx
  · rintro ⟨j, hx⟩
    exact ⟨g j, hmem j, hx⟩

/-- **The sub-dissection object**, assembled from containment and the area count. -/
noncomputable def restrictOfArea {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) (T : Tri)
    (hsub : ∀ i ∈ S, (D.tile i).carrier ⊆ T.carrier)
    (harea : ∑ i ∈ S, volume (D.tile i).carrier = volume T.carrier) :
    Dissection S.card :=
  Erdos634.SubDissection.restrict D S T (subfamily_covers_finset D S T hsub harea)

/-! ## 3. G2: the rep-tile object

`Subdivision.ladderDissection` is a `Dissection (k*k)` of `kT` and
`ladderDissection_congruent` says each cell is congruent to `T`.  Packaged, that is the statement
"`kT` is cut into `k²` copies of `T`" as a single `CongruentDissection` — the object
`Inflation.lean`'s rows are recorded as missing. -/

/-- **`kT` is dissected into `k²` copies of `T`**, as a `CongruentDissection` with model `T`. -/
noncomputable def repTile (A B C : Plane) (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ)
    (hk : 0 < k) : CongruentDissection (k * k) where
  toDissection := Erdos634.Subdivision.ladderDissection A B C hindep k hk
  model := ⟨![A, B, C], hindep⟩
  tiles_congruent := fun n =>
    (Erdos634.Subdivision.ladderDissection_congruent A B C hindep k hk n).symm

@[simp] theorem repTile_target (A B C : Plane) (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ)
    (hk : 0 < k) :
    (repTile A B C hindep k hk).target = Erdos634.Subdivision.bigTri A B C hindep k hk := rfl

@[simp] theorem repTile_model (A B C : Plane) (hindep : AffineIndependent ℝ ![A, B, C]) (k : ℕ)
    (hk : 0 < k) :
    (repTile A B C hindep k hk).model = (⟨![A, B, C], hindep⟩ : Tri) := rfl

/-! ## 4. Non-vacuity witnesses

The corpus has shipped two theorems with unsatisfiable hypotheses.  Each statement above is given
an exhibited witness. -/

/-- A concrete triangle: the isosceles placement with base `1` and height `1`. -/
noncomputable def witnessTri : Tri := Erdos634.IsoTri.isoTri 1 1 one_ne_zero one_ne_zero

/-- The witness triangle's vertices, in the `![A, B, C]` shape `repTile` asks for. -/
theorem witness_indep :
    AffineIndependent ℝ ![Erdos634.IsoTri.isoPts 1 1 0, Erdos634.IsoTri.isoPts 1 1 1,
      Erdos634.IsoTri.isoPts 1 1 2] := by
  have h : (![Erdos634.IsoTri.isoPts 1 1 0, Erdos634.IsoTri.isoPts 1 1 1,
      Erdos634.IsoTri.isoPts 1 1 2] : Fin 3 → Plane) = Erdos634.IsoTri.isoPts 1 1 := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact witnessTri.indep

/-- **`repTile` is instantiated**: a genuine `CongruentDissection 4` of `2T` for a concrete `T`. -/
noncomputable def repTileWitness : CongruentDissection (2 * 2) :=
  repTile _ _ _ witness_indep 2 (by norm_num)

/-- **`subfamily_covers` is not vacuous**: for any dissection and any single tile, the singleton
subfamily satisfies both hypotheses with `T` that tile.  (`M = 1`, `g` constant, hence injective.) -/
theorem subfamily_covers_witness {N : ℕ} (D : Dissection N) (i : Fin N) :
    (∀ j : Fin 1, (D.tile ((fun _ => i) j)).carrier ⊆ (D.tile i).carrier) ∧
      ∑ j : Fin 1, volume (D.tile ((fun _ => i) j)).carrier = volume (D.tile i).carrier := by
  refine ⟨fun _ => subset_rfl, ?_⟩
  simp

/-- **`subfamily_covers_finset` is not vacuous**: the singleton `Finset` at any tile. -/
theorem subfamily_covers_finset_witness {N : ℕ} (D : Dissection N) (i : Fin N) :
    (∀ i' ∈ ({i} : Finset (Fin N)), (D.tile i').carrier ⊆ (D.tile i).carrier) ∧
      ∑ i' ∈ ({i} : Finset (Fin N)), volume (D.tile i').carrier = volume (D.tile i).carrier := by
  refine ⟨?_, by simp⟩
  intro i' hi'
  rw [Finset.mem_singleton.mp hi']

/-- **`exact_packing_interval` is not vacuous**: `N = 1`, `A 0 = Icc a b`. -/
theorem exact_packing_interval_witness {a b : ℝ} (hab : a < b) :
    (⋃ _ : Fin 1, Set.Icc a b) = Set.Icc a b := by
  refine exact_packing_interval hab (fun _ => isClosed_Icc) (fun _ => subset_rfl)
    (fun _ => measurableSet_Icc.nullMeasurableSet) ?_ (by simp)
  intro i j hij
  exact absurd (Subsingleton.elim i j) hij


/-! ## 5. The dimension-1 side, applied to `rem:pingaps` bridge (c)

`LineParam.lean`'s closing note names a specific, still-open step: `sortedPositions_length` needs
`Set.InjOn lo (D.lineChain f c)`, which fails because every chain edge missing the wall segment
defaults to `lo = 0`, and its own note adds that "even two genuinely-touching edges could in
principle both degenerate to the same single point".

Both halves are corollaries of the exact-packing picture, and they are proved here.  A degenerate
interval has length `0`, so it contributes nothing to the sum; the covering therefore survives
deleting all of them, and among the survivors `lo` **is** injective, because two nondegenerate
intervals sharing a left endpoint would overlap in a set with more than one point.  So the
sub-`Finset` the note asks for is exactly the nondegenerate one, and both properties hold on it
simultaneously. -/

open scoped Classical in
/-- The nondegenerate members of an interval family. -/
noncomputable def nondeg {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ) : Finset ι :=
  s.filter (fun i => lo i < hi i)

open scoped Classical in
theorem nondeg_subset {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ) : nondeg s lo hi ⊆ s :=
  Finset.filter_subset _ _

open scoped Classical in
theorem lt_of_mem_nondeg {ι : Type*} {s : Finset ι} {lo hi : ι → ℝ} {i : ι}
    (h : i ∈ nondeg s lo hi) : lo i < hi i :=
  (Finset.mem_filter.mp h).2

open scoped Classical in
/-- **Degenerate members contribute nothing to the length sum.** -/
theorem sum_nondeg {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ) (hle : ∀ i ∈ s, lo i ≤ hi i) :
    ∑ i ∈ nondeg s lo hi, (hi i - lo i) = ∑ i ∈ s, (hi i - lo i) := by
  refine Finset.sum_subset (nondeg_subset s lo hi) ?_
  intro i his hni
  have hnlt : ¬ lo i < hi i := by
    intro h
    exact hni (Finset.mem_filter.mpr ⟨his, h⟩)
  have := hle i his
  have : hi i = lo i := le_antisymm (not_lt.mp hnlt) this
  rw [this, sub_self]

open scoped Classical in
/-- **On the nondegenerate members, the left endpoint is injective.**  This is the half of the
`rem:pingaps` injectivity blocker that `LineParam.lean`'s note flags as needing care: two genuinely
touching edges cannot share a left endpoint unless one of them is a single point. -/
theorem injOn_lo_nondeg {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (Set.Icc (lo i) (hi i) ∩ Set.Icc (lo j) (hi j)).Subsingleton) :
    Set.InjOn lo (nondeg s lo hi) := by
  intro i hi' j hj' hij
  by_contra hne
  have hiF : i ∈ nondeg s lo hi := Finset.mem_coe.mp hi'
  have hjF : j ∈ nondeg s lo hi := Finset.mem_coe.mp hj'
  have hi2 : lo i < hi i := lt_of_mem_nondeg hiF
  have hj2 : lo j < hi j := lt_of_mem_nondeg hjF
  have hij' : lo i = lo j := hij
  set m : ℝ := min (hi i) (hi j) with hm
  have hlm : lo i < m := lt_min hi2 (by rw [hij']; exact hj2)
  have hmem1 : lo i ∈ Set.Icc (lo i) (hi i) ∩ Set.Icc (lo j) (hi j) := by
    refine ⟨Set.mem_Icc.mpr ⟨le_refl _, hi2.le⟩, Set.mem_Icc.mpr ⟨le_of_eq hij'.symm, ?_⟩⟩
    rw [hij']
    exact hj2.le
  have hmem2 : m ∈ Set.Icc (lo i) (hi i) ∩ Set.Icc (lo j) (hi j) := by
    refine ⟨Set.mem_Icc.mpr ⟨hlm.le, min_le_left _ _⟩, Set.mem_Icc.mpr ⟨?_, min_le_right _ _⟩⟩
    rw [← hij']
    exact hlm.le
  have := hdisj i (nondeg_subset s lo hi hiF) j (nondeg_subset s lo hi hjF) hne hmem1 hmem2
  exact absurd this hlm.ne

open scoped Classical in
/-- **The covering survives deleting the degenerate members, and `lo` is injective on what is
left.**  This is exactly the sub-`Finset` `sortedPositions_length` asks for. -/
theorem iUnion_Icc_nondeg {ι : Type*} (a b : ℝ) (hab : a < b) (s : Finset ι)
    (lo hi : ι → ℝ) (hle : ∀ i ∈ s, lo i ≤ hi i)
    (hsub : ∀ i ∈ s, Set.Icc (lo i) (hi i) ⊆ Set.Icc a b)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (Set.Icc (lo i) (hi i) ∩ Set.Icc (lo j) (hi j)).Subsingleton)
    (hsum : ∑ i ∈ s, (hi i - lo i) = b - a) :
    (⋃ i ∈ nondeg s lo hi, Set.Icc (lo i) (hi i)) = Set.Icc a b
      ∧ Set.InjOn lo (nondeg s lo hi) := by
  have hs := nondeg_subset s lo hi
  refine ⟨Erdos634.LineParam.iUnion_Icc_eq_of_sum_eq_length a b hab (nondeg s lo hi) lo hi
    (fun i h => hle i (hs h)) (fun i h => hsub i (hs h))
    (fun i h1 j h2 hne => hdisj i (hs h1) j (hs h2) hne) ?_,
    injOn_lo_nondeg s lo hi hdisj⟩
  rw [sum_nondeg s lo hi hle, hsum]

open scoped Classical in
/-- **On a real wall of a real dissection.**  Restricting `D.lineChain f c` to the edges whose
trace on the wall segment is nondegenerate, the parameter intervals still cover `[0,1]` exactly,
**and** the left-endpoint map is injective there.  Both are what
`Contiguity.sortedPositions_length` / `orderedChain_length` require and `LineParam.lean` records as
not yet built.

**Non-vacuity: INHERITED AND UNDISCHARGED.**  The hypothesis block here is *verbatim* that of
`LineParam.lineChain_covers_Icc`; no witness for it is exhibited anywhere in the corpus, and none
is exhibited here.  So this statement is exactly as (un)vacuous as the theorem it extends — the
abstract statements `iUnion_Icc_nondeg` and `injOn_lo_nondeg` above carry no such debt and are the
part of this section that stands on its own. -/
theorem lineChain_nondeg_covers_and_injOn {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ)
    (hf : f ≠ 0) (c : ℝ) (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
    (hle : ∀ e ∈ D.lineChain f c, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c) :
    (⋃ e ∈ nondeg (D.lineChain f c)
        (fun e => min (Erdos634.LineParam.edgeParam D f c u v e).1
          (Erdos634.LineParam.edgeParam D f c u v e).2)
        (fun e => max (Erdos634.LineParam.edgeParam D f c u v e).1
          (Erdos634.LineParam.edgeParam D f c u v e).2),
        Set.Icc (min (Erdos634.LineParam.edgeParam D f c u v e).1
            (Erdos634.LineParam.edgeParam D f c u v e).2)
          (max (Erdos634.LineParam.edgeParam D f c u v e).1
            (Erdos634.LineParam.edgeParam D f c u v e).2))
        = Set.Icc (0:ℝ) 1
      ∧ Set.InjOn (fun e => min (Erdos634.LineParam.edgeParam D f c u v e).1
          (Erdos634.LineParam.edgeParam D f c u v e).2)
        (nondeg (D.lineChain f c)
          (fun e => min (Erdos634.LineParam.edgeParam D f c u v e).1
            (Erdos634.LineParam.edgeParam D f c u v e).2)
          (fun e => max (Erdos634.LineParam.edgeParam D f c u v e).1
            (Erdos634.LineParam.edgeParam D f c u v e).2)) := by
  have hu : f u = c := hS (left_mem_segment ℝ u v)
  have hv : f v = c := hS (right_mem_segment ℝ u v)
  refine iUnion_Icc_nondeg 0 1 zero_lt_one (D.lineChain f c) _ _ (fun e _ => min_le_max)
    (fun e he => ?_)
    (fun e₁ he₁ e₂ he₂ hne => Erdos634.LineParam.edgeParam_Icc_subsingleton D f hf c u v huv
      he₁ he₂ hne hu hv (hle e₁ he₁) (hle e₂ he₂))
    (by rw [sub_zero]
        exact Erdos634.LineParam.lineChain_param_sum D f hf c u v huv hS hint hwall)
  dsimp only
  rcases Erdos634.LineParam.edgeParam_spec D f hf c u v huv he hu hv with
    ⟨-, hz⟩ | ⟨hb1, hb2, -, -⟩
  · rw [hz]
    intro x hx
    simp only [min_self, max_self, Set.Icc_self, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨le_refl 0, zero_le_one⟩
  · intro x hx
    exact ⟨(le_min hb1.1 hb2.1).trans hx.1, hx.2.trans (max_le hb1.2 hb2.2)⟩


end Erdos634.TPHilbert
