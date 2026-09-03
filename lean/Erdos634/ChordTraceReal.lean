import Erdos634.Dissection

/-!
# Towards a real `ChordTrace`: the sign trichotomy

Erdős #634. `ChordDecomp.ChordTrace` (the `(3,7)`-specific chord-trace data behind
`prop:chorddecomp`/`prop:straddle`) carries its geometry as hypotheses ("the obligation is named
rather than [discharged]", per that file's own header) because nothing built the general fact a
real `Dissection` needs: for an *internal* chord line (not a supporting line of the whole target —
tiles can straddle it), which tiles straddle and which touch it only in a face.

The existing `tile_contact_face`/`contacts_cover_side` machinery in `Dissection.lean` does not
apply here: it assumes the tile already lies weakly on one side of the line (`hle`), which is
exactly false for a straddling tile. This file supplies the missing case split.

`Tri.sign_trichotomy` is the first piece: any tile against any line either lies weakly below it,
weakly above it, or has vertices strictly on both sides (straddles).

`isSegment_of_convex_inter_hyperplane` is the second piece, and the one a real `ChordTrace` needs
directly: any convex compact set lying entirely on one line (in particular, a tile's intersection
with a chord it doesn't straddle, or — via the straddle case — the trace itself once its own
convexity and compactness are established) is *exactly* the segment between two of its own points,
never a more complicated shape. Proved by parametrizing the line through a nonzero vector `v` in
`ker f` (rank-nullity gives `finrank (ker f) = 1` for `f ≠ 0` on the plane), pulling `S`'s convexity
and compactness back along `t ↦ x0 + t•v` to a convex compact — hence closed-interval — subset of
`ℝ`, and pushing the interval's endpoints back through the parametrization.

`straddle_trace_disjoint` is the third piece: two *different* straddling tiles' traces on the same
line meet in at most one point. This was the genuinely open half of the disjointness question —
`Dissection.sameside_edges_subsingleton` (pre-existing) already handles flush-flush disjointness,
but only when both tiles lie weakly on one side of the line, which is false for a straddler. The
proof needs no case-split on which pair of edges the line crosses: if `x ≠ y` were both common to
two straddlers' traces, `Tri.straddle_midpoint_interior` shows their midpoint is interior to *both*
tiles (every barycentric coordinate is the average of its values at `x` and `y`, both `≥ 0`, and a
coordinate can only average to `0` if it vanishes at both — which would put `x, y` on the same edge
line, and `Tri.straddle_no_edge_on_line` rules out that edge lying on the chord line, so the two
lines meet in the single point forced by `eq_of_mem_line_of_agree`, giving `x = y`, contradiction).
This directly contradicts `Dissection.interiors_disjoint`.

Still needed for a real `ChordTrace`: the multi-tile covering/length-additivity bookkeeping across
a whole chord (`contacts_cover_side`/`length_sum_of_cover` already supply the fully general
covering and summation machinery; what remains is combining them with the segment/disjointness
facts here for the mixed flush-straddle case) — not yet attempted.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry

namespace Erdos634.ChordTraceReal

/-- **A tile's sign relative to an external line, from its vertices alone.** Since `T.carrier` is
the convex hull of its three vertices and `f` is linear, `f`'s extreme values over the whole tile
are attained at vertices: `T` lies weakly below `f = c` iff every vertex does. This is the
foundational classification `ChordDecomp`'s straddle/flush dichotomy needs, for a general internal
line -- not just a supporting line of the whole target, which is all the existing
`tile_contact_face`/`contacts_cover_side` machinery handles. -/
theorem Tri.le_iff_forall_vertices_le (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ x ∈ T.carrier, f x ≤ c) ↔ ∀ i, f (T.pts i) ≤ c := by
  constructor
  · intro h i; exact h _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
  · intro h x hx
    rw [Tri.carrier] at hx
    refine convexHull_min ?_ (convex_halfSpace_le f.isLinear c) hx
    rintro y ⟨i, rfl⟩; exact h i

/-- The `≥` mirror of `Tri.le_iff_forall_vertices_le`. -/
theorem Tri.ge_iff_forall_vertices_ge (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ x ∈ T.carrier, c ≤ f x) ↔ ∀ i, c ≤ f (T.pts i) := by
  constructor
  · intro h i; exact h _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
  · intro h x hx
    rw [Tri.carrier] at hx
    refine convexHull_min ?_ (convex_halfSpace_ge f.isLinear c) hx
    rintro y ⟨i, rfl⟩; exact h i

/-- **The sign trichotomy.** Any tile, against any external line, either lies weakly below it,
weakly above it, or straddles it (has a vertex strictly on each side). The first two folds in the
case where the tile only touches the line in a face. -/
theorem Tri.sign_trichotomy (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ x ∈ T.carrier, f x ≤ c) ∨ (∀ x ∈ T.carrier, c ≤ f x)
      ∨ ((∃ i, f (T.pts i) < c) ∧ (∃ j, c < f (T.pts j))) := by
  by_cases hlo : ∀ i, f (T.pts i) ≤ c
  · exact Or.inl ((Tri.le_iff_forall_vertices_le T f c).mpr hlo)
  · by_cases hhi : ∀ i, c ≤ f (T.pts i)
    · exact Or.inr (Or.inl ((Tri.ge_iff_forall_vertices_ge T f c).mpr hhi))
    · push Not at hlo hhi
      exact Or.inr (Or.inr ⟨hhi, hlo⟩)

/-- **A tile's trace on a line is convex.** `T.carrier ∩ {f = c}` is an intersection of two convex
sets (a triangle and an affine hyperplane), hence convex — the first ingredient
`isSegment_of_convex_inter_hyperplane` needs to turn a straddling tile's trace into an honest
segment. -/
theorem Tri.convex_inter_hyperplane (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    Convex ℝ (T.carrier ∩ {x | f x = c}) := by
  apply Convex.inter (convex_convexHull ℝ _)
  intro x hx y hy a b _ _ hab
  simp only [Set.mem_setOf_eq] at *
  rw [map_add, map_smul, map_smul, hx, hy, smul_eq_mul, smul_eq_mul]
  linear_combination c * hab

/-- The trace is compact: a closed subset (the line is closed) of a compact set (the tile). -/
theorem Tri.isCompact_inter_hyperplane (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    IsCompact (T.carrier ∩ {x | f x = c}) :=
  T.isCompact.inter_right (isClosed_eq (AffineMap.continuous_of_finiteDimensional f.toAffineMap) continuous_const)

/-- **`ker f` is `1`-dimensional for `f ≠ 0` on the plane.** Rank-nullity: `f`'s range is all of
`ℝ` (dimension `1`) once it hits a single nonzero value, and `Plane` has dimension `2`. -/
theorem ker_finrank_one (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    Module.finrank ℝ (LinearMap.ker f) = 1 := by
  have hrange : Module.finrank ℝ (LinearMap.range f) = 1 := by
    have hsurj : Function.Surjective f := by
      obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
        by_contra h; push Not at h; exact hf (LinearMap.ext fun z => by simp [h z])
      intro y
      exact ⟨(y / f x) • x, by simp [map_smul, smul_eq_mul]; field_simp⟩
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp [Module.finrank_self]
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hplane : Module.finrank ℝ Plane = 2 := by simp
  omega

/-- **A convex compact subset of a line is a segment.** Given `S` convex and compact, lying
entirely on the line `f = c` (`f ≠ 0`), `S` equals `segment ℝ p q` for two of its own points `p, q`
— never a more complicated shape. This is the geometric heart of a real `ChordTrace`: any tile's
trace on a chord line is an honest single interval, so its "length" is unambiguous.

Proved by parametrizing the line through a nonzero `v ∈ ker f` (from `ker_finrank_one`), pulling
`S`'s convexity and compactness back along `t ↦ x0 + t • v` to a convex compact subset of `ℝ`
(hence a closed interval `Icc (sInf S') (sSup S')`, by the standard real-line fact), and pushing
the interval's endpoints back through the parametrization. -/
theorem isSegment_of_convex_inter_hyperplane
    {S : Set Plane} (hconv : Convex ℝ S) (hcpt : IsCompact S)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) (hSf : ∀ x ∈ S, f x = c) (x0 : Plane) (hx0 : x0 ∈ S) :
    ∃ p q, p ∈ S ∧ q ∈ S ∧ S = segment ℝ p q := by
  have hker1 := ker_finrank_one f hf
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker f) := by omega
  obtain ⟨v0, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  set v : Plane := v0.1 with hvdef
  have hvne : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hspan : ∀ w : LinearMap.ker f, ∃ t : ℝ, t • v0 = w :=
    (finrank_eq_one_iff_of_nonzero' v0 hv0).mp hker1
  set φ : ℝ → Plane := fun t => x0 + t • v with hφdef
  set S' : Set ℝ := φ ⁻¹' S with hS'def
  have hconv' : Convex ℝ S' := by
    intro a ha b hb s t hs ht hst
    show x0 + (s • a + t • b) • v ∈ S
    have heq : x0 + (s • a + t • b) • v = s • (x0 + a • v) + t • (x0 + b • v) := by
      have hst1 : s + t = 1 := hst
      have hrw : s • (x0 + a • v) + t • (x0 + b • v)
          = (s + t) • x0 + (s • a + t • b) • v := by module
      rw [hrw, hst1, one_smul]
    rw [heq]
    exact hconv ha hb hs ht hst
  have hcont : Continuous φ := by fun_prop
  have hbdd : Bornology.IsBounded S' := by
    obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall 0
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℝ)]
    refine ⟨R / ‖v‖ + ‖x0‖ / ‖v‖, fun t ht => ?_⟩
    have hmemS : x0 + t • v ∈ S := ht
    have hball := hR hmemS
    simp only [Metric.mem_closedBall, dist_zero_right] at hball ⊢
    have htv : ‖t • v‖ ≤ ‖x0 + t • v‖ + ‖x0‖ := by
      have h1 := norm_add_le (x0 + t • v) (-x0)
      rw [show x0 + t • v + -x0 = t • v by abel, norm_neg] at h1
      exact h1
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    rw [norm_smul, Real.norm_eq_abs] at htv
    rw [Real.norm_eq_abs]
    have hsum : |t| * ‖v‖ ≤ R + ‖x0‖ := by linarith [htv, hball]
    rw [show R / ‖v‖ + ‖x0‖ / ‖v‖ = (R + ‖x0‖) / ‖v‖ from (add_div R ‖x0‖ ‖v‖).symm]
    exact (le_div_iff₀ hvpos).mpr hsum
  have hclosed : IsClosed S' := hcpt.isClosed.preimage hcont
  have hcpt' : IsCompact S' := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩
  have hne' : S'.Nonempty := ⟨0, by show x0 + (0 : ℝ) • v ∈ S; simpa using hx0⟩
  have hbdd_below : BddBelow S' := hcpt'.bddBelow
  have hbdd_above : BddAbove S' := hcpt'.bddAbove
  have hinf_mem : sInf S' ∈ S' := hcpt'.isClosed.csInf_mem hne' hbdd_below
  have hsup_mem : sSup S' ∈ S' := hcpt'.isClosed.csSup_mem hne' hbdd_above
  have hab : sInf S' ≤ sSup S' := csInf_le hbdd_below hsup_mem
  have hSicc : S' = Set.Icc (sInf S') (sSup S') := by
    apply Set.Subset.antisymm
    · intro x hx; exact ⟨csInf_le hbdd_below hx, le_csSup hbdd_above hx⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hseg := hconv'.segment_subset hinf_mem hsup_mem
      rw [segment_eq_Icc hab] at hseg
      exact hseg ⟨hx1, hx2⟩
  refine ⟨φ (sInf S'), φ (sSup S'), hinf_mem, hsup_mem, ?_⟩
  have hSimg : S = φ '' S' := by
    apply Set.Subset.antisymm
    · intro y hy
      have hfy : f y = c := hSf y hy
      have hfx0 : f x0 = c := hSf x0 hx0
      have hmemker : y - x0 ∈ LinearMap.ker f := by
        simp only [LinearMap.mem_ker, map_sub, hfy, hfx0, sub_self]
      obtain ⟨t, ht⟩ := hspan ⟨y - x0, hmemker⟩
      have hty : y - x0 = t • v := congrArg Subtype.val ht |>.symm
      refine ⟨t, ?_, ?_⟩
      · show φ t ∈ S; show x0 + t • v ∈ S; rw [← hty]; simpa using hy
      · show φ t = y; show x0 + t • v = y; rw [← hty]; abel
    · rintro y ⟨t, ht, rfl⟩; exact ht
  rw [hSimg]
  ext y
  simp only [Set.mem_image, segment]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht1 : sInf S' ≤ t := (hSicc ▸ ht : t ∈ Set.Icc (sInf S') (sSup S')).1
    have ht2 : t ≤ sSup S' := (hSicc ▸ ht : t ∈ Set.Icc (sInf S') (sSup S')).2
    by_cases heq : sInf S' = sSup S'
    · refine ⟨1, 0, by norm_num, le_refl _, by norm_num, ?_⟩
      have htis : t = sInf S' := le_antisymm (heq ▸ ht2) ht1
      simp only [hφdef]
      rw [htis]; module
    · have hlt : sInf S' < sSup S' := lt_of_le_of_ne hab heq
      have hne : sSup S' - sInf S' ≠ 0 := by linarith
      refine ⟨(sSup S' - t) / (sSup S' - sInf S'), (t - sInf S') / (sSup S' - sInf S'), ?_, ?_, ?_, ?_⟩
      · apply div_nonneg <;> linarith
      · apply div_nonneg <;> linarith
      · field_simp; ring
      · simp only [hφdef]
        have hcoef : (sSup S' - t) / (sSup S' - sInf S') * sInf S'
            + (t - sInf S') / (sSup S' - sInf S') * sSup S' = t := by
          field_simp; ring
        have hsum : (sSup S' - t) / (sSup S' - sInf S') + (t - sInf S') / (sSup S' - sInf S') = 1 := by
          field_simp; ring
        have hgoal : ((sSup S' - t) / (sSup S' - sInf S')) • (x0 + sInf S' • v)
              + ((t - sInf S') / (sSup S' - sInf S')) • (x0 + sSup S' • v)
            = (((sSup S' - t) / (sSup S' - sInf S')) + ((t - sInf S') / (sSup S' - sInf S'))) • x0
              + (((sSup S' - t) / (sSup S' - sInf S')) * sInf S'
                + ((t - sInf S') / (sSup S' - sInf S')) * sSup S') • v := by
          module
        rw [hgoal, hsum, hcoef, one_smul]
  · rintro ⟨a, b, ha, hb, hab1, hy⟩
    have hlow : a * sInf S' + b * sInf S' = sInf S' := by rw [← add_mul, hab1, one_mul]
    have hhigh : a * sSup S' + b * sSup S' = sSup S' := by rw [← add_mul, hab1, one_mul]
    refine ⟨a * sInf S' + b * sSup S', ?_, ?_⟩
    · apply hSicc.symm ▸ (Set.mem_Icc.mpr ⟨?_, ?_⟩)
      · linarith [mul_le_mul_of_nonneg_left hab hb]
      · linarith [mul_le_mul_of_nonneg_left hab ha]
    · simp only [hφdef]
      rw [← hy]
      have hgoal : a • (x0 + sInf S' • v) + b • (x0 + sSup S' • v)
          = (a + b) • x0 + (a * sInf S' + b * sSup S') • v := by module
      rw [hgoal, hab1, one_smul]

theorem Tri.straddle_no_edge_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hlo : ∃ i, f (T.pts i) < c) (hhi : ∃ j, c < f (T.pts j)) (k : Fin 3) :
    f (T.pts (k + 1)) ≠ c ∨ f (T.pts (k + 2)) ≠ c := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have hcases : ∀ k m : Fin 3, m = k ∨ m = k + 1 ∨ m = k + 2 := by decide
  have hcases' := hcases k
  rcases lt_trichotomy (f (T.pts k)) c with hk | hk | hk
  · have hall : ∀ m, f (T.pts m) ≤ c := by
      intro m; rcases hcases' m with rfl | rfl | rfl
      · exact hk.le
      · exact h1.le
      · exact h2.le
    exact absurd (hall j) (not_le.mpr hj)
  · have hall : ∀ m, f (T.pts m) ≤ c := by
      intro m; rcases hcases' m with rfl | rfl | rfl
      · exact hk.le
      · exact h1.le
      · exact h2.le
    exact absurd (hall j) (not_le.mpr hj)
  · have hall : ∀ m, c ≤ f (T.pts m) := by
      intro m; rcases hcases' m with rfl | rfl | rfl
      · exact hk.le
      · exact h1.ge
      · exact h2.ge
    exact absurd (hall i) (not_le.mpr hi)

/-- Positive barycentric coordinates put a point in the interior. -/
theorem Tri.mem_interior_of_pos (T : Tri) {x : Plane} (hpos : ∀ i, 0 < T.basis.coord i x) :
    x ∈ interior T.carrier := by
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
  have hxball : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hballopen : IsOpen (Metric.ball x r) := Metric.isOpen_ball
  exact interior_mono hsub (hballopen.interior_eq.symm ▸ hxball)

/-- **A vanishing affine functional at two distinct points is constant on their whole line.**
`ker f` is `1`-dimensional whenever `f.linear ≠ 0`; any point sharing `f`'s value with two distinct
points `x, y` on that level set lies on the line through them (parametrized via `ker f`'s
generator), and an affine map is determined on a line by two of its values. -/
theorem eq_of_mem_line_of_agree {g : Plane →ᵃ[ℝ] ℝ} (hg : g.linear ≠ 0)
    {x y z : Plane} (hxy : x ≠ y) (hgx : g x = g y) (hgz : g z = g x)
    {f : Plane →ᵃ[ℝ] ℝ} (hfx : f x = f y) : f z = f x := by
  have hker1 := ChordTraceReal.ker_finrank_one g.linear hg
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker g.linear) := by omega
  obtain ⟨v0, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  set v : Plane := v0.1 with hvdef
  have hspan : ∀ w : LinearMap.ker g.linear, ∃ t : ℝ, t • v0 = w :=
    (finrank_eq_one_iff_of_nonzero' v0 hv0).mp hker1
  have hyxker : y -ᵥ x ∈ LinearMap.ker g.linear := by
    show g.linear (y -ᵥ x) = 0
    rw [AffineMap.linearMap_vsub]
    simp [hgx]
  have hzxker : z -ᵥ x ∈ LinearMap.ker g.linear := by
    show g.linear (z -ᵥ x) = 0
    rw [AffineMap.linearMap_vsub]
    simp [hgz]
  obtain ⟨ty, hty⟩ := hspan ⟨y -ᵥ x, hyxker⟩
  obtain ⟨tz, htz⟩ := hspan ⟨z -ᵥ x, hzxker⟩
  have hty' : y -ᵥ x = ty • v := congrArg Subtype.val hty |>.symm
  have htz' : z -ᵥ x = tz • v := congrArg Subtype.val htz |>.symm
  have htyne : ty ≠ 0 := by
    intro h; apply hxy
    have : y -ᵥ x = 0 := by rw [hty', h, zero_smul]
    exact (vsub_eq_zero_iff_eq.mp this).symm ▸ rfl
  have hz_eq : z = AffineMap.lineMap x y (tz / ty) := by
    rw [AffineMap.lineMap_apply]
    have : (tz / ty) • (y -ᵥ x) = z -ᵥ x := by
      rw [hty', htz', smul_smul]
      congr 1
      field_simp
    rw [this]
    exact (vsub_vadd z x).symm
  rw [hz_eq, f.apply_lineMap, hfx]
  simp

/-- **The midpoint of two distinct points on a straddler's chord trace is interior.** -/
theorem Tri.straddle_midpoint_interior (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hlo : ∃ i, f (T.pts i) < c) (hhi : ∃ j, c < f (T.pts j))
    {x y : Plane} (hx : x ∈ T.carrier) (hfx : f x = c) (hy : y ∈ T.carrier) (hfy : f y = c)
    (hxy : x ≠ y) :
    midpoint ℝ x y ∈ interior T.carrier := by
  apply Tri.mem_interior_of_pos T
  intro k
  have hxk : 0 ≤ T.basis.coord k x := by
    have h := hx; rw [T.carrier_eq_nonneg_coord] at h; exact h k
  have hyk : 0 ≤ T.basis.coord k y := by
    have h := hy; rw [T.carrier_eq_nonneg_coord] at h; exact h k
  have havg : (T.basis.coord k) (midpoint ℝ x y)
      = midpoint ℝ (T.basis.coord k x) (T.basis.coord k y) := AffineMap.map_midpoint _ x y
  rw [havg]
  rcases eq_or_lt_of_le hxk with hxk0 | hxk0
  · rcases eq_or_lt_of_le hyk with hyk0 | hyk0
    · exfalso
      have hfline : (T.basis.coord k : Plane →ᵃ[ℝ] ℝ).linear ≠ 0 := T.coord_linear_ne_zero k
      have hgx : (T.basis.coord k) x = (T.basis.coord k) y := by rw [← hxk0, ← hyk0]
      have hffx : f.toAffineMap x = f.toAffineMap y := hfx.trans hfy.symm
      have h1 := Tri.straddle_no_edge_on_line T f c hlo hhi k
      have hk1ne : (k : Fin 3) ≠ k + 1 := by fin_cases k <;> decide
      have hk2ne : (k : Fin 3) ≠ k + 2 := by fin_cases k <;> decide
      have hpts : ∀ m : Fin 3, T.pts m = (T.basis : Fin 3 → Plane) m := fun _ => rfl
      have hz1 : (T.basis.coord k) (T.pts (k + 1)) = (T.basis.coord k) x := by
        rw [hpts, ← hxk0]
        exact T.basis.coord_apply_ne hk1ne
      have hz2 : (T.basis.coord k) (T.pts (k + 2)) = (T.basis.coord k) x := by
        rw [hpts, ← hxk0]
        exact T.basis.coord_apply_ne hk2ne
      have hres1 : f.toAffineMap (T.pts (k + 1)) = f.toAffineMap x :=
        eq_of_mem_line_of_agree hfline hxy hgx hz1 (f := f.toAffineMap) hffx
      have hres2 : f.toAffineMap (T.pts (k + 2)) = f.toAffineMap x :=
        eq_of_mem_line_of_agree hfline hxy hgx hz2 (f := f.toAffineMap) hffx
      simp only [LinearMap.coe_toAffineMap] at hres1 hres2
      rw [hfx] at hres1 hres2
      rcases h1 with h | h
      · exact h hres1
      · exact h hres2
    · rw [midpoint_eq_smul_add, smul_eq_mul]
      have hsum : 0 < T.basis.coord k x + T.basis.coord k y := by linarith
      have h2 : (0:ℝ) < ⅟(2:ℝ) := by norm_num
      exact mul_pos h2 hsum
  · rw [midpoint_eq_smul_add, smul_eq_mul]
    have hsum : 0 < T.basis.coord k x + T.basis.coord k y := by linarith
    have h2 : (0:ℝ) < ⅟(2:ℝ) := by norm_num
    exact mul_pos h2 hsum

/-- **Two straddling tiles' traces on the same line meet in at most one point.** If `x ≠ y` were
both common to two different straddlers' traces, their midpoint would be interior to *both* tiles
(`straddle_midpoint_interior`, applied to each), contradicting `D.interiors_disjoint`. -/
theorem straddle_trace_disjoint {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {i j : Fin N} (hij : i ≠ j)
    (hloi : ∃ a, f ((D.tile i).pts a) < c) (hhii : ∃ b, c < f ((D.tile i).pts b))
    (hloj : ∃ a, f ((D.tile j).pts a) < c) (hhij : ∃ b, c < f ((D.tile j).pts b)) :
    (((D.tile i).carrier ∩ {x | f x = c}) ∩ ((D.tile j).carrier ∩ {x | f x = c})).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hxi : x ∈ (D.tile i).carrier := hx.1.1
  have hfxi : f x = c := hx.1.2
  have hyi : y ∈ (D.tile i).carrier := hy.1.1
  have hfyi : f y = c := hy.1.2
  have hmi := Tri.straddle_midpoint_interior (D.tile i) f c hloi hhii hxi hfxi hyi hfyi hxy
  have hxj : x ∈ (D.tile j).carrier := hx.2.1
  have hfxj : f x = c := hx.2.2
  have hyj : y ∈ (D.tile j).carrier := hy.2.1
  have hfyj : f y = c := hy.2.2
  have hmj := Tri.straddle_midpoint_interior (D.tile j) f c hloj hhij hxj hfxj hyj hfyj hxy
  exact (D.interiors_disjoint hij).le_bot ⟨hmi, hmj⟩

end Erdos634.ChordTraceReal
