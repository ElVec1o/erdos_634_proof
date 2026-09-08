import Erdos634.RouteOneStepBridge

/-!
# Tile-interior blocking: the overshoot branch, made a theorem

Erdős #634, `conj:advance` / `rem:route1uniform`, route 1.

`RouteOneStepBridge.escape_flank_advance` carries an undischarged hypothesis `hno`, and its own
docstring names it: *"the exclusion of the overshoot branch `f < length`, which is tile-interior
blocking and is not a theorem anywhere in `lean/`"* (`RouteOneStepBridge.lean:44-45`).  Before this
file, "tile-interior blocking" was prose in `RouteOne.lean:20-24` and nothing else.

**What blocks, exactly.**  `f < (W - V) 0` puts `E`, the point at distance `f` along the wall,
*strictly inside* the serving tile's edge `[V,W]`.  That alone is not a contradiction — a tile may
lay a long edge along the wall, and does, at the end of a march run.  What contradicts is the
escape configuration's own content at `E`: a chord *deviates* from the wall at `E`, i.e. some tile
other than the serving one has points strictly above the wall arbitrarily near `E`.  The serving
tile, being weakly above the wall (`EscapeData.habove`) and having `E` interior to a horizontal
edge, owns a whole upper half-neighbourhood of `E` — every such point is in its *interior* — so the
deviating tile meets it, against `Dissection.interiors_disjoint`.

`upper_nbhd_of_edge_interior` is the half-neighbourhood statement; it is the new geometry.  Its
proof is barycentric: the coordinate opposite the horizontal edge is, on the nose, the height above
the wall divided by the apex height (`coord_apex_height`), so it is positive exactly above the
line; the two coordinates at the edge's endpoints are positive at `E` and stay positive nearby by
continuity of an affine map in finite dimensions.

**What this does and does not close.**  It discharges `hno` from a *named* input — `hdev`, the
deviating tile at `E` — and nothing else.  `hdev` is not derived here: it is the escape word's own
statement that the chord leaves the wall at `E`, and producing it from a hypothetical base-`β`
tiling remains part of `rem:routeoneopen`'s standing attachment obligation, exactly as gap (A)
(`habovei'`, that no tile straddles the wall) remains.  `e = 1` is not closed; the prime case is
not advanced.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.OvershootBlocking

open Erdos634.Geometry Erdos634.RouteOne

/-! ## Index arithmetic in `Fin 3` -/

theorem fin3_shift (a : Fin 3) : a + 1 + 2 = a := by revert a; decide

theorem fin3_succ (a : Fin 3) : a + 1 + 1 = a + 2 := by revert a; decide

theorem fin3_ne (a : Fin 3) : a + 1 ≠ a + 2 := by revert a; decide

theorem fin3_cases (a k : Fin 3) : k = a ∨ k = a + 1 ∨ k = a + 2 := by revert a k; decide

/-! ## The barycentric coordinate opposite a horizontal edge is the height -/

/-- **The apex is strictly above the horizontal edge.**  Weakly above by hypothesis; not level with
it, since two edges at a vertex cannot both be horizontal. -/
theorem apex_above (T : Tri) (a : Fin 3)
    (hy : (T.pts (a + 2) - T.pts (a + 1)) 1 = 0)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - T.pts (a + 1)) 1) :
    0 < (T.pts a - T.pts (a + 1)) 1 := by
  have hmem : T.pts a ∈ T.carrier := by
    rw [Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨a, rfl⟩
  rcases lt_or_eq_of_le (habove _ hmem) with h | h
  · exact h
  · exfalso
    refine not_both_horizontal T (a + 1) ⟨?_, ?_⟩
    · rw [fin3_succ]; exact hy
    · rw [fin3_shift]; exact h.symm

/-- **The coordinate opposite a horizontal edge measures height.**  For every point of the plane,
`coord a` times the apex's height above the edge line equals the point's own height. -/
theorem coord_apex_height (T : Tri) (a : Fin 3)
    (hy : (T.pts (a + 2) - T.pts (a + 1)) 1 = 0) (q : Plane) :
    (q - T.pts (a + 1)) 1 = T.basis.coord a q * ((T.pts a - T.pts (a + 1)) 1) := by
  have hcombo := sub_vertex_eq_combo T (a + 1) q
  rw [fin3_shift, fin3_succ] at hcombo
  have := congrArg (fun v : Plane => v 1) hcombo
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
  rw [this, hy, mul_zero, zero_add]

/-- **Above the line iff the opposite coordinate is positive.** -/
theorem coord_apex_pos (T : Tri) (a : Fin 3)
    (hy : (T.pts (a + 2) - T.pts (a + 1)) 1 = 0)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - T.pts (a + 1)) 1)
    {q : Plane} (hq : 0 < (q - T.pts (a + 1)) 1) :
    0 < T.basis.coord a q := by
  have hA := apex_above T a hy habove
  have h := coord_apex_height T a hy q
  nlinarith [h, hA, hq]

/-! ## The upper half-neighbourhood of an edge-interior point -/

/-- **The two coordinates at the edge's endpoints are positive at an interior point of that
edge.** -/
theorem coords_pos_of_openSegment (T : Tri) (a : Fin 3) {E : Plane}
    (hE : E ∈ openSegment ℝ (T.pts (a + 1)) (T.pts (a + 2))) :
    0 < T.basis.coord (a + 1) E ∧ 0 < T.basis.coord (a + 2) E := by
  obtain ⟨s, t, hs, ht, hst, heq⟩ := hE
  have hlm : E = AffineMap.lineMap (T.pts (a + 1)) (T.pts (a + 2)) t := by
    rw [AffineMap.lineMap_apply, ← heq]
    have hs' : s = 1 - t := by linarith
    rw [hs']
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  have e11 : T.basis.coord (a + 1) (T.pts (a + 1)) = 1 := T.basis.coord_apply_eq _
  have e12 : T.basis.coord (a + 1) (T.pts (a + 2)) = 0 :=
    T.basis.coord_apply_ne (fin3_ne a)
  have e21 : T.basis.coord (a + 2) (T.pts (a + 1)) = 0 :=
    T.basis.coord_apply_ne (Ne.symm (fin3_ne a))
  have e22 : T.basis.coord (a + 2) (T.pts (a + 2)) = 1 := T.basis.coord_apply_eq _
  have h1 := (T.basis.coord (a + 1)).apply_lineMap (T.pts (a + 1)) (T.pts (a + 2)) t
  have h2 := (T.basis.coord (a + 2)).apply_lineMap (T.pts (a + 1)) (T.pts (a + 2)) t
  rw [e11, e12] at h1
  rw [e21, e22] at h2
  rw [hlm]
  constructor
  · rw [h1]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    linarith
  · rw [h2]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    linarith

/-- **An edge-interior point sits on the edge's line.** -/
theorem height_zero_of_openSegment (T : Tri) (a : Fin 3) {E : Plane}
    (hy : (T.pts (a + 2) - T.pts (a + 1)) 1 = 0)
    (hE : E ∈ openSegment ℝ (T.pts (a + 1)) (T.pts (a + 2))) :
    (E - T.pts (a + 1)) 1 = 0 := by
  obtain ⟨s, t, hs, ht, hst, heq⟩ := hE
  have hyc : T.pts (a + 2) 1 - T.pts (a + 1) 1 = 0 := by
    simpa only [PiLp.sub_apply] using hy
  have : E 1 = s * T.pts (a + 1) 1 + t * T.pts (a + 2) 1 := by
    rw [← heq]; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [PiLp.sub_apply, this]
  linear_combination t * hyc + (T.pts (a + 1) 1) * hst

/-- **Tile-interior blocking, the geometry.**  If `E` is interior to an edge of `T` that runs
horizontally, and `T` stays weakly above that edge's line, then a whole upper half-neighbourhood of
`E` lies in the *interior* of `T`. -/
theorem upper_nbhd_of_edge_interior (T : Tri) (a : Fin 3) {E : Plane}
    (hy : (T.pts (a + 2) - T.pts (a + 1)) 1 = 0)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - T.pts (a + 1)) 1)
    (hE : E ∈ openSegment ℝ (T.pts (a + 1)) (T.pts (a + 2))) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : Plane, dist q E < r → 0 < (q - E) 1 →
      q ∈ interior T.carrier := by
  classical
  obtain ⟨hp1, hp2⟩ := coords_pos_of_openSegment T a hE
  have hE0 := height_zero_of_openSegment T a hy hE
  -- continuity of the two edge coordinates
  have hcont : ∀ j : Fin 3, Continuous (T.basis.coord j) := fun j =>
    (T.basis.coord j).continuous_of_finiteDimensional
  have hnhd1 : {q : Plane | 0 < T.basis.coord (a + 1) q} ∈ nhds E :=
    (hcont (a + 1)).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp1)
  have hnhd2 : {q : Plane | 0 < T.basis.coord (a + 2) q} ∈ nhds E :=
    (hcont (a + 2)).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp2)
  obtain ⟨r1, hr1, hs1⟩ := Metric.mem_nhds_iff.mp hnhd1
  obtain ⟨r2, hr2, hs2⟩ := Metric.mem_nhds_iff.mp hnhd2
  refine ⟨min r1 r2, lt_min hr1 hr2, fun q hq hup => ?_⟩
  have hq1 : 0 < T.basis.coord (a + 1) q :=
    hs1 (Metric.mem_ball.mpr (lt_of_lt_of_le hq (min_le_left _ _)))
  have hq2 : 0 < T.basis.coord (a + 2) q :=
    hs2 (Metric.mem_ball.mpr (lt_of_lt_of_le hq (min_le_right _ _)))
  have hqa : 0 < T.basis.coord a q := by
    refine coord_apex_pos T a hy habove ?_
    have hsplit : (q - T.pts (a + 1)) 1 = (q - E) 1 + (E - T.pts (a + 1)) 1 := by
      simp only [PiLp.sub_apply]; ring
    rw [hsplit, hE0, add_zero]; exact hup
  rw [Tri.interior_iff_pos_coord]
  intro k
  rcases fin3_cases a k with rfl | rfl | rfl
  · exact hqa
  · exact hq1
  · exact hq2

/-! ## The blocking contradiction -/

/-- **Tile-interior blocking.**  In a dissection, if `E` is interior to a horizontal edge of the
tile `i`, which keeps weakly above that edge's line, then no *other* tile has points strictly above
the line arbitrarily near `E`.

This is the exclusion the overshoot branch needed.  The hypothesis `hdev` is the deviating chord at
`E`: it is exactly the escape configuration's own content there. -/
theorem overshoot_blocks {N : ℕ} (D : Dissection N) (i k : Fin N) (hki : k ≠ i) (a : Fin 3)
    {E : Plane}
    (hy : ((D.tile i).pts (a + 2) - (D.tile i).pts (a + 1)) 1 = 0)
    (habove : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - (D.tile i).pts (a + 1)) 1)
    (hE : E ∈ openSegment ℝ ((D.tile i).pts (a + 1)) ((D.tile i).pts (a + 2)))
    (hdev : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ (D.tile k).carrier ∧ dist q E < r ∧
      0 < (q - E) 1) :
    False := by
  obtain ⟨r, hr, hsub⟩ := upper_nbhd_of_edge_interior (D.tile i) a hy habove hE
  obtain ⟨q, hqk, hqd, hqup⟩ := hdev r hr
  exact Dissection.not_mem_interior_of_mem D hki hqk (hsub q hqd hqup)

/-! ## From the arithmetic overshoot to the blocked configuration -/

theorem fin3_a1 (m : Fin 3) : m + 2 + 1 = m := by revert m; decide

theorem fin3_a2 (m : Fin 3) : m + 2 + 2 = m + 1 := by revert m; decide

theorem fin3_b1 (m : Fin 3) : m + 1 + 1 = m + 2 := by revert m; decide

theorem fin3_b2 (m : Fin 3) : m + 1 + 2 = m := by revert m; decide

/-- **`E` is interior to the flank edge, when the flank overshoots.**  `V` and `W` are the ends of a
horizontal rightward edge and `E` sits strictly between them in `x`. -/
theorem mem_openSegment_of_overshoot {V W E : Plane}
    (hy : (W - V) 1 = 0) (hEy : (E - V) 1 = 0)
    (hEx0 : 0 < (E - V) 0) (hExlt : (E - V) 0 < (W - V) 0) :
    E ∈ openSegment ℝ V W := by
  have hWx : 0 < (W - V) 0 := lt_trans hEx0 hExlt
  refine mem_openSegment_of_horizontal (t := (E - V) 0 / (W - V) 0) hy hEy
    (div_pos hEx0 hWx) ((div_lt_one hWx).mpr hExlt) ?_
  field_simp

/-- **The overshoot branch is blocked.**  If the serving tile `i` lays a horizontal edge from its
vertex `V` to `W`, keeps weakly above that line, and `E` lies strictly between `V` and `W`, then no
other tile has points strictly above the line arbitrarily near `E`.

`hdev` is the deviating chord at `E`; everything else is the escape configuration as the corpus
already carries it. -/
theorem blocked_of_overshoot {N : ℕ} (D : Dissection N) (i k : Fin N) (hki : k ≠ i)
    (V W E : Plane) (m : Fin 3)
    (hV : (D.tile i).pts m = V)
    (hW : (D.tile i).pts (m + 1) = W ∨ (D.tile i).pts (m + 2) = W)
    (hy : (W - V) 1 = 0)
    (habove : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1)
    (hEy : (E - V) 1 = 0) (hEx0 : 0 < (E - V) 0) (hExlt : (E - V) 0 < (W - V) 0)
    (hdev : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ (D.tile k).carrier ∧ dist q E < r ∧
      0 < (q - E) 1) :
    False := by
  have hseg : E ∈ openSegment ℝ V W := mem_openSegment_of_overshoot hy hEy hEx0 hExlt
  have hVW : (V - W) 1 = 0 := by
    have := hy
    simp only [PiLp.sub_apply] at this ⊢
    linarith
  rcases hW with hW1 | hW2
  · refine overshoot_blocks D i k hki (m + 2) (E := E) ?_ ?_ ?_ hdev
    · rw [fin3_a1, fin3_a2, hV, hW1]; exact hy
    · rw [fin3_a1, hV]; exact habove
    · rw [fin3_a1, fin3_a2, hV, hW1]; exact hseg
  · refine overshoot_blocks D i k hki (m + 1) (E := E) ?_ ?_ ?_ hdev
    · rw [fin3_b1, fin3_b2, hV, hW2]; exact hVW
    · rw [fin3_b1, hW2]
      intro q hq
      have h := habove q hq
      have hyc : W 1 - V 1 = 0 := by simpa only [PiLp.sub_apply] using hy
      simp only [PiLp.sub_apply] at h ⊢
      linarith
    · rw [fin3_b1, fin3_b2, hV, hW2, openSegment_symm]; exact hseg

/-! ## `escape_flank_advance`, with its blocking hypothesis discharged -/

open Erdos634.CertCoord in
/-- **The march advances, given the deviation at `E`.**  This is
`RouteOneStepBridge.escape_flank_advance` with its undischarged `hno` replaced by the escape word's
own content at `E`: a tile other than the serving one carries points strictly above the wall
arbitrarily near `E`.

Nothing else changes.  What was "tile-interior blocking is not a theorem anywhere in `lean/`" is now
`blocked_of_overshoot`; what remains is the attachment of `hdev`, which is not supplied here. -/
theorem escape_flank_advance_of_deviation {N : ℕ} (D : CongruentDissection N)
    (Ed : EscapeData D.toDissection) (f : ℝ) (hf : 2 ≤ f)
    (hmodel : ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
                dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) = {f, f ^ 2 - 1, f ^ 2})
    (E : Plane) (hEy : (E - Ed.V) 1 = 0) (hEx : (E - Ed.V) 0 = f)
    (k : Fin N) (hki : k ≠ Ed.i)
    (hdev : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ (D.tile k).carrier ∧ dist q E < r ∧
      0 < (q - E) 1) :
    ∃ (c : Fin 3) (o : Fin 3), (o = 1 ∨ o = 2) ∧
      (D.tile Ed.i).pts c = Ed.V ∧ (D.tile Ed.i).pts (c + o) = Ed.V + f • mkPt 1 0 := by
  obtain ⟨c, W, hc, hnb, hy, hx, hlen⟩ :=
    Erdos634.RouteOneStepBridge.escape_flank_dichotomy D Ed f hf hmodel
  have hlen' : (W - Ed.V) 0 = f := by
    rcases hlen with h | h
    · exact h
    · exact absurd (blocked_of_overshoot D.toDissection Ed.i k hki Ed.V W E c hc hnb hy
        Ed.habove hEy (by rw [hEx]; linarith) (by rw [hEx]; exact h) hdev) (fun x => x)
  have hWeq : W = Ed.V + f • mkPt 1 0 := Erdos634.RouteOneStepBridge.advance_vector hy hlen'
  rcases hnb with h | h
  · exact ⟨c, 1, Or.inl rfl, hc, by rw [h, hWeq]⟩
  · exact ⟨c, 2, Or.inr rfl, hc, by rw [h, hWeq]⟩

/-! ## A witness: the hypotheses of `upper_nbhd_of_edge_interior` are satisfiable

Rule: a conditional whose hypotheses cannot be met proves nothing.  The half-neighbourhood lemma is
the file's only positive geometric statement, so it is the one that needs a witness.  `wTri` is the
triangle `(0,0), (2,0), (1,1)`; with apex index `2` its edge `(pts 0, pts 1)` is the horizontal
base, the tile sits weakly above it, and `(1,0)` is interior to that edge. -/

open Erdos634.CertCoord in
/-- The witness triangle `(0,0), (2,0), (1,1)`. -/
noncomputable def wTri : Tri := mkTri 0 0 2 0 1 1 (by norm_num [det3])

open Erdos634.CertCoord in
theorem wTri_pts0 : wTri.pts 0 = mkPt 0 0 := rfl

open Erdos634.CertCoord in
theorem wTri_pts1 : wTri.pts 1 = mkPt 2 0 := rfl

open Erdos634.CertCoord in
theorem wTri_pts2 : wTri.pts 2 = mkPt 1 1 := rfl

open Erdos634.CertCoord in
/-- The witness tile keeps weakly above the line of its base. -/
theorem wTri_above (q : Plane) (hq : q ∈ wTri.carrier) : 0 ≤ (q - wTri.pts (2 + 1)) 1 := by
  have hsub : wTri.carrier ⊆ {x : Plane | 0 ≤ x 1} := by
    rw [Erdos634.Geometry.Tri.carrier]
    refine convexHull_min ?_ ?_
    · rintro x ⟨j, rfl⟩
      fin_cases j <;> simp [wTri_pts0, wTri_pts1, wTri_pts2]
    · exact convex_halfSpace_ge (LinearMap.proj 1 |>.comp (EuclideanSpace.equiv (Fin 2) ℝ).toLinearMap
        |>.isLinear) 0
  have h := hsub hq
  have : wTri.pts (2 + 1) = mkPt 0 0 := by
    show wTri.pts 0 = mkPt 0 0
    rfl
  simp only [PiLp.sub_apply, this, mkPt_one, sub_zero]
  exact h

open Erdos634.CertCoord in
/-- `(1,0)` is interior to the witness tile's base edge. -/
theorem wTri_mid : mkPt 1 0 ∈ openSegment ℝ (wTri.pts (2 + 1)) (wTri.pts (2 + 2)) := by
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  show (1/2 : ℝ) • wTri.pts 0 + (1/2 : ℝ) • wTri.pts 1 = mkPt 1 0
  rw [wTri_pts0, wTri_pts1]
  ext j
  fin_cases j <;> simp [mkPt]

open Erdos634.CertCoord in
/-- **The witness.**  Every hypothesis of `upper_nbhd_of_edge_interior` is met by `wTri`, so its
conclusion is not vacuous: a genuine upper half-neighbourhood of `(1,0)` lies in the tile's
interior. -/
theorem upper_nbhd_witness :
    ∃ r : ℝ, 0 < r ∧ ∀ q : Plane, dist q (mkPt 1 0) < r → 0 < (q - mkPt 1 0) 1 →
      q ∈ interior wTri.carrier := by
  refine upper_nbhd_of_edge_interior wTri 2 ?_ wTri_above wTri_mid
  show (wTri.pts 1 - wTri.pts 0) 1 = 0
  rw [wTri_pts0, wTri_pts1]
  simp

end Erdos634.OvershootBlocking
