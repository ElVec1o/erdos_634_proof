import Mathlib.Tactic
import Erdos634.Dissection
import Erdos634.EdgeChain

/-!
# WallChain.lean — G3, interior form: each side of a wall segment is an edge chain

`EdgeChain.lean` proves the exactly-once chain along the *boundary* of the target.  The chord
machinery (`ChordInterface.FarSide`, `RogueChord`'s input (i), `RogueMirror`'s straddled-segment
obligation) consumes the same statement along *interior* segments: for a segment `S` on the line
`{f = c}`, strictly inside the target, that meets no tile's interior (a **wall** — e.g. any
segment made of tile edges), each of the two sides of `S` presents a chain of whole tile edges
covering `S` exactly once.

* `Dissection.edge_point_not_interior` — a non-vertex point of a tile edge lies in no tile's
  interior: **segments made of tile edges are walls**, so the wall hypothesis below is
  dischargeable for every chord the papers use.
* `Dissection.lineChain f c` — the tile edges lying on `{f = c}` whose tile is in `{f ≤ c}`:
  the *near-side chain* of the line.  The far-side chain is `lineChain (−f) (−c)`.
* `Dissection.wall_cover` — every non-vertex point of the open wall segment lies on a near-side
  chain edge.  (Route: the tile found at `x` is not interior — wall — and not exterior, so `x` is
  on one of its edges; pushing along the segment direction must stay out of the tile's interior,
  which forces the edge onto the line by `Tri.mem_interior_of_cross_pos`; if that tile is on the
  far side, `Dissection.second_tile_at_edge_point` produces the tile on the near side, and two
  far-side tiles at once would violate `no_second_tile_same_side` for `−f`.)
* `Dissection.wall_partition` — the near-side chain's traces on `S` cover `S` exactly once:
  `∑ μH¹(edge ∩ S) = μH¹ S`.
* `Dissection.wall_two_sided` — **both sides at once**: near- and far-side chains each partition
  `S`, so the two sides' totals agree — the equal-length input of the residue lemmas
  (`WallStraddle`), with the per-side partition being the `FarSide`-class covering.

Breakpoints of either chain are tiling vertices by `Dissection.chain_breakpoint_vertex`
(EdgeChain.lean), whose hypotheses the `lineChain` fields supply.

Everything proved; no `sorry`, no new axioms.
-/

namespace Erdos634.Geometry

open MeasureTheory Set

/-! ## Walls made of tile edges -/

/-- A convex-hull bound: a triangle all of whose vertices satisfy `f ≤ c` lies in `{f ≤ c}`. -/
theorem Tri.carrier_subset_halfplane (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (h : ∀ i, f (T.pts i) ≤ c) : ∀ y ∈ T.carrier, f y ≤ c := by
  intro y hy
  rw [Tri.carrier] at hy
  have hsub : convexHull ℝ (Set.range T.pts) ⊆ {z | f z ≤ c} := by
    refine convexHull_min ?_ ?_
    · rintro z ⟨i, rfl⟩
      exact h i
    · intro p hp q hq a b ha hb hab
      simp only [Set.mem_setOf_eq] at hp hq ⊢
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have habc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
      have h1 : a * f p ≤ a * c := mul_le_mul_of_nonneg_left hp ha
      have h2 : b * f q ≤ b * c := mul_le_mul_of_nonneg_left hq hb
      linarith
  exact hsub hy

/-- **A frontier point of one tile is interior to no other.**  A point of tile `j`'s carrier that
is not interior to tile `j` (e.g.\ any point of an edge) lies in no tile's interior: interior
points of `j` accumulate at it along a segment from an interior point, so a ball inside another
tile's interior would meet `interior (tile j)`, violating `interiors_disjoint`. -/
theorem Dissection.carrier_point_not_interior {N : ℕ} (D : Dissection N)
    {j : Fin N} {x : Plane} (hx : x ∈ (D.tile j).carrier) :
    ∀ i, i ≠ j → x ∉ interior (D.tile i).carrier := by
  intro i hij hi
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hi
  obtain ⟨y₀, hy₀⟩ := (D.tile j).interior_nonempty
  by_cases hyx : y₀ ∈ Metric.ball x r
  · exact Set.disjoint_left.mp (D.interiors_disjoint hij) (hball hyx) hy₀
  · have hd : r ≤ ‖y₀ - x‖ := by
      rw [Metric.mem_ball, dist_eq_norm] at hyx
      push_neg at hyx
      exact hyx
    have hdpos : 0 < ‖y₀ - x‖ := lt_of_lt_of_le hr hd
    set t := r / (2 * ‖y₀ - x‖) with htdef
    have htpos : 0 < t := by positivity
    have htlt : t < 1 := by
      rw [htdef]
      rw [div_lt_one (by positivity)]
      linarith
    set z := x + t • (y₀ - x) with hzdef
    have hz₁ : z ∈ openSegment ℝ x y₀ := by
      rw [openSegment_eq_image' ℝ x y₀]
      exact ⟨t, ⟨htpos, htlt⟩, rfl⟩
    have hz₂ : z ∈ interior (D.tile j).carrier := by
      have hseg : openSegment ℝ y₀ x ⊆ interior (D.tile j).carrier :=
        (D.tile j).convex.openSegment_interior_closure_subset_interior hy₀
          (subset_closure hx)
      rw [openSegment_symm ℝ x y₀] at hz₁
      exact hseg hz₁
    have hz₃ : z ∈ interior (D.tile i).carrier := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : z - x = t • (y₀ - x) := by rw [hzdef]; abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have h2 : t * ‖y₀ - x‖ = r / 2 := by
        rw [htdef]; field_simp
      rw [h2]; linarith
    exact Set.disjoint_left.mp (D.interiors_disjoint hij) hz₃ hz₂

/-- **Tile edges are walls.**  A point of a tile edge lies in no tile's interior — with no
vertex exclusion.  So the wall hypothesis of the chain theorems holds at *every* point of any
segment made of tile edges. -/
theorem Dissection.edge_point_not_interior {N : ℕ} (D : Dissection N)
    {j : Fin N} {k : Fin 3} {x : Plane} (hx : x ∈ (D.tile j).edge k) :
    ∀ i, x ∉ interior (D.tile i).carrier := by
  intro i hi
  by_cases hij : i = j
  · subst hij
    have hz := (D.tile i).coord_eq_zero_of_mem_edge k hx
    exact absurd hz (ne_of_gt ((D.tile i).interior_coord_pos hi (k + 2)))
  · exact D.carrier_point_not_interior ((D.tile j).edge_subset_carrier k hx) i hij hi

/-! ## The direction step: motion along the segment -/

/-- A point of an open segment can move both ways along it. -/
theorem openSegment_two_sided {u₁ u₂ x : Plane} (hx : x ∈ openSegment ℝ u₁ u₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| < ε₀ → x + ε • (u₂ - u₁) ∈ openSegment ℝ u₁ u₂ := by
  rw [openSegment_eq_image' ℝ u₁ u₂] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨min t (1 - t), lt_min ht.1 (by linarith [ht.2]), fun ε hε => ?_⟩
  rw [openSegment_eq_image' ℝ u₁ u₂]
  refine ⟨t + ε, ⟨?_, ?_⟩, ?_⟩
  · have h1 : |ε| < t := lt_of_lt_of_le hε (min_le_left _ _)
    have h2 := abs_lt.mp h1
    linarith [h2.1]
  · have h1 : |ε| < 1 - t := lt_of_lt_of_le hε (min_le_right _ _)
    have h2 := abs_lt.mp h1
    linarith [h2.2]
  · show u₁ + (t + ε) • (u₂ - u₁) = u₁ + t • (u₂ - u₁) + ε • (u₂ - u₁)
    rw [add_smul]
    abel

/-- **The edge through a wall point is forced onto the wall's line.**  At an edge-interior point
`x` of a tile with `f x = c`, if the cross of the tile's left edge direction with a direction `w`
of the line (`f w = 0`, `w ≠ 0`) vanishes, the edge's endpoints lie on `{f = c}` and the third
vertex is strictly off it. -/
theorem Tri.edge_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    (hfx : f x = c) {w : Plane} (hw0 : w ≠ 0) (hfw : f w = 0)
    (hcross : cross (T.leftDir (m + 1)) w = 0) :
    f (T.pts (m + 1)) = c ∧ f (T.pts (m + 2)) = c ∧ f (T.pts m) ≠ c := by
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero (T.leftDir_ne_zero (m + 1)) hcross
  have hτne : τ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hτ
    exact hw0 hτ
  have hfdir : f (T.leftDir (m + 1)) = 0 := by
    have h1 : f w = τ * f (T.leftDir (m + 1)) := by rw [hτ, map_smul, smul_eq_mul]
    rw [hfw] at h1
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h hτne
    · exact h
  have hidx : (m + 1) + 1 = m + 2 := by fin_cases m <;> rfl
  have hPQ : f (T.pts (m + 2)) = f (T.pts (m + 1)) := by
    rcases T.leftDir_eq_or (m + 1) with h | h
    · have h2 := hfdir
      rw [h, hidx, map_sub] at h2
      linarith
    · have h2 := hfdir
      rw [h, hidx, map_neg, map_sub] at h2
      linarith
  have hxe := T.mem_edge_of_coord_zero hm ho
  rw [Tri.edge, hidx] at hxe
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hxe
  have hfP : f (T.pts (m + 1)) = c := by
    have h1 : a * f (T.pts (m + 1)) + b * f (T.pts (m + 2)) = c := by
      rw [← hfx, ← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hPQ] at h1
    have h2 : (a + b) * f (T.pts (m + 1)) = c := by rw [add_mul]; linarith
    rw [hab, one_mul] at h2
    exact h2
  have hfQ : f (T.pts (m + 2)) = c := by rw [hPQ, hfP]
  refine ⟨hfP, hfQ, fun hfm => ?_⟩
  have hall : ∀ i, f (T.pts i) = c := by
    intro i
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    rcases h3 i m with rfl | rfl | rfl
    · exact hfm
    · exact hfP
    · exact hfQ
  exact two_vertices_on_line T f c hf hall

/-! ## The line chain -/

open Classical in
/-- **The near-side chain of the line `{f = c}`**: the tile edges with both endpoints on the line
and the whole tile in the half-plane `{f ≤ c}`.  The far-side chain is `lineChain (−f) (−c)`. -/
noncomputable def Dissection.lineChain {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e =>
    f ((D.tile e.1).pts e.2) = c ∧ f ((D.tile e.1).pts (e.2 + 1)) = c
      ∧ ∀ i, f ((D.tile e.1).pts i) ≤ c

theorem Dissection.mem_lineChain {N : ℕ} {D : Dissection N} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    {e : Fin N × Fin 3} :
    e ∈ D.lineChain f c ↔
      f ((D.tile e.1).pts e.2) = c ∧ f ((D.tile e.1).pts (e.2 + 1)) = c
        ∧ ∀ i, f ((D.tile e.1).pts i) ≤ c := by
  classical
  simp [Dissection.lineChain]

/-- A chain edge lies on the line. -/
theorem Dissection.lineChain_edge_subset {N : ℕ} (D : Dissection N)
    {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  intro y hy
  rw [Tri.edge] at hy
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hy
  rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h1, h2,
    ← add_mul, hab, one_mul]

/-! ## The cover -/

/-- **Wall cover, one side.**  Every non-vertex point of an open wall segment lies on an edge of
the near-side chain. -/
theorem Dissection.wall_cover {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (hS : segment ℝ u₁ u₂ ⊆ {y | f y = c})
    (hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier)
    {x : Plane} (hx : x ∈ openSegment ℝ u₁ u₂) (hxv : x ∉ D.vertexSet) :
    ∃ e ∈ D.lineChain f c, x ∈ (D.tile e.1).edge e.2 := by
  classical
  have hnv := D.notMem_vertexSet hxv
  have hxint : x ∈ interior D.target.carrier := hint hx
  have hxtar : x ∈ D.target.carrier := interior_subset hxint
  have hfx : f x = c := hS (openSegment_subset_segment ℝ u₁ u₂ hx)
  have hw0 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hfw : f (u₂ - u₁) = 0 := by
    have h1 : f u₁ = c := hS (left_mem_segment ℝ u₁ u₂)
    have h2 : f u₂ = c := hS (right_mem_segment ℝ u₁ u₂)
    rw [map_sub, h1, h2, sub_self]
  obtain ⟨j₀, hj₀⟩ : ∃ j, x ∈ (D.tile j).carrier := by
    have h1 := hxtar
    rw [← D.covers] at h1
    exact Set.mem_iUnion.mp h1
  rcases (D.tile j₀).classify (hnv j₀) with hpos | ⟨m₀, hm₀, ho₀⟩ | ⟨m₀, hneg⟩
  · obtain ⟨r, hr, hsub'⟩ := (D.tile j₀).ball_subset_of_pos hpos
    exact absurd (mem_interior.mpr ⟨Metric.ball x r, hsub', Metric.isOpen_ball,
      Metric.mem_ball_self hr⟩) (hwall x hx j₀)
  · -- x is on an edge of tile j₀; the edge must be parallel to the segment
    have hcr : cross ((D.tile j₀).leftDir (m₀ + 1)) (u₂ - u₁) = 0 := by
      by_contra hc
      obtain ⟨ε₀, hε₀, hmove⟩ := openSegment_two_sided hx
      rcases lt_or_gt_of_ne hc with hneg' | hpos'
      · have hpos'' : 0 < cross ((D.tile j₀).leftDir (m₀ + 1)) (-(u₂ - u₁)) := by
          rw [← neg_one_smul ℝ (u₂ - u₁), cross_smul_right]
          linarith
        obtain ⟨ε₁, hε₁, hpush⟩ := (D.tile j₀).mem_interior_of_cross_pos hm₀ ho₀ hpos''
        set ε := min ε₀ ε₁ / 2 with hεdef
        have hεpos : 0 < ε := by
          rw [hεdef]; have := lt_min hε₀ hε₁; linarith
        have hlt₁ : ε < ε₁ := by
          rw [hεdef]
          have h2 := min_le_right ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have hlt₀ : ε < ε₀ := by
          rw [hεdef]
          have h2 := min_le_left ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have h1 : x + ε • -(u₂ - u₁) ∈ interior (D.tile j₀).carrier := hpush ε hεpos hlt₁
        have h2 : x + ε • -(u₂ - u₁) ∈ openSegment ℝ u₁ u₂ := by
          have h3 : x + ε • -(u₂ - u₁) = x + (-ε) • (u₂ - u₁) := by
            rw [smul_neg, neg_smul]
          rw [h3]
          apply hmove
          rw [abs_neg, abs_of_pos hεpos]
          exact hlt₀
        exact absurd h1 (hwall _ h2 j₀)
      · obtain ⟨ε₁, hε₁, hpush⟩ := (D.tile j₀).mem_interior_of_cross_pos hm₀ ho₀ hpos'
        set ε := min ε₀ ε₁ / 2 with hεdef
        have hεpos : 0 < ε := by
          rw [hεdef]; have := lt_min hε₀ hε₁; linarith
        have hlt₁ : ε < ε₁ := by
          rw [hεdef]
          have h2 := min_le_right ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have hlt₀ : ε < ε₀ := by
          rw [hεdef]
          have h2 := min_le_left ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have h1 : x + ε • (u₂ - u₁) ∈ interior (D.tile j₀).carrier := hpush ε hεpos hlt₁
        have h2 : x + ε • (u₂ - u₁) ∈ openSegment ℝ u₁ u₂ := by
          apply hmove
          rw [abs_of_pos hεpos]
          exact hlt₀
        exact absurd h1 (hwall _ h2 j₀)
    obtain ⟨hfP, hfQ, hfm⟩ := (D.tile j₀).edge_on_line f c hf hm₀ ho₀ hfx hw0 hfw hcr
    have hxe : x ∈ (D.tile j₀).edge (m₀ + 1) := (D.tile j₀).mem_edge_of_coord_zero hm₀ ho₀
    have hidx : ∀ m : Fin 3, (m + 1) + 1 = m + 2 := by decide
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    rcases lt_or_gt_of_ne hfm with hlt | hgt
    · refine ⟨(j₀, m₀ + 1), ?_, hxe⟩
      rw [Dissection.mem_lineChain]
      refine ⟨hfP, by rw [hidx m₀]; exact hfQ, ?_⟩
      intro i
      rcases h3 i m₀ with rfl | rfl | rfl
      · exact hlt.le
      · exact hfP.le
      · exact hfQ.le
    · -- tile j₀ is on the far side: fetch the near-side tile
      have hN := D.pos
      obtain ⟨R, hR, hRt'⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
      have hRt : Metric.ball x R ⊆ D.target.carrier := hRt'.trans interior_subset
      obtain ⟨j₁, hne, hOn⟩ := D.second_tile_at_edge_point hN hnv hR hRt ⟨m₀, hm₀, ho₀⟩
      obtain ⟨m₁, hm₁, ho₁⟩ := hOn
      obtain ⟨c₀, hc₀neg, hc₀⟩ := D.leftDir_antiparallel (Ne.symm hne) hm₀ ho₀ hm₁ ho₁
      have hcr₁ : cross ((D.tile j₁).leftDir (m₁ + 1)) (u₂ - u₁) = 0 := by
        rw [hc₀, cross_smul_left, hcr, mul_zero]
      obtain ⟨hfP₁, hfQ₁, hfm₁⟩ := (D.tile j₁).edge_on_line f c hf hm₁ ho₁ hfx hw0 hfw hcr₁
      have hxe₁ : x ∈ (D.tile j₁).edge (m₁ + 1) := (D.tile j₁).mem_edge_of_coord_zero hm₁ ho₁
      rcases lt_or_gt_of_ne hfm₁ with hlt₁ | hgt₁
      · refine ⟨(j₁, m₁ + 1), ?_, hxe₁⟩
        rw [Dissection.mem_lineChain]
        refine ⟨hfP₁, by rw [hidx m₁]; exact hfQ₁, ?_⟩
        intro i
        rcases h3 i m₁ with rfl | rfl | rfl
        · exact hlt₁.le
        · exact hfP₁.le
        · exact hfQ₁.le
      · -- both tiles strictly on the far side: impossible
        exfalso
        have hle₀ : ∀ y ∈ (D.tile j₀).carrier, (-f) y ≤ -c := by
          apply (D.tile j₀).carrier_subset_halfplane
          intro i
          simp only [LinearMap.neg_apply]
          rcases h3 i m₀ with rfl | rfl | rfl
          · linarith
          · linarith [hfP.le, hfP.ge]
          · linarith [hfQ.le, hfQ.ge]
        have hle₁ : ∀ y ∈ (D.tile j₁).carrier, (-f) y ≤ -c := by
          apply (D.tile j₁).carrier_subset_halfplane
          intro i
          simp only [LinearMap.neg_apply]
          rcases h3 i m₁ with rfl | rfl | rfl
          · linarith
          · linarith [hfP₁.le, hfP₁.ge]
          · linarith [hfQ₁.le, hfQ₁.ge]
        have hfx' : (-f) x = -c := by
          simp only [LinearMap.neg_apply, hfx]
        have hf' : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
        exact D.no_second_tile_same_side (Ne.symm hne) (-f) (-c) hf' hle₀ hle₁ hfx'
          hm₀ ho₀ hm₁ ho₁
  · rw [(D.tile j₀).carrier_eq_nonneg_coord] at hj₀
    exact absurd (hj₀ m₀) (not_le.mpr hneg)

/-! ## The partition -/

/-- **G3, interior form, one side: the near-side chain covers a wall segment exactly once.**
The traces of the near-side chain edges on `S` are pairwise at-most-a-point and their
`μH¹`-lengths sum to `μH¹ S`. -/
theorem Dissection.wall_partition {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (hS : segment ℝ u₁ u₂ ⊆ {y | f y = c})
    (hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) (segment ℝ u₁ u₂) := by
  classical
  have hclseg : IsClosed (segment ℝ u₁ u₂) := by
    rw [segment_eq_image ℝ u₁ u₂]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  apply sum_hausdorff_of_partition (D.lineChain f c)
    (fun e => (D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂) (segment ℝ u₁ u₂)
    (D.vertexSet ∪ {u₁, u₂})
    (D.vertexSet_finite.union ((Set.finite_singleton u₂).insert u₁))
  · exact fun e _ => (((D.tile e.1).isClosed_edge e.2).inter hclseg).measurableSet
  · intro e₁ h₁ e₂ h₂ hne
    have hsub : ((D.tile e₁.1).edge e₁.2 ∩ segment ℝ u₁ u₂)
        ∩ ((D.tile e₂.1).edge e₂.2 ∩ segment ℝ u₁ u₂)
        ⊆ (D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2 :=
      fun y hy => ⟨hy.1.1, hy.2.1⟩
    refine Set.Subsingleton.anti ?_ hsub
    obtain ⟨hP₁, hQ₁, hle₁⟩ := Dissection.mem_lineChain.mp h₁
    obtain ⟨hP₂, hQ₂, hle₂⟩ := Dissection.mem_lineChain.mp h₂
    exact D.sameside_edges_subsingleton f c hf hne
      ((D.tile e₁.1).carrier_subset_halfplane f c hle₁)
      ((D.tile e₂.1).carrier_subset_halfplane f c hle₂)
      (D.lineChain_edge_subset h₁) (D.lineChain_edge_subset h₂)
  · exact fun e _ => Set.inter_subset_right
  · intro y hy
    obtain ⟨hyS, hyF⟩ := hy
    rw [Set.mem_union, not_or] at hyF
    obtain ⟨hyv, hyends⟩ := hyF
    have hy1 : u₁ ≠ y := fun h => hyends (by rw [← h]; exact Set.mem_insert _ _)
    have hy2 : u₂ ≠ y := fun h => hyends (by rw [← h]; simp)
    have hyopen : y ∈ openSegment ℝ u₁ u₂ :=
      mem_openSegment_of_ne_left_right hy1 hy2 hyS
    obtain ⟨e, he, hye⟩ := D.wall_cover f c hf hu hS hint hwall hyopen hyv
    exact Set.mem_iUnion₂.mpr ⟨e, he, hye, hyS⟩

/-- **G3, interior form, both sides.**  A wall segment is covered exactly once from each side:
the near-side chain (`f ≤ c`) and the far-side chain (`−f ≤ −c`) both partition it, so in
particular the two sides' totals agree — the equal-length input of the residue lemmas, with the
per-side partition being the `FarSide`-class covering statement. -/
theorem Dissection.wall_two_sided {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (hS : segment ℝ u₁ u₂ ⊆ {y | f y = c})
    (hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier) :
    (∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) (segment ℝ u₁ u₂))
    ∧ (∑ e ∈ D.lineChain (-f) (-c),
        (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) (segment ℝ u₁ u₂)) := by
  refine ⟨D.wall_partition f c hf hu hS hint hwall, ?_⟩
  refine D.wall_partition (-f) (-c) (fun h => hf (neg_eq_zero.mp h)) hu ?_ hint hwall
  intro y hy
  have h1 := hS hy
  simp only [Set.mem_setOf_eq] at h1 ⊢
  simp [h1]

/-! ## The per-edge instantiation: a tile edge's two sides -/

/-- Every tile edge lies on the level line of an explicit nonzero functional: `crossL` of its
direction. -/
theorem Tri.edge_line (T : Tri) (k : Fin 3) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ ∀ y ∈ T.edge k, f y = c := by
  have hne : T.pts (k + 1) - T.pts k ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h1 : k + 1 = k := T.indep.injective h
    have h2 : ∀ m : Fin 3, m + 1 ≠ m := by decide
    exact h2 k h1
  refine ⟨crossL (T.pts (k + 1) - T.pts k),
    cross (T.pts (k + 1) - T.pts k) (T.pts k), crossL_ne_zero hne, ?_⟩
  intro y hy
  rw [Tri.edge] at hy
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hy
  have hPP' : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1))
      = cross (T.pts (k + 1) - T.pts k) (T.pts k) := by
    have h1 : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1) - T.pts k) = 0 := cross_self _
    rw [cross_sub_right] at h1
    linarith
  rw [crossL_apply, ← hcomb, cross_add_right, cross_smul_right, cross_smul_right, hPP',
    ← add_mul, hab, one_mul]

/-- **The two sides of an interior tile edge are each an exactly-once chain of whole tile
edges.**  For a tile edge whose open segment lies inside the target, there is a supporting
functional of its line such that both the near-side chain and the far-side chain cover the edge
exactly once, in the `μH¹`-length sense.  All wall hypotheses are discharged:
`edge_point_not_interior` makes any tile edge a wall.

This is the `FarSide`/`RogueChord`-class covering statement (obligation G3, interior form) for a
single tile edge; chords made of several collinear tile edges follow by applying
`wall_two_sided` to the composite segment with the same discharge. -/
theorem Dissection.edge_two_sided {N : ℕ} (D : Dissection N) (j : Fin N) (k : Fin 3)
    (hint : openSegment ℝ ((D.tile j).pts k) ((D.tile j).pts (k + 1))
      ⊆ interior D.target.carrier) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ y ∈ (D.tile j).edge k, f y = c) ∧
      (∑ e ∈ D.lineChain f c,
          (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
            ((D.tile e.1).edge e.2 ∩ (D.tile j).edge k)
        = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile j).edge k))
      ∧ (∑ e ∈ D.lineChain (-f) (-c),
          (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
            ((D.tile e.1).edge e.2 ∩ (D.tile j).edge k)
        = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile j).edge k)) := by
  obtain ⟨f, c, hf, hline⟩ := (D.tile j).edge_line k
  have hu : (D.tile j).pts k ≠ (D.tile j).pts (k + 1) := by
    intro h
    have h1 : k = k + 1 := (D.tile j).indep.injective h
    have h2 : ∀ m : Fin 3, m ≠ m + 1 := by decide
    exact h2 k h1
  have hS : segment ℝ ((D.tile j).pts k) ((D.tile j).pts (k + 1)) ⊆ {y | f y = c} := by
    intro y hy
    exact hline y hy
  have hwall : ∀ y ∈ openSegment ℝ ((D.tile j).pts k) ((D.tile j).pts (k + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    exact D.edge_point_not_interior
      (openSegment_subset_segment ℝ _ _ hy : y ∈ (D.tile j).edge k)
  obtain ⟨h₁, h₂⟩ := D.wall_two_sided f c hf hu hS hint hwall
  exact ⟨f, c, hf, hline, h₁, h₂⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Dissection.edge_point_not_interior
#print axioms Erdos634.Geometry.Dissection.wall_cover
#print axioms Erdos634.Geometry.Dissection.wall_partition
#print axioms Erdos634.Geometry.Dissection.wall_two_sided
#print axioms Erdos634.Geometry.Dissection.edge_two_sided
