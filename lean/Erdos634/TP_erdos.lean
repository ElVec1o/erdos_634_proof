import Erdos634.LineParam
import Erdos634.CertCoord
import Erdos634.CertGeom
import Erdos634.ChordOpenSegmentInterior
import Erdos634.BaseSelection

/-!
# TP_erdos — a satisfiability witness for the wall hypothesis block

Erdős #634, room `tileplace`, ERDŐS seat.

`Erdos634.LineParam.lineChain_covers_Icc`, `Geometry.Dissection.wall_partition`,
`wall_cover` and `wall_two_sided` all carry the same hypothesis block

```
(hf : f ≠ 0) (huv : u ≠ v)
(hS   : segment ℝ u v ⊆ {y | f y = c})
(hint : openSegment ℝ u v ⊆ interior D.target.carrier)
(hwall: ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier)
```

and **no witness for it existed anywhere in the corpus**.  Two theorems with unsatisfiable
hypotheses have already been shipped on this project, so this block was a live vacuity risk for
the whole of `WallChain.lean`, `LineParam.lean`, `PinPlumbing.lean`, `IntervalChain.lean`,
`ChordDecomposition*`, `RogueChord`, `RogueMirror`, `ForcedRow`, `InvariantCore`,
`StraightEdgeSums`, `CorridorLowStop` — every consumer of `wall_partition`/`wall_two_sided`.

This file settles it: the block is **satisfiable**, with an explicit `Dissection 2`.

* `wallDissection : Dissection 2` — the right isoceles triangle `(0,0) (2,0) (0,2)` cut by the
  median from `(0,0)` to `(1,1)`, built through `AreaDet.ofDetCertificate`.
* `wallWitness` — all five hypotheses discharged for `f = (x ↦ x₀ - x₁)`, `c = 0`,
  `u = (0,0)`, `v = (1,1)`.
* `lineChain_covers_Icc_witness` — `LineParam.lineChain_covers_Icc` instantiated: its conclusion
  holds *and is non-trivial*, since an empty chain could not cover `Icc 0 1`.
* `wall_partition_witness`, `wall_two_sided_witness` — the same for `WallChain`'s two headline
  theorems.

Two further, independent findings, also proved here:

* `edge_dir_parallel_of_boundary_relint` / `no_straddle_of_transversal` /
  `chord_endpoint_no_straddle` (§7) — the **anti-straddle lemma at a transversal boundary point**:
  a tile edge whose *relative interior* meets a supporting line of the target is parallel to that
  line.  This is `prop:cornerpara`'s "no such edge can straddle" step, which `PAPER_MAP.md`'s
  `prop:cornerpara` row records as *"no such argument is known or has been attempted"*.  §8 gives
  witnesses for its hypotheses, so it is not vacuous.


* `hle_redundant` — `lineChain_covers_Icc`'s hypothesis `hle` is **derivable** from membership in
  `lineChain` itself (`mem_lineChain`'s third field plus `Tri.carrier_subset_halfplane`), so it is
  a redundant hypothesis; `lineChain_covers_Icc'` restates the theorem without it.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TPErdos

open Erdos634.Geometry Erdos634.CertCoord Set

/-! ## 0. `hle` is redundant -/

/-- **`lineChain_covers_Icc`'s `hle` hypothesis is free.**  Membership in `lineChain f c` already
carries "every vertex of the tile satisfies `f ≤ c`", and `Tri.carrier_subset_halfplane` promotes
that to the whole carrier.  So the hypothesis is derivable, not an assumption. -/
theorem hle_redundant {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    ∀ e ∈ D.lineChain f c, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c := by
  intro e he
  exact Tri.carrier_subset_halfplane (D.tile e.1) f c (Dissection.mem_lineChain.mp he).2.2

/-- **`lineChain_covers_Icc` with `hle` removed.** -/
theorem lineChain_covers_Icc' {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) (u v : Plane) (huv : u ≠ v)
    (hS : segment ℝ u v ⊆ {y | f y = c})
    (hint : openSegment ℝ u v ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u v, ∀ i, y ∉ interior (D.tile i).carrier) :
    (⋃ e ∈ D.lineChain f c,
        Icc (min (Erdos634.LineParam.edgeParam D f c u v e).1
              (Erdos634.LineParam.edgeParam D f c u v e).2)
          (max (Erdos634.LineParam.edgeParam D f c u v e).1
              (Erdos634.LineParam.edgeParam D f c u v e).2))
      = Icc (0:ℝ) 1 :=
  Erdos634.LineParam.lineChain_covers_Icc D f hf c u v huv hS hint hwall
    (hle_redundant D f c)

/-! ## 1. The three triangles -/

theorem detT : det3 0 0 2 0 0 2 = 4 := by norm_num [det3]
theorem detT1 : det3 0 0 1 1 2 0 = -2 := by norm_num [det3]
theorem detT2 : det3 0 0 0 2 1 1 = -2 := by norm_num [det3]

/-- The target: the right isoceles triangle `(0,0) (2,0) (0,2)`. -/
noncomputable def wallTarget : Tri := mkTri 0 0 2 0 0 2 (by rw [detT]; norm_num)

/-- The far-side tile: `(0,0) (1,1) (2,0)`. -/
noncomputable def wallTileA : Tri := mkTri 0 0 1 1 2 0 (by rw [detT1]; norm_num)

/-- The near-side tile: `(0,0) (0,2) (1,1)`. -/
noncomputable def wallTileB : Tri := mkTri 0 0 0 2 1 1 (by rw [detT2]; norm_num)

noncomputable def wallTiles : Fin 2 → Tri := ![wallTileA, wallTileB]

/-! ## 2. Containment -/

theorem mem_target {a b : ℝ}
    (h₀ : 0 ≤ det3 a b 2 0 0 2) (h₁ : 0 ≤ det3 0 0 a b 0 2) (h₂ : 0 ≤ det3 0 0 2 0 a b) :
    mkPt a b ∈ wallTarget.carrier :=
  mem_carrier_of_dets (show (0:ℝ) < det3 0 0 2 0 0 2 by rw [detT]; norm_num) h₀ h₁ h₂

theorem A_mem : mkPt 0 0 ∈ wallTarget.carrier :=
  mem_target (by norm_num [det3]) (by norm_num [det3]) (by norm_num [det3])

theorem B_mem : mkPt 2 0 ∈ wallTarget.carrier :=
  mem_target (by norm_num [det3]) (by norm_num [det3]) (by norm_num [det3])

theorem C_mem : mkPt 0 2 ∈ wallTarget.carrier :=
  mem_target (by norm_num [det3]) (by norm_num [det3]) (by norm_num [det3])

theorem M_mem : mkPt 1 1 ∈ wallTarget.carrier :=
  mem_target (by norm_num [det3]) (by norm_num [det3]) (by norm_num [det3])

theorem wallTiles_subset : ∀ i, (wallTiles i).carrier ⊆ wallTarget.carrier := by
  intro i
  refine Erdos634.CertGeom.carrier_subset_of_pts_mem ?_
  intro k
  fin_cases i <;> fin_cases k
  · exact A_mem
  · exact M_mem
  · exact B_mem
  · exact A_mem
  · exact C_mem
  · exact M_mem

/-! ## 3. Disjoint interiors: the median line separates the two tiles -/

/-- The `≥` companion of `CertGeom.le_of_forall_pts_le`. -/
theorem ge_of_forall_pts_ge {t : Tri} (g : Plane →ᵃ[ℝ] ℝ) {c : ℝ} (h : ∀ k, c ≤ g (t.pts k)) :
    ∀ x ∈ t.carrier, c ≤ g x := by
  have hconv : Convex ℝ (g ⁻¹' Set.Ici c) := (convex_Ici c).affine_preimage g
  have hsub : t.carrier ⊆ g ⁻¹' Set.Ici c :=
    convexHull_min (Set.range_subset_iff.mpr h) hconv
  exact fun x hx => hsub hx

/-- The separating functional: `v ↦ v₁ - v₀`, zero exactly on the median line. -/
noncomputable def sepFun : Plane →ᵃ[ℝ] ℝ := Erdos634.CertGeom.lineFun 0 0 1 1

theorem sepFun_ne : (sepFun).linear ≠ 0 :=
  Erdos634.CertGeom.lineFun_linear_ne_zero (Or.inl (by norm_num))

theorem sepFun_pt (x y : ℝ) : sepFun (mkPt x y) = y - x := by
  simp [sepFun, Erdos634.CertGeom.lineFun_apply]

theorem wallTiles_disjoint :
    Pairwise fun i j => Disjoint (interior (wallTiles i).carrier)
      (interior (wallTiles j).carrier) := by
  have hA : ∀ x ∈ wallTileA.carrier, sepFun x ≤ 0 := by
    refine Erdos634.CertGeom.le_of_forall_pts_le sepFun ?_
    intro k
    fin_cases k <;> simp [wallTileA, sepFun_pt]
  have hB : ∀ x ∈ wallTileB.carrier, (0:ℝ) ≤ sepFun x := by
    refine ge_of_forall_pts_ge sepFun ?_
    intro k
    fin_cases k <;> simp [wallTileB, sepFun_pt]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all
  · exact Erdos634.CertGeom.interiors_disjoint_of_separating sepFun sepFun_ne 0 hA hB
  · exact (Erdos634.CertGeom.interiors_disjoint_of_separating sepFun sepFun_ne 0 hA hB).symm

/-! ## 4. The determinant identity, and the dissection -/

theorem wallTiles_det :
    ∑ i, |Erdos634.AreaDet.detTri (wallTiles i)| = |Erdos634.AreaDet.detTri wallTarget| := by
  have h1 : Erdos634.AreaDet.detTri wallTileA = -2 := by
    rw [wallTileA, detTri_mkTri, detT1]
  have h2 : Erdos634.AreaDet.detTri wallTileB = -2 := by
    rw [wallTileB, detTri_mkTri, detT2]
  have h0 : Erdos634.AreaDet.detTri wallTarget = 4 := by
    rw [wallTarget, detTri_mkTri, detT]
  rw [Fin.sum_univ_two, h0]
  show |Erdos634.AreaDet.detTri wallTileA| + |Erdos634.AreaDet.detTri wallTileB| = _
  rw [h1, h2]
  norm_num

/-- **The witness dissection**: `(0,0) (2,0) (0,2)` cut by the median to `(1,1)`. -/
noncomputable def wallDissection : Dissection 2 :=
  Erdos634.AreaDet.ofDetCertificate wallTarget wallTiles
    wallTiles_subset wallTiles_disjoint wallTiles_det

@[simp] theorem wallDissection_target : wallDissection.target = wallTarget := rfl
@[simp] theorem wallDissection_tile : wallDissection.tile = wallTiles := rfl

/-! ## 5. The wall data -/

/-- The linear functional `x ↦ x₀ - x₁`; the median line is `{wallF = 0}`. -/
noncomputable def wallF : Plane →ₗ[ℝ] ℝ where
  toFun v := v 0 - v 1
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem wallF_apply (v : Plane) : wallF v = v 0 - v 1 := rfl

theorem wallF_pt (x y : ℝ) : wallF (mkPt x y) = x - y := by
  simp [wallF_apply]

theorem wallF_ne : wallF ≠ 0 := by
  intro h
  have h2 : wallF (mkPt 2 0) = 0 := by rw [h]; simp
  rw [wallF_pt] at h2
  norm_num at h2

/-- `u = (0,0)`, the target's own corner. -/
noncomputable def wallU : Plane := mkPt 0 0
/-- `v = (1,1)`, the midpoint of the hypotenuse. -/
noncomputable def wallV : Plane := mkPt 1 1

theorem wallU_ne_wallV : wallU ≠ wallV := by
  intro h
  have := congrArg (fun p : Plane => p 0) h
  simp [wallU, wallV, mkPt_zero] at this

theorem wallF_u : wallF wallU = 0 := by rw [wallU, wallF_pt]; norm_num
theorem wallF_v : wallF wallV = 0 := by rw [wallV, wallF_pt]; norm_num

/-- **`hS`.** -/
theorem wall_hS : segment ℝ wallU wallV ⊆ {y | wallF y = 0} := by
  rintro y ⟨a, b, ha, hb, hab, rfl⟩
  simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul, wallF_u, wallF_v]
  ring

/-- **`hwall`.**  The open segment is inside a genuine tile edge, so
`Dissection.edge_point_not_interior` applies. -/
theorem wall_hwall : ∀ y ∈ openSegment ℝ wallU wallV, ∀ i,
    y ∉ interior (wallDissection.tile i).carrier := by
  intro y hy
  have hedge : y ∈ (wallDissection.tile 0).edge 0 := by
    have : (wallDissection.tile 0).edge 0 = segment ℝ wallU wallV := by
      show segment ℝ ((wallTiles 0).pts 0) ((wallTiles 0).pts (0 + 1)) = _
      norm_num [wallTiles, wallTileA, mkTri, wallU, wallV]
    rw [this]
    exact openSegment_subset_segment ℝ _ _ hy
  exact wallDissection.edge_point_not_interior hedge

/-- **`hint`.**  The target straddles the median line, and `(0,0)`, `(1,1)` are two of its own
points on that line, so `Tri.straddle_openSegment_interior` puts the open segment in the
interior. -/
theorem wall_hint : openSegment ℝ wallU wallV ⊆ interior wallDissection.target.carrier := by
  have hlo : ∃ i, wallF (wallTarget.pts i) < 0 := by
    refine ⟨2, ?_⟩
    show wallF (mkPt 0 2) < 0
    rw [wallF_pt]; norm_num
  have hhi : ∃ j, (0:ℝ) < wallF (wallTarget.pts j) := by
    refine ⟨1, ?_⟩
    show (0:ℝ) < wallF (mkPt 2 0)
    rw [wallF_pt]; norm_num
  intro y hy
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  show AffineMap.lineMap wallU wallV s ∈ interior wallTarget.carrier
  exact Erdos634.ChordTraceReal.Tri.straddle_openSegment_interior wallTarget wallF 0 hlo hhi
    (show wallU ∈ wallTarget.carrier from A_mem) wallF_u
    (show wallV ∈ wallTarget.carrier from M_mem) wallF_v
    wallU_ne_wallV hs.1 hs.2

/-! ## 6. The witness, and the instantiations -/

/-- **THE WITNESS.**  All five hypotheses of the wall block, discharged simultaneously for an
explicit `Dissection 2`. -/
theorem wallWitness :
    wallF ≠ 0 ∧ wallU ≠ wallV ∧
    segment ℝ wallU wallV ⊆ {y | wallF y = 0} ∧
    openSegment ℝ wallU wallV ⊆ interior wallDissection.target.carrier ∧
    (∀ y ∈ openSegment ℝ wallU wallV, ∀ i, y ∉ interior (wallDissection.tile i).carrier) :=
  ⟨wallF_ne, wallU_ne_wallV, wall_hS, wall_hint, wall_hwall⟩

/-- **`LineParam.lineChain_covers_Icc` is not vacuous.**  Instantiated at the witness; note the
conclusion forces `lineChain` to be nonempty, since an empty union cannot be `Icc 0 1`. -/
theorem lineChain_covers_Icc_witness :
    (⋃ e ∈ wallDissection.lineChain wallF 0,
        Icc (min (Erdos634.LineParam.edgeParam wallDissection wallF 0 wallU wallV e).1
              (Erdos634.LineParam.edgeParam wallDissection wallF 0 wallU wallV e).2)
          (max (Erdos634.LineParam.edgeParam wallDissection wallF 0 wallU wallV e).1
              (Erdos634.LineParam.edgeParam wallDissection wallF 0 wallU wallV e).2))
      = Icc (0:ℝ) 1 :=
  lineChain_covers_Icc' wallDissection wallF wallF_ne 0 wallU wallV
    wallU_ne_wallV wall_hS wall_hint wall_hwall

/-- **`WallChain.wall_partition` is not vacuous.** -/
theorem wall_partition_witness :
    ∑ e ∈ wallDissection.lineChain wallF 0,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((wallDissection.tile e.1).edge e.2 ∩ segment ℝ wallU wallV)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ wallU wallV) :=
  wallDissection.wall_partition wallF 0 wallF_ne wallU_ne_wallV wall_hS wall_hint wall_hwall

/-- **`WallChain.wall_two_sided` is not vacuous.**  Both sides of the median wall carry a chain
partitioning it, with equal totals. -/
theorem wall_two_sided_witness :
    (∑ e ∈ wallDissection.lineChain wallF 0,
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((wallDissection.tile e.1).edge e.2 ∩ segment ℝ wallU wallV)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ wallU wallV))
    ∧ (∑ e ∈ wallDissection.lineChain (-wallF) (-0),
        (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((wallDissection.tile e.1).edge e.2 ∩ segment ℝ wallU wallV)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          (segment ℝ wallU wallV)) :=
  wallDissection.wall_two_sided wallF 0 wallF_ne wallU_ne_wallV wall_hS wall_hint wall_hwall

/-- **The chain is nonempty** — the sharp corollary: the witness is not the empty-chain
degenerate case. -/
theorem lineChain_nonempty : (wallDissection.lineChain wallF 0).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hcov := lineChain_covers_Icc_witness
  rw [h] at hcov
  simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty] at hcov
  have : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  rw [← hcov] at this
  exact this


/-! ## 7. The anti-straddle lemma at a transversal boundary point

`PAPER_MAP.md`'s `prop:cornerpara` row records, precisely, what closing that proposition needs:

> closing `prop:cornerpara` (if possible at all) needs something specific to the CORNER tile's
> `b`-edge — not a general interior `b`-edge — that rules out straddles there specifically; no such
> argument is known or has been attempted.

The paper's own proof (`erdos-634.tex:751`) does name the mechanism — *"a straddling edge would
extend beyond `P` or beyond `Q` along the line `PQ`, and both `P` and `Q` lie on `∂ABC`, so the
extension leaves `ABC`"* — so what is missing is the formalization, not the idea.  This section
supplies it, in the general form, with no congruence and no corner hypothesis:

**a tile edge whose *relative interior* contains a point of a supporting line of the target must be
parallel to that line.**

Equivalently, contrapositively: at a point where the target's boundary is transversal to a
direction `w`, no tile edge parallel to `w` straddles.  That is exactly the "no straddler at `P`"
step, and it is *local at `P`*: it does not know what the chord is, that the tile is a corner tile,
or that the dissection is congruent. -/

open Erdos634.Geometry in
/-- **A tile edge meeting a supporting line of the target in its relative interior is parallel to
that line.**  Both one-sided pushes off the point stay inside the edge, hence inside the target,
hence on the `≤ c` side; only a direction in the kernel survives both. -/
theorem edge_dir_parallel_of_boundary_relint {N : ℕ} (D : Dissection N) {i : Fin N} {k : Fin 3}
    {x : Plane} (hx : x ∈ openSegment ℝ ((D.tile i).pts k) ((D.tile i).pts (k + 1)))
    (g : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ y ∈ D.target.carrier, g y ≤ c) (hgx : g x = c) :
    g ((D.tile i).pts (k + 1) - (D.tile i).pts k) = 0 := by
  obtain ⟨ε₀, hε₀, hmove⟩ := Erdos634.Geometry.openSegment_two_sided hx
  set d : Plane := (D.tile i).pts (k + 1) - (D.tile i).pts k with hd
  set ε : ℝ := ε₀ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεlt : ε < ε₀ := by rw [hεdef]; linarith
  have hin : ∀ t : ℝ, |t| < ε₀ → g (x + t • d) ≤ c := by
    intro t ht
    have h1 : x + t • d ∈ openSegment ℝ ((D.tile i).pts k) ((D.tile i).pts (k + 1)) := hmove t ht
    have h2 : x + t • d ∈ (D.tile i).edge k :=
      openSegment_subset_segment ℝ _ _ h1
    exact hbound _ (Erdos634.BaseSelection.tile_subset_target D i
      ((D.tile i).edge_subset_carrier k h2))
  have hplus := hin ε (by rw [abs_of_pos hεpos]; exact hεlt)
  have hminus := hin (-ε) (by rw [abs_neg, abs_of_pos hεpos]; exact hεlt)
  rw [map_add, map_smul, smul_eq_mul, hgx] at hplus hminus
  nlinarith [hplus, hminus, hεpos]

open Erdos634.Geometry in
/-- **No straddle at a transversal boundary point** — the contrapositive, in the form the chord
argument uses.  If the target's supporting line at `x` is transversal to the chord direction
`w`, then no tile edge *parallel to* `w` contains `x` in its relative interior. -/
theorem no_straddle_of_transversal {N : ℕ} (D : Dissection N) {i : Fin N} {k : Fin 3}
    {x w : Plane} (g : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ y ∈ D.target.carrier, g y ≤ c) (hgx : g x = c) (hw : g w ≠ 0)
    (hpar : ∃ t : ℝ, (D.tile i).pts (k + 1) - (D.tile i).pts k = t • w) :
    x ∉ openSegment ℝ ((D.tile i).pts k) ((D.tile i).pts (k + 1)) := by
  intro hx
  obtain ⟨t, ht⟩ := hpar
  have hzero := edge_dir_parallel_of_boundary_relint D hx g c hbound hgx
  rw [ht, map_smul, smul_eq_mul] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · -- `t = 0` would make the edge degenerate
    have hne : (D.tile i).pts k ≠ (D.tile i).pts (k + 1) := by
      intro heq
      have h1 : k = k + 1 := (D.tile i).indep.injective heq
      have h2 : ∀ m : Fin 3, m ≠ m + 1 := by decide
      exact h2 k h1
    apply hne
    have : (D.tile i).pts (k + 1) - (D.tile i).pts k = 0 := by rw [ht, h, zero_smul]
    exact (sub_eq_zero.mp this).symm
  · exact hw h

open Erdos634.Geometry in
/-- **The chord form.**  `P` lies on the target's side `j`; the chord direction `Q - P` is
transversal to that side.  Then no tile edge along the chord line straddles `P`.  This is
`prop:cornerpara`'s "no such edge can straddle" step, with the supporting functional produced by
`Tri.exists_supporting` rather than assumed. -/
theorem chord_endpoint_no_straddle {N : ℕ} (D : Dissection N) (j : Fin 3)
    {P Q : Plane} {i : Fin N} {k : Fin 3}
    (hPside : ∀ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), (∀ y ∈ D.target.carrier, g y ≤ c) →
      g (D.target.pts j) = c → g (D.target.pts (j + 1)) = c → g P = c)
    (htrans : ∀ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), (∀ y ∈ D.target.carrier, g y ≤ c) →
      g (D.target.pts j) = c → g (D.target.pts (j + 1)) = c → g (Q - P) ≠ 0)
    (hpar : ∃ t : ℝ, (D.tile i).pts (k + 1) - (D.tile i).pts k = t • (Q - P)) :
    P ∉ openSegment ℝ ((D.tile i).pts k) ((D.tile i).pts (k + 1)) := by
  obtain ⟨g, c, hg0, hbound, hj, hj1, -⟩ := Erdos634.Geometry.exists_supporting D.target j
  exact no_straddle_of_transversal D g c hbound (hPside g c hbound hj hj1)
    (htrans g c hbound hj hj1) hpar


/-! ## 8. Satisfiability witnesses for §7

The same `wallDissection` discharges §7's hypotheses, so none of the three statements is vacuous.
`gBase v = -(v 1)` supports the target along its base `y = 0`. -/

/-- The supporting functional of the target's base, `v ↦ -v₁`. -/
noncomputable def gBase : Plane →ₗ[ℝ] ℝ where
  toFun v := -(v 1)
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem gBase_apply (v : Plane) : gBase v = -(v 1) := rfl

theorem gBase_pt (x y : ℝ) : gBase (mkPt x y) = -y := by simp [gBase_apply]

/-- `gBase ≤ 0` on the target. -/
theorem gBase_bound : ∀ y ∈ wallTarget.carrier, gBase y ≤ 0 := by
  refine Tri.carrier_subset_halfplane wallTarget gBase 0 ?_
  intro i
  fin_cases i <;> simp [wallTarget, mkTri, gBase_pt] <;> norm_num

theorem gBase_bound_target : ∀ y ∈ wallDissection.target.carrier, gBase y ≤ 0 := gBase_bound

/-- The base-edge midpoint of tile `A` is in that edge's relative interior. -/
theorem mid_mem_openSegment :
    mkPt 1 0 ∈ openSegment ℝ ((wallDissection.tile 0).pts 2)
      ((wallDissection.tile 0).pts (2 + 1)) := by
  have h2 : (wallDissection.tile 0).pts 2 = mkPt 2 0 := rfl
  have h0 : (wallDissection.tile 0).pts (2 + 1) = mkPt 0 0 := rfl
  rw [h2, h0]
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  refine PiLp.ext (fun i => ?_)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    simp [PiLp.add_apply, PiLp.smul_apply, mkPt_zero, mkPt_one]

/-- **§7's first statement is not vacuous.** -/
theorem edge_dir_parallel_witness :
    gBase ((wallDissection.tile 0).pts (2 + 1) - (wallDissection.tile 0).pts 2) = 0 :=
  edge_dir_parallel_of_boundary_relint wallDissection mid_mem_openSegment gBase 0
    gBase_bound_target (by rw [gBase_pt]; norm_num)

/-- **§7's second statement is not vacuous**, and says something true and non-trivial: no tile
edge parallel to the wall direction `(1,1)` straddles the target's corner `(0,0)`. -/
theorem no_straddle_witness :
    mkPt 0 0 ∉ openSegment ℝ ((wallDissection.tile 0).pts 0)
      ((wallDissection.tile 0).pts (0 + 1)) := by
  refine no_straddle_of_transversal wallDissection (w := mkPt 1 1) gBase 0
    gBase_bound_target (by rw [gBase_pt]; norm_num) (by rw [gBase_pt]; norm_num) ⟨1, ?_⟩
  have h0 : (wallDissection.tile 0).pts 0 = mkPt 0 0 := rfl
  have h1 : (wallDissection.tile 0).pts (0 + 1) = mkPt 1 1 := rfl
  rw [h0, h1, one_smul]
  refine PiLp.ext (fun i => ?_)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> simp [PiLp.sub_apply, mkPt_zero, mkPt_one]


/-- **`chord_endpoint_no_straddle`'s first hypothesis is discharged for any `P` on side `j`.**
A supporting functional is constant on the side it supports, so `g P = c` automatically. -/
theorem hPside_of_mem_side {N : ℕ} (D : Dissection N) (j : Fin 3) {P : Plane}
    (hP : P ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1))) :
    ∀ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), (∀ y ∈ D.target.carrier, g y ≤ c) →
      g (D.target.pts j) = c → g (D.target.pts (j + 1)) = c → g P = c := by
  rintro g c - hj hj1
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hP
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hj, hj1, ← add_mul, hab, one_mul]


/-! ## 9. The chord clamp: everything of the target on the chord's line is inside the chord

The step `prop:cornerpara` actually needs is not "no straddler at `P`" but its consequence: every
far-side edge along the chord's line is *contained in* the chord, so its trace on the chord is the
whole edge and its contribution to `wall_partition`'s sum is its full length.  With both chord
endpoints on `∂ABC` and the chord transversal there, that is immediate from two supporting
half-planes — no relative-interior argument needed.

This is the specific-to-the-corner-tile input `PAPER_MAP.md`'s `prop:cornerpara` row asks for.
It does **not** contradict the withdrawn general claim at `BaseBetaWalks.lean:797–808` ("an
interior `b`-edge is matched by exactly one further `b`-edge"): that claim concerns a `b`-edge
whose endpoints are *interior* to the target, where no supporting line exists at the endpoints and
`chord_clamp` has nothing to apply. -/

open Erdos634.Geometry in
/-- **The line `{f = c}` through two of its distinct points is their `lineMap` line.** -/
theorem line_eq_lineMap (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q : Plane}
    (hP : f P = c) (hQ : f Q = c) (hPQ : P ≠ Q) {x : Plane} (hx : f x = c) :
    ∃ t : ℝ, x = AffineMap.lineMap P Q t := by
  set v : Plane := Q - P with hv
  have hvne : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
  have hvker : v ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, hv, map_sub, hP, hQ, sub_self]
  have hle : Submodule.span ℝ {v} ≤ LinearMap.ker f := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hvker
  have h1 : Module.finrank ℝ (Submodule.span ℝ ({v} : Set Plane)) = 1 :=
    finrank_span_singleton hvne
  have h2 : Module.finrank ℝ (LinearMap.ker f) = 1 :=
    Erdos634.ChordTraceReal.ker_finrank_one f hf
  have heq : Submodule.span ℝ ({v} : Set Plane) = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [h1, h2])
  have hxker : x - P ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, map_sub, hx, hP, sub_self]
  rw [← heq, Submodule.mem_span_singleton] at hxker
  obtain ⟨t, ht⟩ := hxker
  refine ⟨t, ?_⟩
  have : x = t • v + P := by rw [ht]; abel
  rw [this, hv]
  simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]

open Erdos634.Geometry in
/-- **The chord clamp.**  `P` and `Q` are two points of a convex set `S`, on the line `{f = c}`,
each carrying a supporting functional of `S` that is *strict* at the other.  Then every point of
`S` on that line lies in `segment ℝ P Q`. -/
theorem chord_clamp {S : Set Plane} (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q : Plane} (hPQ : P ≠ Q) (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ S, g y ≤ cg) (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ S, h y ≤ ch) (hhQ : h Q = ch) (hhP : h P < ch)
    {x : Plane} (hxS : x ∈ S) (hfx : f x = c) :
    x ∈ segment ℝ P Q := by
  obtain ⟨t, rfl⟩ := line_eq_lineMap f hf c hfP hfQ hPQ hfx
  have hgx : g (AffineMap.lineMap P Q t) = cg + t * (g Q - cg) := by
    simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, map_add, map_smul, map_sub,
      smul_eq_mul, hgP]
    ring
  have hhx : h (AffineMap.lineMap P Q t) = h P + t * (ch - h P) := by
    simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, map_add, map_smul, map_sub,
      smul_eq_mul, hhQ]
    ring
  have hg' := hg _ hxS
  have hh' := hh _ hxS
  rw [hgx] at hg'
  rw [hhx] at hh'
  have ht0 : 0 ≤ t := by nlinarith
  have ht1 : t ≤ 1 := by nlinarith
  rw [segment_eq_image_lineMap]
  exact ⟨t, ⟨ht0, ht1⟩, rfl⟩

open Erdos634.Geometry in
/-- **Every chain edge along the chord's line is contained in the chord** — hence flush, hence its
trace on the chord is the whole edge.  This is the "no overhang" half of `prop:cornerpara`'s
partition step, and the input the length equation needs. -/
theorem chain_edge_subset_chord {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q) (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    (D.tile e.1).edge e.2 ⊆ segment ℝ P Q := by
  intro y hy
  exact chord_clamp f hf c hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP
    (Erdos634.BaseSelection.tile_subset_target D e.1
      ((D.tile e.1).edge_subset_carrier e.2 hy))
    (D.lineChain_edge_subset he y hy)

open Erdos634.Geometry in
/-- **The length equation along a two-sided-clamped chord.**  Combining `chain_edge_subset_chord`
with `wall_partition`: every chain edge's trace is the whole edge, so the chain's *own* edge
lengths sum to the chord's length.  This is the equation `prop:bunsplit` is applied to in
`prop:cornerpara`. -/
theorem chain_edge_lengths_sum {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (c : ℝ) {P Q : Plane} (hPQ : P ≠ Q) (hfP : f P = c) (hfQ : f Q = c)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hS : segment ℝ P Q ⊆ {y | f y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∑ e ∈ D.lineChain f c,
        ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist P Q) := by
  have hstep : ∀ e ∈ D.lineChain f c,
      (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ P Q)
        = ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) := by
    intro e he
    have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ P Q :=
      chain_edge_subset_chord D f hf c hPQ hfP hfQ g cg hg hgP hgQ h ch hh hhQ hhP he
    rw [Set.inter_eq_self_of_subset_left hsub]
    show (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane)
        (segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) = _
    rw [MeasureTheory.hausdorffMeasure_segment, edist_dist]
  have hpart := D.wall_partition f c hf hPQ hS hint hwall
  rw [Finset.sum_congr rfl hstep] at hpart
  rw [hpart, MeasureTheory.hausdorffMeasure_segment, edist_dist]


/-! ## 10. Satisfiability witnesses for §9

The wall of `wallDissection` is a genuine two-sided-clamped chord: `P = (0,0)` is clamped by the
base `y = 0` and `Q = (1,1)` by the hypotenuse `x + y = 2`, each strict at the other endpoint.
So §9 is not vacuous, and its conclusion here is a real length equation: the near-side chain's own
edge lengths sum to `dist (0,0) (1,1) = √2`. -/

/-- The supporting functional of the target's hypotenuse, `v ↦ v₀ + v₁`. -/
noncomputable def hHyp : Plane →ₗ[ℝ] ℝ where
  toFun v := v 0 + v 1
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem hHyp_apply (v : Plane) : hHyp v = v 0 + v 1 := rfl

theorem hHyp_pt (x y : ℝ) : hHyp (mkPt x y) = x + y := by simp [hHyp_apply]

theorem hHyp_bound : ∀ y ∈ wallDissection.target.carrier, hHyp y ≤ 2 := by
  refine Tri.carrier_subset_halfplane wallTarget hHyp 2 ?_
  intro i
  fin_cases i <;> simp [wallTarget, mkTri, hHyp_pt] <;> norm_num

/-- **§9's clamp is not vacuous**, and gives a real length equation on the witness. -/
theorem chain_edge_lengths_sum_witness :
    ∑ e ∈ wallDissection.lineChain wallF 0,
        ENNReal.ofReal (dist ((wallDissection.tile e.1).pts e.2)
          ((wallDissection.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist wallU wallV) :=
  chain_edge_lengths_sum wallDissection wallF wallF_ne 0 wallU_ne_wallV wallF_u wallF_v
    gBase 0 gBase_bound_target (by rw [wallU, gBase_pt]; norm_num)
    (by rw [wallV, gBase_pt]; norm_num)
    hHyp 2 hHyp_bound (by rw [wallV, hHyp_pt]; norm_num)
    (by rw [wallU, hHyp_pt]; norm_num)
    wall_hS wall_hint wall_hwall

/-- Every chain edge really is contained in the wall — the flushness conclusion, on the witness. -/
theorem chain_edge_subset_chord_witness (e : Fin 2 × Fin 3)
    (he : e ∈ wallDissection.lineChain wallF 0) :
    (wallDissection.tile e.1).edge e.2 ⊆ segment ℝ wallU wallV :=
  chain_edge_subset_chord wallDissection wallF wallF_ne 0 wallU_ne_wallV wallF_u wallF_v
    gBase 0 gBase_bound_target (by rw [wallU, gBase_pt]; norm_num)
    (by rw [wallV, gBase_pt]; norm_num)
    hHyp 2 hHyp_bound (by rw [wallV, hHyp_pt]; norm_num)
    (by rw [wallU, hHyp_pt]; norm_num) he

end Erdos634.TPErdos
