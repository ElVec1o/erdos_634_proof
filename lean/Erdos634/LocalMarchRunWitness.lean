import Erdos634.LocalMarchRun
import Erdos634.Tiling44Bridge

/-!
# A real march run: length four along the base of the `(16,16,22)` tiling

`LocalMarchRun.Run` is only worth having if it is inhabited by something that is not degenerate.
This file exhibits one, in the **verified** 44-tile congruent dissection of the `(16,16,22)`
triangle by `(2,3,4)` triangles (`Tiling44Bridge.dissection`, whose certificate checks (C1)–(C4)
are kernel-verified).

Its target's base runs from `(0,0)` to `(176,0)`, and the tiles laid along it are

```
(0,0)–(16,0)   (16,0)–(32,0)   (32,0)–(48,0)   (48,0)–(64,0)   (64,0)–(96,0)  …
```

— four `a`-edges (`a = 16`, the shortest side of the scaled `(2,3,4)` tile), then a `c`-edge of
length `32`.  Those four are a march run of length `4`, step `w = (16,0)`, and this file builds it:
`baseRun`.

So the structure is inhabited at a length where `contig` has content (`baseRun_contig` is a real
equation between two distinct tiles' vertices), and `tile_ne_succ`, `entry_injective`,
`length_le_three_mul`, `length_le_runLength` are all non-vacuous.

This does **not** claim the `(16,16,22)` tiling is a base-`β` escape configuration — it is not; it
is a witness that the *object* is real.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LocalMarchRunWitness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LocalMarchRun

/-- The 44-tile dissection of the `(16,16,22)` triangle, as a plain `Dissection`. -/
noncomputable def D : Dissection Tiling44.tiles.length :=
  Erdos634.Tiling44Bridge.dissection.toDissection

/-- Affine combination in coordinates. -/
theorem mkPt_add_smul (a b c x y : ℝ) :
    mkPt a b + c • mkPt x y = mkPt (a + c * x) (b + c * y) := by
  ext i
  fin_cases i <;> simp

/-- The march's positions along the base: `(16n, 0)`. -/
theorem pos_base (n : ℕ) : pos (mkPt 0 0) (mkPt 16 0) n = mkPt ((n : ℝ) * 16) 0 := by
  rw [pos, mkPt_add_smul]
  norm_num

/-- The first vertex of a certificate piece, read off its integer data. -/
theorem pts_zero (i : Fin Tiling44.tiles.length) (a : ℤ) (r : ℝ)
    (h : Tiling44.t1 Tiling44.tiles[i.val] = (a, 0, 0, 0)) (hr : (a : ℝ) = r) :
    (D.tile i).pts 0 = mkPt r 0 := by
  show (Erdos634.Tiling44Bridge.pieceAt i).pts 0 = _
  unfold Erdos634.Tiling44Bridge.pieceAt Erdos634.Tiling44Bridge.pieceTri
  rw [Erdos634.CertCoord.mkTri_pts, h, ← hr]
  norm_num [Erdos634.Z15Real.toR, Erdos634.Tiling44Bridge.toZPt, Erdos634.Z15Real.zx,
    Erdos634.Z15Real.zy]

/-- The second vertex of a certificate piece, read off its integer data. -/
theorem pts_one (i : Fin Tiling44.tiles.length) (a : ℤ) (r : ℝ)
    (h : Tiling44.t2 Tiling44.tiles[i.val] = (a, 0, 0, 0)) (hr : (a : ℝ) = r) :
    (D.tile i).pts 1 = mkPt r 0 := by
  show (Erdos634.Tiling44Bridge.pieceAt i).pts 1 = _
  unfold Erdos634.Tiling44Bridge.pieceAt Erdos634.Tiling44Bridge.pieceTri
  rw [Erdos634.CertCoord.mkTri_pts, h, ← hr]
  norm_num [Erdos634.Z15Real.toR, Erdos634.Tiling44Bridge.toZPt, Erdos634.Z15Real.zx,
    Erdos634.Z15Real.zy]

/-- The four tiles laying `a`-edges along the base, in order. -/
def baseTile : Fin 4 → Fin Tiling44.tiles.length :=
  ![⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩]

/-- **A march run of length four**, in a kernel-verified dissection.  Every field is checked
against the certificate's own integer coordinates. -/
noncomputable def baseRun : Run D (mkPt 0 0) (mkPt 16 0) 4 where
  tile := baseTile
  corner := ![0, 0, 0, 0]
  head n := by
    fin_cases n
    · rw [pos_base]; exact pts_zero _ 0 _ rfl (by norm_num)
    · rw [pos_base]; exact pts_zero _ 16 _ rfl (by norm_num)
    · rw [pos_base]; exact pts_zero _ 32 _ rfl (by norm_num)
    · rw [pos_base]; exact pts_zero _ 48 _ rfl (by norm_num)
  foot n := by
    fin_cases n
    · rw [pos_base]; exact pts_one _ 16 _ rfl (by norm_num)
    · rw [pos_base]; exact pts_one _ 32 _ rfl (by norm_num)
    · rw [pos_base]; exact pts_one _ 48 _ rfl (by norm_num)
    · rw [pos_base]; exact pts_one _ 64 _ rfl (by norm_num)

/-- The step is nonzero. -/
theorem step_ne_zero : (mkPt 16 0 : Plane) ≠ 0 := by
  intro h
  have := congrArg (fun v : Plane => v 0) h
  simp at this

/-- **Contiguity has content here.**  The far endpoint of the first entry is the near endpoint of
the second, and the two entries are different tiles. -/
theorem baseRun_contig :
    (D.tile (baseRun.tile 0)).pts (baseRun.corner 0 + 1)
      = (D.tile (baseRun.tile 1)).pts (baseRun.corner 1) :=
  contig baseRun 0 1 rfl

/-- **Consecutive entries really are distinct tiles.** -/
theorem baseRun_tile_ne : baseRun.tile 0 ≠ baseRun.tile 1 :=
  tile_ne_succ baseRun 0 1 rfl

/-- **The length bound applies.** -/
theorem baseRun_short : (4 : ℕ) ≤ 3 * Tiling44.tiles.length :=
  length_le_three_mul baseRun step_ne_zero

/-! ## The shape hypotheses hold at the witness

`orient_mono` asks, of each entry, that the run's edge be the tile's **strictly shortest** side.
For the first entry of `baseRun` that is checked here from the certificate's coordinates: the sides
are `16 < 24 < 32`, the scaled `(2,3,4)` triangle. -/

/-- The third vertex of a certificate piece. -/
theorem pts_two (i : Fin Tiling44.tiles.length) (a b : ℤ) (r s : ℝ)
    (h : Tiling44.t3 Tiling44.tiles[i.val] = (a, 0, 0, b)) (hr : (a : ℝ) = r)
    (hs : (b : ℝ) * Real.sqrt 15 = s) :
    (D.tile i).pts 2 = mkPt r s := by
  show (Erdos634.Tiling44Bridge.pieceAt i).pts 2 = _
  unfold Erdos634.Tiling44Bridge.pieceAt Erdos634.Tiling44Bridge.pieceTri
  rw [Erdos634.CertCoord.mkTri_pts, h, ← hr, ← hs]
  simp [Erdos634.Z15Real.toR, Erdos634.Tiling44Bridge.toZPt, Erdos634.Z15Real.zx,
    Erdos634.Z15Real.zy]

private theorem dist_of_sq {p q : Plane} {d : ℝ} (hd : 0 ≤ d) (h : dist p q ^ 2 = d ^ 2) :
    dist p q = d := by
  nlinarith [dist_nonneg (x := p) (y := q)]

/-- The first entry's three sides: `16`, `24`, `32`. -/
theorem tile0_sides :
    dist ((D.tile (baseRun.tile 0)).pts 0) ((D.tile (baseRun.tile 0)).pts 1) = 16 ∧
    dist ((D.tile (baseRun.tile 0)).pts 1) ((D.tile (baseRun.tile 0)).pts 2) = 24 ∧
    dist ((D.tile (baseRun.tile 0)).pts 2) ((D.tile (baseRun.tile 0)).pts 0) = 32 := by
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have p0 : (D.tile (baseRun.tile 0)).pts 0 = mkPt 0 0 := pts_zero _ 0 _ rfl (by norm_num)
  have p1 : (D.tile (baseRun.tile 0)).pts 1 = mkPt 16 0 := pts_one _ 16 _ rfl (by norm_num)
  have p2 : (D.tile (baseRun.tile 0)).pts 2 = mkPt 22 (6 * Real.sqrt 15) :=
    pts_two _ 22 6 _ _ rfl (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [p0, p1]
    exact dist_of_sq (by norm_num) (by rw [Erdos634.CertCoord.dist_sq_mkPt]; norm_num)
  · rw [p1, p2]
    refine dist_of_sq (by norm_num) ?_
    rw [Erdos634.CertCoord.dist_sq_mkPt]
    nlinarith [h15]
  · rw [p2, p0]
    refine dist_of_sq (by norm_num) ?_
    rw [Erdos634.CertCoord.dist_sq_mkPt]
    nlinarith [h15]

/-- **The strict-shortest-side hypotheses of `orient_mono` hold at the first entry.** -/
theorem baseRun_shape0 :
    Erdos634.TilePlacement.sideOpp (D.tile (baseRun.tile 0)) (apex baseRun 0) <
      Erdos634.TilePlacement.sideOpp (D.tile (baseRun.tile 0)) (apex baseRun 0 + 1) ∧
    Erdos634.TilePlacement.sideOpp (D.tile (baseRun.tile 0)) (apex baseRun 0 + 1) <
      Erdos634.TilePlacement.sideOpp (D.tile (baseRun.tile 0)) (apex baseRun 0 + 2) := by
  obtain ⟨e0, e1, e2⟩ := tile0_sides
  have s0 : Erdos634.TilePlacement.sideOpp (D.tile (baseRun.tile 0)) (apex baseRun 0)
      = dist ((D.tile (baseRun.tile 0)).pts 0) ((D.tile (baseRun.tile 0)).pts 1) := rfl
  have s1 : Erdos634.TilePlacement.sideOpp (D.tile (baseRun.tile 0)) (apex baseRun 0 + 1)
      = dist ((D.tile (baseRun.tile 0)).pts 1) ((D.tile (baseRun.tile 0)).pts 2) := rfl
  have s2 : Erdos634.TilePlacement.sideOpp (D.tile (baseRun.tile 0)) (apex baseRun 0 + 2)
      = dist ((D.tile (baseRun.tile 0)).pts 2) ((D.tile (baseRun.tile 0)).pts 0) := rfl
  rw [s0, s1, s2, e0, e1, e2]
  norm_num

/-! ## The wall bridge, non-vacuously

The run lies on the line `y = 0`, the target's base.  So `length_le_runLength` applies here and the
four entries really are members of `MarchRunObject.aRun` for that wall. -/

/-- The `y`-coordinate, as an affine functional: the wall's defining map. -/
noncomputable def gY : Plane →ᵃ[ℝ] ℝ :=
  LinearMap.toAffineMap (EuclideanSpace.proj (1 : Fin 2)).toLinearMap

@[simp] theorem gY_apply (p : Plane) : gY p = p 1 := rfl

/-- The base line: `gY = 0`, and the step lies in the kernel. -/
theorem gY_start : gY (mkPt 0 0) = 0 := by simp

theorem gY_step : gY.linear (mkPt 16 0) = 0 := by
  show (EuclideanSpace.proj (1 : Fin 2)).toLinearMap (mkPt 16 0) = 0
  simp

/-- **The four entries are `a`-edges of the base wall.** -/
theorem baseRun_mem_aRun (n : Fin 4) :
    (baseRun.tile n, baseRun.corner n) ∈
      Erdos634.MarchRunObject.aRun D gY 0 ‖(mkPt 16 0 : Plane)‖ :=
  mem_aRun baseRun gY 0 gY_start gY_step n

/-- **The local run is inside the global one**, at this witness. -/
theorem baseRun_le_runLength :
    (4 : ℕ) ≤ Erdos634.MarchRunObject.runLength D gY 0 ‖(mkPt 16 0 : Plane)‖ :=
  length_le_runLength baseRun step_ne_zero gY 0 gY_start gY_step

end Erdos634.LocalMarchRunWitness
