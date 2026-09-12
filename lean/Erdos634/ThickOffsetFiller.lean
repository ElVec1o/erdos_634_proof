import Erdos634.ThickWedgeGram
import Erdos634.Frontier

/-!
# The **offset** filler at the `a|a` junction of the thick tile `(e,f) = (2,3)`, `(a,b,c) = (6,5,9)`

Room `e2b2`, Tao seat, 2026-09-12.  `ThickJunctionCoords.lean` built the *flush* filler at this
junction and explicitly named its sibling as **not attempted**: "`MarchKills.lean`'s second, deeper
construction — `offsetFiller` … is **not** attempted here".  `ThickWedgeGram.wedge_extremal_coords63`
then proved that the only two edge pairs a third tile can present into the junction wedge are the
flush rays (branch 1) and "the swapped-and-scaled pair" (branch 2), and called branch 2 "the (as yet
unbuilt …) offset filler's edges".  **This file builds branch 2 in exact coordinates and exhibits it
as a genuine triangle congruent to the tile, inside the real target.**  Branch 2 of
`wedge_extremal_coords63` therefore acquires its first witness: that disjunction is not degenerate.

## The construction, with every constant tracked

Junction `J = (t+6, 0)` of two `BG` `a`-tiles on `[t, t+6]`, `[t+6, t+12]`.  From `J` the two wedge
rays are (`ThickWedgeGram`)

    b-ray  `(p63, h) = (5/3, 10√2/3)`,  length `b = 5`   (to the LEFT tile's apex `A_L`)
    c-ray  `(q63, h) = (23/3, 10√2/3)`, length `c = 9`   (to the RIGHT tile's apex `A_R`)

with `h = apexH63 = 10√2/3`.  Note `p63 = dBG63 − a63 = 5/3 > 0`: at this thick tile **both** apexes
lie to the *right* of the junction (`dBG63 = 23/3 > a63 = 6`), unlike `e = 1`.  The offset filler is

    `J`,  `P₁ = J + (b/c)·(q63, h) = J + (115/27, 50√2/27)`,
          `P₂ = J + (c/b)·(p63, h) = J + (3, 6√2)`.

Exact side lengths (`offsetFiller63_sides`): `|J P₁| = b = 5`, `|J P₂| = c = 9`, `|P₁ P₂| = a = 6`.
Its angles (`offsetFiller63_angle_cosines`): `α` at `J` (`cos = 7/9`), `γ` at `P₁`, `β` at `P₂`
(`cos = 23/27`).  Note `cos β = 23/27 > cos α = 21/27`, i.e. `β < α` — **hazard H3**, the reverse of
every `e = 1` member; nothing below imports an `α < β`-dependent lemma.

## The exposed run, exactly

`P₂ = J + (c/b)·(A_L − J)` lies on the ray `J → A_L` **past** the left `a`-tile's apex `A_L`
(`overshoot_between`: `A_L` is strictly between `J` and `P₂`), and

    `dist A_L P₂ = c − b = e² = 4`          (`exposed_run_is_e_sq`, computed two ways)

so the offset filler's `c`-edge `[J, P₂]` covers the left `a`-tile's whole `b`-edge `[J, A_L]`
(length `5`) and leaves a straight boundary run of length exactly `4` on the same line.  And `4` is
not representable: `run_e_sq_not_representable` instantiates the already-general, already-proved
`Frontier.gap_e_squared` at `(e,f,b) = (2,3,5)`.  **This is the number Chain 1 was looking for.**

## What this does NOT prove, and it is the whole point

`RunPartition.run_partition` converts a run into a semigroup element only when the run is clamped at
**both** ends.  Here:

* the **near** end is clamped, and cleanly.  The run `[J, P₂]` (length `c = 9`) taken whole is
  clamped at `J` by clamp type (c), the target boundary: the extension of the ray backwards from `J`
  has strictly negative `y` (`extension_below_base`), hence leaves `baseBetaTarget 2 3` whose base is
  on the `x`-axis.  Equivalently, the sub-run `[A_L, P₂]` is clamped at `A_L` by clamp type (b), the
  left `a`-tile's own `b`-edge `[J, A_L]` lying on the line on the near side.
* the **far** end `P₂` is **not clamped by anything in this configuration**, and none of
  `run_partition`'s three clamp types can be supplied here.  `P₂` sits at height `6√2 ≈ 8.49`,
  which is `9/5` of the `a`-tile apex height `10√2/3 ≈ 4.71` (`overshoot_above_layer1`): it is
  strictly above every vertex of the base layer *and* of both fillers, so (a) no placed tile's
  interior contains the extension beyond `P₂`, (b) no placed tile has an edge on that line beyond
  `P₂`, and (c) `P₂` is strictly interior to the target (`offsetFiller63_subset_target` at `t = 12`,
  with `6√2 < 10√2`), so the extension is not outside it either.  The run is clamped at one end only,
  and `run_partition` does not apply.

**Consequence for Chain 1, stated plainly.**  The `e²` run is real and is exactly the gap the plan
predicted; the *clamp* is what is missing, and it is missing for a structural reason, not for want of
bookkeeping — the overshoot vertex is the highest point of the whole layer-1 figure, so there is
nothing above it to clamp against.  Note this is already true at `e = 1`: `MarchKills` records the
overshoot vertex only as a **confinement** fact (`march_confined`, `overshootH_lt_strip`) and never
kills with it.  The `e = 1` kill that the plan transplanted (`MarchStep.offset_terminal_dies`) is a
*terminal base-line residue* argument, whose number is `1` because `L − p − s = 1` positions, **not**
because `c − b = 1`.  Those two quantities coincide at `e = 1` and are different objects; at
`(e,f) = (2,3)` the geometric overshoot is `c − b = 4` while the terminal residue is still one base
position.  Chain 1's premise — "the `e = 1` pattern suggests the offset filler exposes a clamped run"
— rests on that coincidence.

Nothing here is a statement about Group A's three words, and no Rule 0 label moves.  One instance,
`(e,f) = (2,3)`; no `(e,f)`-general claim.  Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.ThickOffsetFiller

open Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord
open Erdos634.ThickJunctionCoords Erdos634.ThickWedgeGram

/-! ## 1. `√2` and the apex height, in a usable form -/

theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-- `1.414… < √2 < 1.4143`: the two rational bounds every inequality below uses. -/
theorem sqrt2_bounds : 1.414 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  constructor
  · nlinarith [sqrt2_sq, sqrt2_pos]
  · nlinarith [sqrt2_sq, sqrt2_pos]

/-! ## 2. The offset filler -/

/-- The left `a`-tile's apex `A_L = (t + dBG63, h)`; as seen from the junction `J = (t+6,0)` it is
the `b`-ray endpoint, offset `(p63, h) = (5/3, 10√2/3)`. -/
noncomputable def aApexL (t : ℝ) : Plane := mkPt (t + dBG63) apexH63

theorem aApexL_eq (t : ℝ) : aApexL t = mkPt (t + 6 + 5 / 3) apexH63 := by
  unfold aApexL dBG63
  congr 1
  ring

/-- `|J A_L| = b = 5`: the left `a`-tile's `b`-edge. -/
theorem dist_J_aApexL (t : ℝ) : dist (mkPt (t + 6) 0) (aApexL t) = b63 := by
  have hsq : dist (mkPt (t + 6) 0) (aApexL t) ^ 2 = b63 ^ 2 := by
    unfold aApexL
    rw [dist_sq_mkPt, zero_sub, neg_sq, apexH63_sq]
    simp only [h2_63, dBG63, b63]; ring_nf
  have hb : (0:ℝ) < b63 := by simp only [b63]; norm_num
  nlinarith [hsq, dist_nonneg (x := mkPt (t + 6) 0) (y := aApexL t), hb]

theorem det_offsetFiller63 (t : ℝ) :
    det3 (t + 6) 0 (t + 6 + 115 / 27) (50 * Real.sqrt 2 / 27) (t + 6 + 3) (6 * Real.sqrt 2) ≠ 0 := by
  have h : det3 (t + 6) 0 (t + 6 + 115 / 27) (50 * Real.sqrt 2 / 27) (t + 6 + 3)
      (6 * Real.sqrt 2) = 20 * Real.sqrt 2 := by unfold det3; ring
  rw [h]
  exact (mul_pos (by norm_num : (0:ℝ) < 20) sqrt2_pos).ne'

/-- **The offset filler at the `a|a` junction `t+6`.**  Vertex order: the junction `J`, then the
`b`-length vector `P₁` along the `c`-ray (scaled by `b/c = 5/9`), then the `c`-length vector `P₂`
along the `b`-ray (scaled by `c/b = 9/5`) — the overshoot vertex.  Same vertex convention as
`MarchKills.offsetFiller` at `e = 1`. -/
noncomputable def offsetFiller63 (t : ℝ) : Tri :=
  mkTri (t + 6) 0 (t + 6 + 115 / 27) (50 * Real.sqrt 2 / 27) (t + 6 + 3) (6 * Real.sqrt 2)
    (det_offsetFiller63 t)

/-- **The offset filler's vertices are exactly `wedge_extremal_coords63`'s branch-2 pair.**  `P₁ − J
= (b/c)·(q63, h)` and `P₂ − J = (c/b)·(p63, h)`, the second disjunct of that theorem, verbatim. -/
theorem offsetFiller63_is_branch2 :
    (115 / 27 : ℝ) = b63 / c63 * q63 ∧ (50 * Real.sqrt 2 / 27 : ℝ) = b63 / c63 * apexH63 ∧
    (3 : ℝ) = c63 / b63 * p63 ∧ (6 * Real.sqrt 2 : ℝ) = c63 / b63 * apexH63 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [q63_eq]; simp only [b63, c63]; norm_num
  · unfold apexH63; simp only [b63, c63]; ring
  · rw [p63_eq]; simp only [b63, c63]; norm_num
  · unfold apexH63; simp only [b63, c63]; ring

/-! ## 3. The offset filler is congruent to the tile -/

theorem offsetFiller63_sides (t : ℝ) :
    dist ((offsetFiller63 t).pts 0) ((offsetFiller63 t).pts 1) ^ 2 = b63 ^ 2 ∧
    dist ((offsetFiller63 t).pts 0) ((offsetFiller63 t).pts 2) ^ 2 = c63 ^ 2 ∧
    dist ((offsetFiller63 t).pts 1) ((offsetFiller63 t).pts 2) ^ 2 = a63 ^ 2 := by
  have h2 := sqrt2_sq
  simp only [offsetFiller63, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩ <;> rw [dist_sq_mkPt] <;> simp only [a63, b63, c63] <;> nlinarith [h2]

/-- The three side lengths themselves (not squared): `b`, `c`, `a`. -/
theorem offsetFiller63_lengths (t : ℝ) :
    dist ((offsetFiller63 t).pts 0) ((offsetFiller63 t).pts 1) = 5 ∧
    dist ((offsetFiller63 t).pts 0) ((offsetFiller63 t).pts 2) = 9 ∧
    dist ((offsetFiller63 t).pts 1) ((offsetFiller63 t).pts 2) = 6 := by
  obtain ⟨h1, h2, h3⟩ := offsetFiller63_sides t
  simp only [b63, c63, a63] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [h1, dist_nonneg (x := (offsetFiller63 t).pts 0) (y := (offsetFiller63 t).pts 1)]
  · nlinarith [h2, dist_nonneg (x := (offsetFiller63 t).pts 0) (y := (offsetFiller63 t).pts 2)]
  · nlinarith [h3, dist_nonneg (x := (offsetFiller63 t).pts 1) (y := (offsetFiller63 t).pts 2)]

/-- **The offset filler's angle cosines, by the law of cosines from the exact side lengths**:
`α` at the junction `J` (`cos = 7/9 = 21/27`), `β` at the overshoot vertex `P₂` (`cos = 23/27`),
`γ` at `P₁` (`cos = −1/3 = −e/(2f)`).  Recorded because of **hazard H3**: `23/27 > 21/27`, so `β < α` at this
tile, the reverse of every `e = 1` member. -/
theorem offsetFiller63_angle_cosines :
    ((5:ℝ) ^ 2 + 9 ^ 2 - 6 ^ 2) / (2 * 5 * 9) = 7 / 9 ∧
    ((6:ℝ) ^ 2 + 9 ^ 2 - 5 ^ 2) / (2 * 6 * 9) = 23 / 27 ∧
    ((5:ℝ) ^ 2 + 6 ^ 2 - 9 ^ 2) / (2 * 5 * 6) = -1 / 3 ∧
    (23:ℝ) / 27 > 7 / 9 := by
  norm_num

/-! ## 4. The exposed run: exactly `c − b = e² = 4` -/

/-- **`A_L` is strictly between `J` and `P₂`.**  `P₂ = J + (c/b)·(A_L − J)` with `c/b = 9/5 > 1`, so
the offset filler's `c`-edge runs along the left `a`-tile's `b`-edge and past its apex. -/
theorem overshoot_between (t : ℝ) :
    aApexL t = AffineMap.lineMap (mkPt (t + 6) 0) ((offsetFiller63 t).pts 2) ((5:ℝ) / 9) := by
  simp only [offsetFiller63, mkTri_pts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  apply Erdos634.MarchInduction.plane_ext <;>
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, aApexL, dBG63, apexH63] <;> ring

/-- **THE EXPOSED RUN.**  The straight segment left on the line of the left `a`-tile's `b`-edge,
between that tile's apex `A_L` and the offset filler's overshoot vertex `P₂`, has length exactly
`c − b = 9 − 5 = 4 = e²`.  Checked two independent ways: from the coordinate difference
`(4/3, 8√2/3)` (norm² `= 16/9 + 128/9 = 144/9 = 16`), and as `(c/b − 1)·b = c − b`. -/
theorem exposed_run_is_e_sq (t : ℝ) :
    dist (aApexL t) ((offsetFiller63 t).pts 2) = (2:ℝ) ^ 2 ∧ (2:ℝ) ^ 2 = c63 - b63 := by
  have h2 := sqrt2_sq
  have hsq : dist (aApexL t) ((offsetFiller63 t).pts 2) ^ 2 = 16 := by
    simp only [offsetFiller63, mkTri_pts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      aApexL, dBG63, apexH63]
    rw [dist_sq_mkPt]; nlinarith [h2]
  refine ⟨?_, by simp only [c63, b63]; norm_num⟩
  nlinarith [hsq, dist_nonneg (x := aApexL t) (y := (offsetFiller63 t).pts 2)]

/-- **The run length `e² = 4` is not a nonnegative integer combination of `a = 6`, `b = 5`, `c = 9`.**
`Frontier.gap_e_squared`, already general and already proved, instantiated at `(e,f,b) = (2,3,5)`
(`b + e² = 5 + 4 = 9 = f²`).  No new arithmetic: exactly the discharge Chain 1 predicted. -/
theorem run_e_sq_not_representable (x y z : ℕ) : x * 6 + y * 5 + z * 9 ≠ 4 := by
  intro h
  exact Erdos634.Frontier.gap_e_squared (e := 2) (f := 3) (b := 5) (x := x) (y := y) (z := z)
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by omega)

/-! ## 5. Why the far end is not clamped: the overshoot vertex is the highest point -/

/-- The overshoot vertex's height, `(c/b)·h = (9/5)(10√2/3) = 6√2`. -/
theorem overshoot_height (t : ℝ) : (offsetFiller63 t).pts 2 1 = 6 * Real.sqrt 2 := by
  simp only [offsetFiller63, mkTri_pts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    mkPt_one]

/-- **The overshoot vertex is strictly above the whole of layer 1.**  Every vertex of both `a`-tile
orientations and both *flush* fillers lies at height `≤ apexH63 = 10√2/3`
(`ThickJunctionCoords.junction_confined_63`), and `6√2 > 10√2/3`.  Also `50√2/27 < 10√2/3`, so the
filler's *other* new vertex `P₁` is inside layer 1: `P₂` is the unique point above it.  This is why
clamp types (a) and (b) are unavailable at `P₂` — there is nothing placed there to clamp against. -/
theorem overshoot_above_layer1 :
    apexH63 < 6 * Real.sqrt 2 ∧ 50 * Real.sqrt 2 / 27 < apexH63 := by
  have hs := sqrt2_pos
  unfold apexH63
  constructor <;> nlinarith [hs]

/-- **The backward extension of the run leaves the target.**  The ray `J → A_L` continued *backwards*
past `J = (t+6, 0)` has strictly negative height, so it is outside `baseBetaTarget 2 3` (whose base is
the segment of the `x`-axis from `(0,0)` to `(46,0)`).  This is clamp type (c) at the near end — the
one clamp this configuration really does supply. -/
theorem extension_below_base (t s : ℝ) (hs : 0 < s) :
    (mkPt (t + 6 - s * 5 / 3) (-(s * apexH63)) : Plane) 1 < 0 := by
  rw [mkPt_one]
  have := apexH63_pos
  nlinarith

/-! ## 6. Non-vacuity: the offset filler really fits inside the target, at `t = 12` -/

theorem baseLen_23 : baseLen 2 3 = 46 := by unfold baseLen Nq; norm_num

theorem height_23 : height 2 3 = 10 * Real.sqrt 2 := by
  unfold height Dr
  norm_num
  rw [show (32:ℝ) = 4 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  ring

/-- **The offset filler at `t = 12` lies inside `baseBetaTarget 2 3`.**  All three vertices are in
the target's carrier, hence so is the convex hull.  So the construction is realised at real
coordinates in the real target — it is not an abstract configuration.  (Where Ramanujan's round-1
transplant of the `e = 1` `c|a` recipe *overshot* the target, this one does not.) -/
theorem offsetFiller63_pts_mem_target (k : Fin 3) :
    (offsetFiller63 12).pts k ∈ (baseBetaTarget 2 3 (by norm_num) (by norm_num)).carrier := by
  have hs := sqrt2_pos
  have h2 := sqrt2_sq
  have hlo := sqrt2_bounds.1
  have hhi := sqrt2_bounds.2
  have hdet : (0:ℝ) < det3 0 0 (baseLen 2 3) 0 (baseLen 2 3 / 2) (height 2 3) :=
    target_det_pos (by norm_num) (by norm_num)
  fin_cases k <;>
    simp only [offsetFiller63, baseBetaTarget, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] <;>
    refine mem_carrier_of_dets hdet ?_ ?_ ?_ <;>
    simp only [det3, baseLen_23, height_23] <;> nlinarith [hs, h2, hlo, hhi]

theorem offsetFiller63_subset_target :
    (offsetFiller63 12).carrier ⊆ (baseBetaTarget 2 3 (by norm_num) (by norm_num)).carrier := by
  refine convexHull_min ?_ (Tri.convex _)
  rintro _ ⟨k, rfl⟩
  exact offsetFiller63_pts_mem_target k

/-- **The far end is strictly interior in height too.**  `P₂`'s height `6√2` is strictly below the
target's apex height `10√2`, so clamp type (c) — "the extension beyond `P₂` is outside the target" —
is **not** available at the far end either.  Together with `overshoot_above_layer1` (types (a), (b)
unavailable) this is the precise obstruction: the run `[A_L, P₂]` of length `e² = 4` is clamped at one
end only, and `RunPartition.run_partition` needs both. -/
theorem far_end_not_clamped_by_boundary : 6 * Real.sqrt 2 < height 2 3 := by
  rw [height_23]; nlinarith [sqrt2_pos]

/-! ## 7. Axiom audit -/

#print axioms offsetFiller63_is_branch2
#print axioms offsetFiller63_sides
#print axioms offsetFiller63_lengths
#print axioms offsetFiller63_angle_cosines
#print axioms overshoot_between
#print axioms exposed_run_is_e_sq
#print axioms run_e_sq_not_representable
#print axioms overshoot_above_layer1
#print axioms extension_below_base
#print axioms offsetFiller63_pts_mem_target
#print axioms offsetFiller63_subset_target
#print axioms far_end_not_clamped_by_boundary

end Erdos634.ThickOffsetFiller
