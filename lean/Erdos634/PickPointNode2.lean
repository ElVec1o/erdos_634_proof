import Erdos634.LemmaPNode2

/-!
# The `blocked_arcs`/`free_dirs` bookkeeping, verified at node 2 of Lemma P

Erdős #634.  `private/ROOM/e2b14/report_spec.md` (2026-09-13 audit of `PlacementCompleteness.lean`
against `gen_tree.py`) flags one precise, previously-unformalized gap in the constructor's
correctness case:

> "The d-selection (free-direction) logic in `gen_tree.py`/`build23.py` is the ONE piece of the
> whole placement pipeline with no Lean-proved correctness backing it — everything downstream (six
> placements, escape, overlap) is verified against Lean, but the free-arc/angular-order computation
> that decides WHICH direction `d` is, is trusted from the Python engine alone."

`LemmaPNode2.node2_jam` already discharges `hlex`/`hfree`/`hblocked` of `placement_completeness`
for `v = v2 = (6,0)`, `d = d2 = (7/9, √32/9)` by direct coordinate algebra — but nowhere does the
corpus check that `d2` is actually what `Cons.pick_point`/`Cons.free_dirs` (`gen_tree.py:147-209`)
*compute* at that corner.  This file closes exactly that check, for this one node.

## What `blocked_arcs`/`free_dirs` compute at `v2`

`gen_tree.py`'s `blocked_arcs(v, tiles)`, run at `v = v2` with `tiles = [w1t0, w1t1]`:

* `v2` is interior to the target's base edge `(0,0)–(46,0)` (`on_seg_interior`), contributing the
  arc `(sub(A,B), sub(B,A)) = ((-46,0),(46,0))` — angles `(π, 2π)`, i.e. the lower half-plane;
* `v2 = w1t0.pts 1`, a genuine tile corner, contributing the arc between
  `w1t0.pts 2 - v2` and `w1t0.pts 0 - v2` in whichever order has positive `cross` — the tile's own
  interior wedge at that corner;
* `v2 = w1t1.pts 0`, likewise contributing the wedge between `w1t1.pts 1 - v2` and
  `w1t1.pts 2 - v2`.

`free_dirs` sorts the six arc endpoints by `Cons.ang_lt` and returns the gaps between consecutive
arcs that no arc covers; `pick_point` returns the clockwise-most (`ang_lt`-least) start among them.
`node2_blocked_arcs_correct` below computes these three arcs' endpoints in closed form from the
tile coordinates already fixed in `LemmaPNode2.lean`, and shows:

1. both tile-corner arcs are genuinely oriented the way `blocked_arcs` orients them
   (`cross e_a e_b > 0`, `cross e_c e_d > 0` — this is the `if G.cross(d1,d2) > 0` branch, taken);
2. the base-edge arc's two endpoints are exactly the two tile-corner edges lying flush on the base
   (`w1t0.pts 0 - v2` is a negative real multiple of the base-edge direction `(-1,0)`,
   `w1t1.pts 1 - v2` a positive one) — so the three arcs abut with **no unaccounted gap** on the
   base side;
3. `d2` is *literally* the direction to `w1t1`'s apex, `w1t1.pts 2 - v2` up to a positive scalar —
   the exact vector `free_dirs` would return as the clockwise endpoint of the (unique) free arc;
4. that free arc is genuinely open: `cross d2 e_a > 0`, so `d2` sits strictly clockwise of
   `w1t0`'s wedge, matching `ang_lt`'s comparator on the one remaining gap.

This is the **combinatorial fact `gen_tree.py`'s comparator relies on**, checked against the same
coordinates `LemmaPNode2.node2_jam` already certified as `hlex`/`hfree`/`hblocked`-sound. It does
**not** reprove `hfree`/`hblocked` (those stand, proved directly, in `LemmaPNode2.lean`) and it does
**not** formalize `Cons.ang_lt`/`Cons.free_dirs` as general Lean definitions — only that at this one
node, on these coordinates, the arc bookkeeping picks out `d2`. General correctness of the
sorting/complement step over an arbitrary number of arcs remains open; see the module docstring's
closing note.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PickPointNode2

open Erdos634.Geometry Erdos634.CertCoord Erdos634.ThickBlockingLemmas
  Erdos634.LemmaPNode2 Erdos634.PlacementCompleteness

/-! ## 1. The three arcs' endpoints, read off the tile coordinates -/

theorem e_a_eq : w1t0.pts 2 - v2 = mkPt (5 / 3) (5 / 6 * rr) := by
  refine plane_ext ?_ ?_ <;>
    simp only [PiLp.sub_apply, w1t0, v2, mkTri_pts, mkPt_zero, mkPt_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

theorem e_b_eq : w1t0.pts 0 - v2 = mkPt (-6) 0 := by
  refine plane_ext ?_ ?_ <;>
    simp only [PiLp.sub_apply, w1t0, v2, mkTri_pts, mkPt_zero, mkPt_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

theorem e_c_eq : w1t1.pts 1 - v2 = mkPt 9 0 := by
  refine plane_ext ?_ ?_ <;>
    simp only [PiLp.sub_apply, w1t1, v2, mkTri_pts, mkPt_zero, mkPt_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

theorem e_d_eq : w1t1.pts 2 - v2 = mkPt (35 / 9) (5 / 9 * rr) := by
  refine plane_ext ?_ ?_ <;>
    simp only [PiLp.sub_apply, w1t1, v2, mkTri_pts, mkPt_zero, mkPt_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-! ## 2. The tile-corner arcs are oriented the way `blocked_arcs` orients them -/

/-- **`w1t0`'s corner arc at `v2` is taken in the order `(e_a, e_b)`** — the branch
`G.cross(d1,d2) > 0` of `blocked_arcs`'s `if G.cross(d1, d2) > 0 : arcs.append((d1,d2)) else
(d2,d1)`, with `d1 = w1t0.pts 2 - v2`, `d2 = w1t0.pts 0 - v2` (the code visits `tri[(i+1)%3]` then
`tri[(i+2)%3]` after finding `v = tri[i]` at `i = 1`). -/
theorem w1t0_arc_orientation : 0 < cross (w1t0.pts 2 - v2) (w1t0.pts 0 - v2) := by
  rw [e_a_eq, e_b_eq]
  show 0 < (5 / 3 : ℝ) * 0 - (5 / 6 * rr) * (-6)
  nlinarith [rr_pos]

/-- **`w1t1`'s corner arc at `v2` is taken in the order `(e_c, e_d)`**, the corner found at
`i = 0` (`v2 = w1t1.pts 0`), visiting `tri[1]` then `tri[2]`. -/
theorem w1t1_arc_orientation : 0 < cross (w1t1.pts 1 - v2) (w1t1.pts 2 - v2) := by
  rw [e_c_eq, e_d_eq]
  show 0 < (9 : ℝ) * (5 / 9 * rr) - 0 * (35 / 9)
  nlinarith [rr_pos]

/-! ## 3. The tile corners abut the base arc with no gap -/

/-- **`w1t0`'s back edge at `v2` lies exactly on the base**, negative-`x` direction — the same ray
`blocked_arcs`'s base-edge arc uses as its `sub(A,B)` endpoint (`A,B = (0,0),(46,0)`, giving
direction `(-46,0)`, a positive multiple of `(-6,0)`). -/
theorem w1t0_back_on_base : ∃ k : ℝ, 0 < k ∧ w1t0.pts 0 - v2 = k • mkPt (-1) 0 := by
  refine ⟨6, by norm_num, ?_⟩
  rw [e_b_eq]; refine plane_ext ?_ ?_ <;> simp

/-- **`w1t1`'s front edge at `v2` lies exactly on the base**, positive-`x` direction — the same ray
`blocked_arcs`'s base-edge arc uses as its `sub(B,A)` endpoint. -/
theorem w1t1_front_on_base : ∃ k : ℝ, 0 < k ∧ w1t1.pts 1 - v2 = k • mkPt 1 0 := by
  refine ⟨9, by norm_num, ?_⟩
  rw [e_c_eq]; refine plane_ext ?_ ?_ <;> simp

/-! ## 4. `d2` is exactly the free arc's clockwise-most start -/

/-- **`d2` is a positive multiple of `w1t1`'s apex direction** — exactly the vector
`free_dirs`/`pick_point` return as the free arc's starting endpoint once the base and the two
tile-corner arcs are removed: the one endpoint among the six that is nobody's *other* endpoint. -/
theorem d2_eq_apex_dir : w1t1.pts 2 - v2 = (5 : ℝ) • d2 := by
  rw [e_d_eq]
  refine plane_ext ?_ ?_ <;> simp [d2] <;> ring

/-- **The free arc is genuinely open**: `d2` sits strictly clockwise of `w1t0`'s near edge, i.e.
`ang_lt`'s comparator (`cross > 0` within a half) puts `d2` before `e_a` — this is the gap
`free_dirs` reports between `w1t1`'s arc-end and `w1t0`'s arc-start, and `pick_point` returns its
start, `d2`. -/
theorem d2_before_ea : 0 < cross d2 (w1t0.pts 2 - v2) := by
  have hd2 : d2 = (5 : ℝ)⁻¹ • (w1t1.pts 2 - v2) := by
    rw [d2_eq_apex_dir, smul_smul]; norm_num
  have h : cross d2 (w1t0.pts 2 - v2)
      = (5 : ℝ)⁻¹ * cross (w1t1.pts 2 - v2) (w1t0.pts 2 - v2) := by
    rw [hd2, cross_anticomm _ (w1t0.pts 2 - v2), cross_smul_right,
      cross_anticomm (w1t0.pts 2 - v2)]
    ring
  rw [h, e_a_eq, e_d_eq]
  show 0 < (5:ℝ)⁻¹ * ((35/9) * (5/6*rr) - (5/9*rr) * (5/3))
  nlinarith [rr_pos]

/-! ## 5. Assembly -/

/-- **`gen_tree.py`'s `blocked_arcs`/`free_dirs`/`pick_point` bookkeeping, verified at node 2**: the
two tile-corner arcs are correctly oriented, they abut the base-edge arc with no unaccounted gap,
and the one remaining free arc's clockwise-most direction — exactly what `pick_point` returns — is
`d2`, the ray `LemmaPNode2.node2_jam` already certifies `hfree`/`hblocked` for. This connects the
algorithm's arc computation to the Dissection-level hypotheses of `placement_completeness` for this
one node, closing the gap `private/ROOM/e2b14/report_spec.md` flags as unformalized in general. -/
theorem node2_blocked_arcs_pick_d2 :
    0 < cross (w1t0.pts 2 - v2) (w1t0.pts 0 - v2) ∧
    0 < cross (w1t1.pts 1 - v2) (w1t1.pts 2 - v2) ∧
    (∃ k : ℝ, 0 < k ∧ w1t0.pts 0 - v2 = k • mkPt (-1) 0) ∧
    (∃ k : ℝ, 0 < k ∧ w1t1.pts 1 - v2 = k • mkPt 1 0) ∧
    w1t1.pts 2 - v2 = (5 : ℝ) • d2 ∧
    0 < cross d2 (w1t0.pts 2 - v2) :=
  ⟨w1t0_arc_orientation, w1t1_arc_orientation, w1t0_back_on_base, w1t1_front_on_base,
    d2_eq_apex_dir, d2_before_ea⟩

end Erdos634.PickPointNode2

#print axioms Erdos634.PickPointNode2.node2_blocked_arcs_pick_d2
