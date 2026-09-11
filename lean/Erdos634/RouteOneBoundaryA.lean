import Erdos634.RouteOneWallOnly
import Erdos634.BaseBetaTargetCoord

/-!
# `hAint` repaired: `A` on the target's boundary is enough, and the composition now goes through

Written 2026-09-11, directly after `BaseBetaTargetCoord.lean`, which found that
`RouteOneWallOnly.flank_from_wall_only` and `RouteOne.route_one_flank_from_configuration` both
carried `hAint : A ∈ interior D.target.carrier` while `rem:route1uniform`'s own
`A = c·u` — the upper end of the side's first `c`-edge — lies **on the target's left side**
(`BaseBetaTargetCoord.sideA_not_mem_interior`).  The hypothesis was therefore false at the exact
configuration those theorems were written for.

## The repair, and which of the two candidate routes is the right one

Two repairs were possible.

* **Move `A`.**  Rejected: `erdos-634-companion.tex:1604` *defines* `A = c\,u` as "the upper end of
  the side's first `c`-edge", and the whole content of the remark is the rigid order
  `A —ᵃ— R₁ —^{c−a}— V —ᵃ— E` of four points at the common height `c sin β` on that line.
  Perturbing `A` inward destroys `|V−A| = c`, i.e. the statement that `[A,V]` is a *tile edge*,
  which is what `hjseg` transports.  The paper's point genuinely is a boundary point.

* **Weaken the hypothesis.**  Correct, and the interiority of `A` was never used: the proof of
  `route_one_flank_from_configuration` consumes `hAint` in exactly one place, to show every point
  of the **open** segment `V`–`A` is interior to the target.  For a convex set, an open segment
  from an interior point to *any* point of the set is already interior
  (`Convex.openSegment_interior_self_subset_interior`).  So `A ∈ D.target.carrier` suffices —
  no one-sided, tangent or half-space condition is needed, and `ChordChartPlanar`'s determinant
  machinery is not needed either (it supplies the *containment*, below, not the local structure).

The weakening was made **in place** (it is strictly stronger) in
`RouteOne.route_one_flank_from_configuration`, `RouteOne.route_one_flank_of_vertices`,
`RouteOneWallOnly.flank_from_wall_only` and `.flank_from_wall_only_of_vertices`; the two call sites
inside `RouteOne.flank_propagates` now pass `interior_subset`.  This file supplies the
configuration side.

## What is proved here

* `sideA_mem_carrier` — `A = c·u` **is** a point of the base-`β` target (it is `(1/f)` of the way
  up the left side, since `c = f²` and the leg is `f³`).  Together with the weakening this
  discharges the repaired hypothesis at the configuration.
* `sideA_sub_escapeV` — `(A − V)₁ = 0` and `(A − V)₀ = −f² < 0`: `hAy` and `hAx` are *also* free,
  being the shift `escapeV_eq_A_shift` verbatim.
* `flank_at_route1uniform` — **the composition.**  For a dissection in normal position
  (`D.target = baseBetaTarget e f`), at `V` and `A` of `rem:route1uniform`, from the `α`-tile data
  and `hwall` alone: some tile has `V` as a vertex with a horizontal rightward edge there.  Four
  hypotheses of `flank_from_wall_only` (`hV`, `hAcar`, `hAy`, `hAx`) are discharged from the
  coordinate model; none of them is assumed.

## What is **not** claimed, exactly

Not one of the three `/goal` outcomes.  `conj:advance` remains CONJECTURE, `e = 1` is not closed,
`e ≥ 2` is untouched, the prime case is not advanced, and no Rule 0 label moves.  The two
obligations `BaseBetaTargetCoord.lean` flagged alongside `hAint` are **both still open and both
still hypotheses of `flank_at_route1uniform`**:

1. `hwall` — the local wall — is the actual open content of Route 1 (`rem:routeoneopen`, OPEN).
   Nothing here bears on it.
2. **Normal position** (`htgt`) — reducing a general base-`β` `Dissection` to `D.target =
   baseBetaTarget e f` is a real placement step, since `Tri.Congruent` is congruence under an
   arbitrary isometry.  It is assumed, not proved.

Nor is the `α`-tile bundle (`hjseg`, `habovej`, `hjleft`) witnessed at `Dissection` level; only at
`Tri` level, by `RouteOneWallOnly.alpha_tile_witness`.  So what changed is precisely this: of the
hypotheses of `flank_from_wall_only`, the two target-geometry ones are now *theorems* at the
configuration rather than one theorem and one refuted assumption.  The residue is `hwall` plus
normal position plus the `α`-tile placement — no longer a false hypothesis.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.RouteOneBoundaryA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord

/-! ## 1. `A = c·u` is a point of the target -/

/-- **The companion point lies in the target's carrier.**  `A = c·u` with `c = f²` on a left side
of length `f³`, so `A` is the point `(1/f)` of the way from `(0,0)` to the apex — on the boundary
(`sideA_not_mem_interior`) but in the closed triangle.  The three determinant tests:
the left one vanishes identically, the bottom one is `L·H/f > 0`, and the right one is
`L·H·(1 − 1/f) ≥ 0`, which is where `1 ≤ f` enters. -/
theorem sideA_mem_carrier {e f : ℝ} (he : 0 < e) (hef : e < f) (hf1 : 1 ≤ f) :
    mkPt (sideA e f).1 (sideA e f).2 ∈ (baseBetaTarget e f he hef).carrier := by
  have hf : (0:ℝ) < f := lt_of_lt_of_le one_pos hf1
  have hf0 : (f : ℝ) ≠ 0 := ne_of_gt hf
  have hH := height_pos he hef
  have hL := baseLen_pos he hef
  refine Erdos634.CertCoord.mem_carrier_of_dets (target_det_pos he hef) ?_ ?_ ?_
  · -- right-hand test: `det3 A P₁ P₂ = L·H·(1 − 1/f)`
    have : det3 (sideA e f).1 (sideA e f).2 (baseLen e f) 0 (baseLen e f / 2) (height e f)
        = baseLen e f * height e f * (1 - 1 / f) := by
      unfold det3 sideA; field_simp; ring
    rw [this]
    have : 0 ≤ 1 - 1 / f := by
      rw [sub_nonneg, div_le_one hf]; exact hf1
    positivity
  · -- left test: vanishes
    have : det3 0 0 (sideA e f).1 (sideA e f).2 (baseLen e f / 2) (height e f) = 0 := by
      unfold det3 sideA; field_simp; ring
    rw [this]
  · -- bottom test: `L·H/f`
    have : det3 0 0 (baseLen e f) 0 (sideA e f).1 (sideA e f).2
        = baseLen e f * height e f / f := by
      unfold det3 sideA; field_simp; ring
    rw [this]
    positivity

/-- **The shift, in `Plane` coordinates.**  `A − V = (−f², 0)`: `hAy` and `hAx` of
`flank_from_wall_only` are discharged by `escapeV_eq_A_shift`. -/
theorem sideA_sub_escapeV (e f : ℝ) (hf : 0 < f) :
    (mkPt (sideA e f).1 (sideA e f).2 - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
    (mkPt (sideA e f).1 (sideA e f).2 - mkPt (escapeV e f).1 (escapeV e f).2) 0 < 0 := by
  obtain ⟨h1, h2⟩ := escapeV_eq_A_shift e f
  constructor
  · simp only [PiLp.sub_apply, mkPt_one, h2]; ring
  · simp only [PiLp.sub_apply, mkPt_zero, h1]
    nlinarith

/-! ## 2. The composition at `rem:route1uniform` -/

/-- **Route 1's flank at `rem:route1uniform`'s configuration, from the wall and the `α`-tile.**

`V = c·u + (c,0)` and `A = c·u` are the remark's own points; the target is the base-`β` member
`(e,f)` in normal position.  `hV`, `hAcar`, `hAy`, `hAx` are all supplied by the coordinate model
(`escapeV_mem_interior`, `sideA_mem_carrier`, `sideA_sub_escapeV`) and none of them appears as a
hypothesis.  What remains assumed is the `α`-tile's placement, the local wall `hwall`, and normal
position `htgt` — see the module docstring for why each is genuinely open. -/
theorem flank_at_route1uniform {N : ℕ} (D : Dissection N) {e f : ℝ}
    (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f)
    (htgt : D.target = baseBetaTarget e f (by linarith) hef)
    (j : Fin N) (mj : Fin 3)
    (hjseg : openSegment ℝ (mkPt (escapeV e f).1 (escapeV e f).2)
        (mkPt (sideA e f).1 (sideA e f).2)
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier →
      0 ≤ (q - mkPt (escapeV e f).1 (escapeV e f).2) 1)
    (hjleft : ∀ q : Plane, q ∈ (D.tile j).carrier →
      (q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : Fin N,
      (∃ q : Plane, q ∈ (D.tile k).carrier ∧
        0 < (q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ∧
        0 < (q - mkPt (escapeV e f).1 (escapeV e f).2) 1 ∧
        dist q (mkPt (escapeV e f).1 (escapeV e f).2) < ρ) →
      ∀ q : Plane, q ∈ (D.tile k).carrier →
        0 ≤ (q - mkPt (escapeV e f).1 (escapeV e f).2) 1) :
    ∃ (i : Fin N) (m : Fin 3),
      (D.tile i).pts m = mkPt (escapeV e f).1 (escapeV e f).2 ∧
      ((((D.tile i).pts (m + 1) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < ((D.tile i).pts (m + 1) - mkPt (escapeV e f).1 (escapeV e f).2) 0) ∨
       (((D.tile i).pts (m + 2) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < ((D.tile i).pts (m + 2) - mkPt (escapeV e f).1 (escapeV e f).2) 0)) := by
  have he0 : (0:ℝ) < e := by linarith
  have hf : (0:ℝ) < f := lt_trans he0 hef
  obtain ⟨hAy, hAx⟩ := sideA_sub_escapeV e f hf
  refine Erdos634.RouteOneWallOnly.flank_from_wall_only D _ _ j mj
    (escapeV_mem_interior_of_target D he hef hf2 htgt) ?_ hjseg hAy hAx habovej hjleft hwall
  rw [htgt]
  exact sideA_mem_carrier he0 hef (by linarith)

/-! ## 3. Axiom audit -/

#print axioms sideA_mem_carrier
#print axioms sideA_sub_escapeV
#print axioms flank_at_route1uniform

end Erdos634.RouteOneBoundaryA
