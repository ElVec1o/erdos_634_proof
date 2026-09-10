import Erdos634.RouteOneApproach
import Erdos634.RouteOneThroughEdge
import Erdos634.RouteOneFlankTransfer

/-!
# Route 1's flank at `V` from the wall alone: no below-tile, no straight angle, no `π`-count

Written 2026-09-11, immediately after `RouteOneApproach.lean`, and **correcting that file's
closing note**.

`RouteOneApproach.lean` ends by saying the residue of Route 1's attachment obligation is `hV`, the
below-tile data (`hVb`, `hb`, `hbelow`) and `hwall`, and that `hbelow`/`hwall` *are*
`conj:advance`'s named unproved input, *"that a through-edge, rather than a junction, runs below
the line at `V`"*.  **That reading is an artefact of the vehicle, not of the mathematics.**
`RouteOne.EscapeData` carries the below-tile `b`, its straight angle `hb` and the `π`-count `hcard`
as *fields of the structure*, so anything routed through `EscapeData` inherits them whether the
argument uses them or not.  The corpus already has a second route to the very same conclusion which
never mentions a tile below the line:
`RouteOne.route_one_flank_from_configuration` (2026-09-09, `RouteOneThroughEdge.lean`), recorded in
`lean/PAPER_MAP.md` as removing `conj:advance`'s case (a) at the flank step.

This file composes that route with `RouteOneApproach.exists_approach_sequence`, and the below-tile
disappears from the statement entirely.

## What is proved

* `serving_ne_two_pi_of_above` — a tile whose carrier lies weakly above `V` has
  `localAngle V ≠ 2π`.  `RouteOne.serving_ne_two_pi` derives the same conclusion from the existence
  of a *different* tile `b ≠ i` containing `V`; here nothing but the tile's own position is used, so
  the last field of `EscapeData` that needed `b` stops needing it.

* `flank_from_wall_only` — **the main theorem.**  From
  - `hV`, `hAint` : `V` and `A` interior to the target,
  - the `α`-tile `j`: its edge `(mj+1, mj+2)` contains the open stretch `V`–`A`, `A` is horizontally
    left of `V`, `j`'s carrier lies weakly above `V` and weakly left of `V`,
  - `hwall` : `∃ ρ > 0`, every tile with a point strictly up-and-right of `V` within `ρ` lies weakly
    above `V`,

  there is a tile `i` with `V` as a vertex and a horizontal rightward edge at `V` — Route 1's flank
  conclusion, the input `overshoot_dichotomy` consumes.

  **No below-tile appears**: no `b`, no `hVb`, no `hb : localAngle = π`, no `hcard`, no `hbelow`.
  `hwall` here is *verbatim* the `hwall` of `RouteOneApproach.EscapeData.ofInterior_plain`; the
  present theorem is that theorem's hypothesis list minus `b, hVb, hb, hcard, hbelow`, with the
  `α`-tile data of `rem:route1uniform` in their place.

* `flank_from_wall_only_of_vertices` — the same with the two carrier-position hypotheses on `j`
  replaced by sign conditions on its three vertices (`carrier_above_of_vertices`' form).

* `alpha_tile_witness` — the `α`-tile hypotheses `habovej`, `hjleft`, `hjseg`, `hAy`, `hAx` are
  simultaneously satisfiable: the triangle `(0,0), (-1,0), (-1,1)` with `V = (0,0)`,
  `A = (-1,0)` meets all five.

## Scope, stated exactly, and what is **not** claimed

This does **not** prove `conj:advance`, does not close `e = 1`, does not touch `e ≥ 2`, and does not
advance the prime case.  `hwall` is still an assumed statement about a hypothetical tiling and is
still the open part of the attachment (`rem:routeoneopen`, OPEN).  Nor is the hypothesis bundle
witnessed at the `Dissection` level: like `route_one_flank_from_configuration`'s own bundle
(`PAPER_MAP.md`, "the wall configuration is not" witnessed), no concrete dissection satisfying all
of it is exhibited here — only the `α`-tile part is, by `alpha_tile_witness`.

What changes is the *content* of the residue.  Before: "which tile occupies the region below the
line at `V`, and is it a through-edge or a junction there".  After: nothing about the region below
the line at all — only that tiles which poke up-and-right of `V` near `V` do not dip below the
horizontal through `V`.  The paper's clause (a) is not an obligation of this route.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.RouteOneWallOnly

open Erdos634.Geometry

/-! ## 1. `localAngle ≠ 2π` without a second tile -/

/-- **The serving tile does not cover `V`, from its own position alone.**  If every point of `T`
lies weakly above `V` then `T.localAngle V ≠ 2π`: the `2π` branch of `Tri.localAngle` is the
all-coordinates-positive one, which puts a whole ball around `V` inside the carrier, and such a ball
contains points strictly below `V`.

Compare `RouteOne.serving_ne_two_pi`, which reaches the same conclusion from a *different* tile
`b ≠ i` containing `V`.  This version needs no other tile — the point of the exercise. -/
theorem serving_ne_two_pi_of_above (T : Tri) (V : Plane)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1) :
    T.localAngle V ≠ 2 * Real.pi := by
  classical
  intro h2
  rw [Erdos634.Geometry.Tri.localAngle] at h2
  split at h2
  · rename_i hv
    have hle := EuclideanGeometry.angle_le_pi (T.pts (hv.choose + 1)) (T.pts hv.choose)
      (T.pts (hv.choose + 2))
    have hpi := Real.pi_pos
    rw [Erdos634.Geometry.cornerAngle] at h2
    rw [h2] at hle; linarith
  · split at h2
    · rename_i hpos
      obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
      -- the point `V - (r/2) e₁` lies in the ball, hence in the carrier, and is strictly below `V`
      set q : Plane := V + (r / 2) • Erdos634.RouteOne.downVec with hq
      have hdist : dist q V = r / 2 := by
        rw [hq, dist_eq_norm, show V + (r / 2) • Erdos634.RouteOne.downVec - V
              = (r / 2) • Erdos634.RouteOne.downVec by abel,
          norm_smul, Erdos634.RouteOne.norm_downVec, mul_one, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      have hmem : q ∈ T.carrier := hsub (Metric.mem_ball.mpr (by rw [hdist]; linarith))
      have hy : (q - V) 1 = -(r / 2) := by
        rw [hq, show V + (r / 2) • Erdos634.RouteOne.downVec - V
              = (r / 2) • Erdos634.RouteOne.downVec by abel]
        simp only [PiLp.smul_apply, smul_eq_mul, Erdos634.RouteOne.downVec_one]
        ring
      have := habove q hmem
      rw [hy] at this
      linarith
    · split at h2
      · have := Real.pi_pos; linarith
      · have := Real.pi_pos; linarith

/-! ## 1b. The mirror of `carrier_above_of_vertices` in the first coordinate -/

/-- **The abscissa of a carrier point is the barycentric average of the vertices' abscissae.**
The first-coordinate twin of `RouteOne.height_eq_coord_combo`. -/
theorem abscissa_eq_coord_combo (T : Tri) (V q : Plane) :
    (q - V) 0 = ∑ j, T.basis.coord j q * ((T.pts j - V) 0) := by
  have hq : ∑ j, T.basis.coord j q • T.pts j = q := T.basis.linear_combination_coord_eq_self q
  have hs : ∑ j, T.basis.coord j q = 1 := T.basis.sum_coord_apply_eq_one q
  have hqy : q 0 = ∑ j, T.basis.coord j q * (T.pts j) 0 := by
    conv_lhs => rw [← hq]
    simp
  have key : ∑ j, T.basis.coord j q * ((T.pts j - V) 0)
      = (∑ j, T.basis.coord j q * (T.pts j) 0) - (∑ j, T.basis.coord j q) * (V 0) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp only [PiLp.sub_apply]; ring)
  rw [key, hs, one_mul, ← hqy]
  simp only [PiLp.sub_apply]

/-- **A tile whose vertices lie weakly left of `V` lies weakly left of `V`.** -/
theorem carrier_left_of_vertices (T : Tri) (V : Plane)
    (h : ∀ j, (T.pts j - V) 0 ≤ 0) : ∀ q : Plane, q ∈ T.carrier → (q - V) 0 ≤ 0 := by
  intro q hq
  have hnn : ∀ j, 0 ≤ T.basis.coord j q := by
    rw [Erdos634.Geometry.Tri.carrier_eq_nonneg_coord] at hq; exact hq
  rw [abscissa_eq_coord_combo T V q]
  exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hnn j) (h j))

/-! ## 2. The main theorem -/

/-- **Route 1's flank at `V` from the wall alone.**

Hypotheses: `V` and `A` interior to the target; the `α`-tile `j` of `rem:route1uniform` laying its
horizontal edge from `V` leftward to `A`, with its carrier weakly above and weakly left of `V`; and
the local wall — every tile with a point strictly up-and-right of `V` within `ρ` lies weakly above
`V`.

Conclusion: some tile has `V` as a vertex and a horizontal rightward edge there.

Nothing about the region below the line at `V` occurs anywhere in the statement.  In particular the
serving tile `i` is *produced*, not assumed, and the three `EscapeData` fields that referred to a
below-tile (`b`, `hb`, `hcard`) together with `hbelow` are absent. -/
theorem flank_from_wall_only {N : ℕ} (D : Dissection N) (V A : Plane) (j : Fin N) (mj : Fin 3)
    (hV : V ∈ interior D.target.carrier) (hAint : A ∈ interior D.target.carrier)
    (hjseg : openSegment ℝ V A
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (hAy : (A - V) 1 = 0) (hAx : (A - V) 0 < 0)
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier → 0 ≤ (q - V) 1)
    (hjleft : ∀ q : Plane, q ∈ (D.tile j).carrier → (q - V) 0 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : Fin N,
      (∃ q : Plane, q ∈ (D.tile k).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      ∀ q : Plane, q ∈ (D.tile k).carrier → 0 ≤ (q - V) 1) :
    ∃ (i : Fin N) (m : Fin 3), (D.tile i).pts m = V ∧
      ((((D.tile i).pts (m + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 1) - V) 0) ∨
       (((D.tile i).pts (m + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 2) - V) 0)) := by
  classical
  obtain ⟨ρ, hρ, hw⟩ := hwall
  obtain ⟨pick, g, hg, hx, hslope, hnear, hpos, hin⟩ :=
    Erdos634.RouteOneApproach.exists_approach_sequence D hV ρ hρ
  obtain ⟨i, hserve, hclose, -, n0, hn0⟩ :=
    Erdos634.RouteOne.pigeonhole_wall D V pick g hg hx hslope hnear hpos
  -- the serving tile lies weakly above the wall: it carries an approach point
  have habovei : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1 := by
    refine hw i ⟨pick n0, ?_, hx n0, hpos n0, hin n0⟩
    rw [← hn0]; exact hg n0
  -- the serving tile is not the `α`-tile: it has points strictly right of `V`, which `j` has not
  have hij : i ≠ j := by
    obtain ⟨q, hq, hqx, -⟩ := hserve 1 one_pos
    intro h
    rw [h] at hq
    exact absurd (hjleft q hq) (not_le.mpr hqx)
  obtain ⟨m, hm, hflank⟩ :=
    Erdos634.RouteOne.route_one_flank_from_configuration D i j V A hij
      (Erdos634.RouteOne.serving_ne_zero D i hclose)
      (serving_ne_two_pi_of_above (D.tile i) V habovei)
      habovei habovej hserve mj hjseg hAy hAx hV hAint
  exact ⟨i, m, hm, hflank⟩

/-- **The same, with the `α`-tile's position given by its vertices.**  `carrier_above_of_vertices`
turns the two carrier hypotheses on `j` into six sign conditions on its three vertices — the form
the corpus's own `no_downward_edge` / `edge_dir_nonneg_of_local` produce. -/
theorem flank_from_wall_only_of_vertices {N : ℕ} (D : Dissection N) (V A : Plane) (j : Fin N)
    (mj : Fin 3)
    (hV : V ∈ interior D.target.carrier) (hAint : A ∈ interior D.target.carrier)
    (hjseg : openSegment ℝ V A
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (hAy : (A - V) 1 = 0) (hAx : (A - V) 0 < 0)
    (hvj : ∀ m : Fin 3, 0 ≤ ((D.tile j).pts m - V) 1)
    (hlj : ∀ m : Fin 3, ((D.tile j).pts m - V) 0 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : Fin N,
      (∃ q : Plane, q ∈ (D.tile k).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      ∀ q : Plane, q ∈ (D.tile k).carrier → 0 ≤ (q - V) 1) :
    ∃ (i : Fin N) (m : Fin 3), (D.tile i).pts m = V ∧
      ((((D.tile i).pts (m + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 1) - V) 0) ∨
       (((D.tile i).pts (m + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (m + 2) - V) 0)) := by
  exact flank_from_wall_only D V A j mj hV hAint hjseg hAy hAx
    (Erdos634.RouteOne.carrier_above_of_vertices (D.tile j) V hvj)
    (carrier_left_of_vertices (D.tile j) V hlj) hwall

/-! ## 3. The `α`-tile hypotheses are satisfiable

`hjseg`, `hAy`, `hAx`, `habovej`, `hjleft` are five conditions on one tile; the triangle
`(0,0), (-1,0), (-1,1)` meets all five at `V = (0,0)`, `A = (-1,0)`.  (This is a `Tri`-level
witness, exactly as `RouteOne.through_edge_witness` is for the `π` branch; it is **not** a
`Dissection`-level witness for the whole hypothesis bundle, which is not exhibited here.) -/

/-- **The `α`-tile side of the configuration is not vacuous.** -/
theorem alpha_tile_witness :
    ∃ (T : Tri) (V A : Plane) (m : Fin 3),
      openSegment ℝ V A ⊆ openSegment ℝ (T.pts (m + 1)) (T.pts (m + 2)) ∧
      (A - V) 1 = 0 ∧ (A - V) 0 < 0 ∧
      (∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1) ∧
      (∀ q : Plane, q ∈ T.carrier → (q - V) 0 ≤ 0) := by
  have hdet : Erdos634.CertCoord.det3 0 0 (-1) 0 (-1) 1 ≠ 0 := by
    simp [Erdos634.CertCoord.det3]
  set T : Tri := Erdos634.CertCoord.mkTri 0 0 (-1) 0 (-1) 1 hdet with hT
  have h20 : (2 : Fin 3) + 1 = 0 := by decide
  have h21 : (2 : Fin 3) + 2 = 1 := by decide
  refine ⟨T, T.pts 0, T.pts 1, 2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h20, h21]
  · rw [hT]
    simp [Erdos634.CertCoord.mkTri_pts, Erdos634.CertCoord.mkPt_one]
  · rw [hT]
    simp [Erdos634.CertCoord.mkTri_pts, Erdos634.CertCoord.mkPt_zero]
  · -- every vertex is weakly above `(0,0)`, so every carrier point is
    refine Erdos634.RouteOne.carrier_above_of_vertices T (T.pts 0) (fun k => ?_)
    fin_cases k <;>
      simp [hT, Erdos634.CertCoord.mkTri_pts, Erdos634.CertCoord.mkPt_one]
  · -- and weakly left, by the same barycentric average on the first coordinate
    refine carrier_left_of_vertices T (T.pts 0) (fun k => ?_)
    fin_cases k <;>
      simp [hT, Erdos634.CertCoord.mkTri_pts, Erdos634.CertCoord.mkPt_zero]

end Erdos634.RouteOneWallOnly
