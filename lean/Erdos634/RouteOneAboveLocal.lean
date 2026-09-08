import Erdos634.RouteOne
import Erdos634.CertCoord

/-!
# `habove` is a *local* condition, and it is what a through-edge below the wall supplies

Written 2026-09-09.

`RouteOne.escape_flank` — and through it `route_one_flank_composed`, `escape_data_flank`, and the
`habove` field of `RouteOne.EscapeData` — asks that the serving tile's **whole carrier** lie weakly
above the wall.  That is much more than the argument uses.  `weakly_upward_of_above` extracts from
it only the two vertex signs at `V`, and by convexity those are already determined by the tile's
behaviour in an *arbitrarily small* neighbourhood of `V`.

This file records that reduction and the consequence that matters for the march:

* `vertex_signs_of_local_above` — a tile weakly above `V` **near** `V` has both edge directions at
  `V` weakly upward.  (Convexity: walk a little way along each edge.)
* `escape_flank_local`, `route_one_flank_composed_local` — the flank conclusion with the global
  `habove` replaced by its local form.
* `route_one_flank_composed` is re-derived from the local version (`..._of_global`), which is the
  non-vacuity witness: the new hypothesis is implied by the old one, with `r = 1`.
* `local_above_of_lower_halfdisc` — the local condition *follows* from the statement that some
  other tile `b` covers a lower half-disc at `V`.  No sign hypothesis on the serving tile at all.

## What this changes, stated honestly

It does **not** prove `habove` at a new march position.  What it does is replace an obligation about
a tile that has not yet been identified (the *new* serving tile, whatever it turns out to be) by an
obligation about a tile the cascade does forcibly name: the tile **below** the wall.  Concretely,
`route_one_flank_of_through_edge_below` derives the flank conclusion at `V` from

  "some tile `b ≠ i` contains the lower half-disc of radius `r` at `V`",

which is exactly the paper's already-named unproved input to `conj:advance` — *that a through-edge,
rather than a junction, runs below the line at `V`* (`erdos-634-companion.tex`, `conj:advance`; see
also `OrderForcing.lean:900`).  So gap (A) of the march step is not a new gap: it collapses onto a
gap the paper already lists, and the collapse is by the two lemmas below.

It also does not decide whether that input can be established at a *new* march position; the
`c`-edge of `rem:route1uniform` **ends** at `V`, so the below-edge there does not automatically
extend past `E`.  That remains open.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.RouteOne

open Erdos634.Geometry

/-! ## The local reduction -/

/-- **A tile weakly above `V` near `V` has weakly upward edge directions at `V`.**

Only the behaviour of `T` inside `Metric.ball (T.pts k) r` is used.  The proof walks a short way
from the vertex along each of the two edges: the point stays in the (convex) carrier, and lands
inside the ball once the parameter is small enough, so its height above `T.pts k` is `≥ 0`; dividing
by the positive parameter gives the vertex sign. -/
theorem vertex_signs_of_local_above (T : Tri) (k : Fin 3) {r : ℝ} (hr : 0 < r)
    (h : ∀ q : Plane, q ∈ T.carrier → dist q (T.pts k) < r → 0 ≤ (q - T.pts k) 1) :
    0 ≤ (T.pts (k + 1) - T.pts k) 1 ∧ 0 ≤ (T.pts (k + 2) - T.pts k) 1 := by
  have key : ∀ j : Fin 3, 0 ≤ (T.pts j - T.pts k) 1 := by
    intro j
    set v : Plane := T.pts j - T.pts k with hv
    -- choose a small positive step
    set t : ℝ := min (1 : ℝ) (r / (2 * (‖v‖ + 1))) with ht
    have hnorm : (0:ℝ) < ‖v‖ + 1 := by positivity
    have htpos : 0 < t := lt_min one_pos (by positivity)
    have htle : t ≤ 1 := min_le_left _ _
    have htr : t * ‖v‖ < r := by
      have h1 : t ≤ r / (2 * (‖v‖ + 1)) := min_le_right _ _
      have h2 : t * ‖v‖ ≤ (r / (2 * (‖v‖ + 1))) * ‖v‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have h3 : (r / (2 * (‖v‖ + 1))) * ‖v‖ < r := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg v]
      linarith
    -- the point `T.pts k + t • v` lies in the carrier
    have hmemk : T.pts k ∈ T.carrier := subset_convexHull ℝ _ ⟨k, rfl⟩
    have hmemj : T.pts j ∈ T.carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
    have hseg : T.pts k + t • v ∈ T.carrier := by
      have := T.convex hmemk hmemj (by linarith : (0:ℝ) ≤ 1 - t) htpos.le (by ring)
      have heq : (1 - t) • T.pts k + t • T.pts j = T.pts k + t • v := by
        rw [hv]; module
      rwa [heq] at this
    have hdist : dist (T.pts k + t • v) (T.pts k) < r := by
      rw [dist_eq_norm]
      have : T.pts k + t • v - T.pts k = t • v := by abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      exact htr
    have hnn := h _ hseg hdist
    have hco : (T.pts k + t • v - T.pts k) 1 = t * (v 1) := by
      have : T.pts k + t • v - T.pts k = t • v := by abel
      rw [this]
      simp
    rw [hco] at hnn
    exact nonneg_of_mul_nonneg_right hnn htpos
  exact ⟨key _, key _⟩

/-- **The escape flank from the local hypothesis.**  `escape_flank` with `habove` weakened to hold
only inside a ball around the vertex. -/
theorem escape_flank_local (T : Tri) (k : Fin 3) {r : ℝ} (hr : 0 < r)
    (habove : ∀ q : Plane, q ∈ T.carrier → dist q (T.pts k) < r → 0 ≤ (q - T.pts k) 1)
    (htan : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ T.carrier ∧
      0 < (q - T.pts k) 0 ∧ (q - T.pts k) 1 ≤ δ * ((q - T.pts k) 0)) :
    ((T.pts (k + 1) - T.pts k) 1 = 0 ∧ 0 < (T.pts (k + 1) - T.pts k) 0) ∨
    ((T.pts (k + 2) - T.pts k) 1 = 0 ∧ 0 < (T.pts (k + 2) - T.pts k) 0) :=
  flank_along_line' T k (vertex_signs_of_local_above T k hr habove).1
    (vertex_signs_of_local_above T k hr habove).2 htan

/-! ## The flank conclusion, with `habove` local -/

/-- **Route 1's flank, with the vertex hypothesis discharged and `habove` localized.**  Identical to
`route_one_flank_composed` except that the serving tile need only lie weakly above `V` within some
ball around `V`. -/
theorem route_one_flank_composed_local {N : ℕ} (D : Dissection N) (V : Plane) (i b : Fin N)
    (hib : i ≠ b)
    (hcard : ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card = 1)
    (hb : (D.tile b).localAngle V = Real.pi)
    (hne0 : (D.tile i).localAngle V ≠ 0)
    (hne2pi : (D.tile i).localAngle V ≠ 2 * Real.pi)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0))
    {r : ℝ} (hr : 0 < r)
    (habove : ∀ q : Plane, q ∈ (D.tile i).carrier → dist q V < r → 0 ≤ (q - V) 1) :
    ∃ k : Fin 3, (D.tile i).pts k = V ∧
      ((((D.tile i).pts (k + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 1) - V) 0) ∨
       (((D.tile i).pts (k + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 2) - V) 0)) := by
  obtain ⟨k, hk⟩ := serving_has_vertex D i V hne0 hne2pi
    (not_straight_of_unique D V hcard b hb i hib)
  refine ⟨k, hk, ?_⟩
  have h := escape_flank_local (D.tile i) k hr (by rw [hk]; exact habove) (by rw [hk]; exact hserve)
  rw [hk] at h
  exact h

/-- **Non-vacuity witness.**  The local hypothesis is *implied* by the global one (take `r = 1`), so
`route_one_flank_composed_local` subsumes `route_one_flank_composed`; in particular its hypothesis
set is satisfied by every configuration the original theorem applies to. -/
theorem route_one_flank_composed_of_global {N : ℕ} (D : Dissection N) (V : Plane) (i b : Fin N)
    (hib : i ≠ b)
    (hcard : ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card = 1)
    (hb : (D.tile b).localAngle V = Real.pi)
    (hne0 : (D.tile i).localAngle V ≠ 0)
    (hne2pi : (D.tile i).localAngle V ≠ 2 * Real.pi)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0))
    (habove : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1) :
    ∃ k : Fin 3, (D.tile i).pts k = V ∧
      ((((D.tile i).pts (k + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 1) - V) 0) ∨
       (((D.tile i).pts (k + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 2) - V) 0)) :=
  route_one_flank_composed_local D V i b hib hcard hb hne0 hne2pi hserve one_pos
    (fun q hq _ => habove q hq)

/-! ## Where the local condition comes from: the tile below the wall

The point of localizing is that the local condition is supplied by a tile *other than the serving
tile*.  If some tile `b` covers the lower half-disc at `V`, then no other tile has a point there,
because tile interiors are disjoint and an open lower half-disc consists of interior points of `b`.
-/

/-- The open lower half-disc at `V` of radius `r`. -/
def lowerHalfDisc (V : Plane) (r : ℝ) : Set Plane :=
  {q : Plane | dist q V < r ∧ (q - V) 1 < 0}

theorem isOpen_lowerHalfDisc (V : Plane) (r : ℝ) : IsOpen (lowerHalfDisc V r) := by
  have hcont : Continuous fun q : Plane => (q - V) 1 := by
    exact ((EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous).comp
      (continuous_id.sub continuous_const)
  have h1 : IsOpen {q : Plane | dist q V < r} := by
    simpa [Metric.ball, Set.mem_setOf_eq] using (Metric.isOpen_ball (x := V) (ε := r))
  have h2 : IsOpen {q : Plane | (q - V) 1 < 0} := isOpen_lt hcont continuous_const
  exact h1.inter h2

/-- **The lower half-disc lies in `b`'s interior once it lies in `b`'s carrier.**  It is open, so
containment in the carrier already gives containment in the interior. -/
theorem lowerHalfDisc_subset_interior {T : Tri} {V : Plane} {r : ℝ}
    (h : lowerHalfDisc V r ⊆ T.carrier) :
    lowerHalfDisc V r ⊆ interior T.carrier :=
  interior_maximal h (isOpen_lowerHalfDisc V r)

/-- **A covered lower half-disc gives the local `habove` for every other tile.**

This is the step that removes the circularity of gap (A): the hypothesis is about the tile *below*
the wall, which the cascade names, not about the serving tile, which it does not. -/
theorem local_above_of_lower_halfdisc {N : ℕ} (D : Dissection N) {i b : Fin N} (hib : i ≠ b)
    {V : Plane} {r : ℝ} (hcover : lowerHalfDisc V r ⊆ (D.tile b).carrier) :
    ∀ q : Plane, q ∈ (D.tile i).carrier → dist q V < r → 0 ≤ (q - V) 1 := by
  intro q hq hd
  rcases le_or_gt 0 ((q - V) 1) with h | hneg
  · exact h
  · exact absurd (lowerHalfDisc_subset_interior hcover ⟨hd, hneg⟩)
      (Dissection.not_mem_interior_of_mem D hib hq)

/-- **Route 1's flank from a through-edge below the wall.**

The `habove` obligation is discharged entirely: the only hypothesis about the region below `V` is
that the tile `b` carrying the straight angle there also covers a lower half-disc at `V` — which is
what "a through-edge, rather than a junction, runs below the line at `V`" means locally.  Nothing is
assumed about the serving tile's carrier. -/
theorem route_one_flank_of_through_edge_below {N : ℕ} (D : Dissection N) (V : Plane) (i b : Fin N)
    (hib : i ≠ b)
    (hcard : ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card = 1)
    (hb : (D.tile b).localAngle V = Real.pi)
    (hne0 : (D.tile i).localAngle V ≠ 0)
    (hne2pi : (D.tile i).localAngle V ≠ 2 * Real.pi)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0))
    {r : ℝ} (hr : 0 < r) (hcover : lowerHalfDisc V r ⊆ (D.tile b).carrier) :
    ∃ k : Fin 3, (D.tile i).pts k = V ∧
      ((((D.tile i).pts (k + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 1) - V) 0) ∨
       (((D.tile i).pts (k + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 2) - V) 0)) :=
  route_one_flank_composed_local D V i b hib hcard hb hne0 hne2pi hserve hr
    (local_above_of_lower_halfdisc D hib hcover)

/-! ## Non-vacuity of the covering hypothesis

`hcover` is a real geometric condition, and it is satisfiable: a triangle with `V` in the relative
interior of one of its edges, lying below that edge, contains the lower half-disc at `V` once the
radius is small enough.  Witness: `A = (0,0)`, `B = (1,-1)`, `C = (2,0)`, `V = (1,0)`, `r = 1/2`. -/

theorem mkPt_self (q : Plane) : Erdos634.CertCoord.mkPt (q 0) (q 1) = q := by
  refine PiLp.ext ?_
  intro i
  fin_cases i <;> simp

/-- The witness triangle: `(0,0)`, `(1,-1)`, `(2,0)`, positively oriented. -/
noncomputable def witnessTri : Tri :=
  Erdos634.CertCoord.mkTri 0 0 1 (-1) 2 0 (by norm_num [Erdos634.CertCoord.det3])

/-- **`hcover` is satisfiable.**  The lower half-disc of radius `1/2` at `(1,0)` lies in the
witness triangle, so `route_one_flank_of_through_edge_below` is not a conditional with an
unsatisfiable hypothesis. -/
theorem witness_cover :
    lowerHalfDisc (Erdos634.CertCoord.mkPt 1 0) (1/2) ⊆ witnessTri.carrier := by
  rintro q ⟨hd, hy⟩
  have hq : q = Erdos634.CertCoord.mkPt (q 0) (q 1) := (mkPt_self q).symm
  set a := q 0 with ha
  set b := q 1 with hb
  -- the sign condition, rewritten in coordinates
  have hbneg : b < 0 := by
    have : (q - Erdos634.CertCoord.mkPt 1 0) 1 = b := by
      simp [hb]
    rwa [this] at hy
  -- the distance condition, rewritten in coordinates
  have hsq : (a - 1) ^ 2 + (b - 0) ^ 2 < (1/2 : ℝ) ^ 2 := by
    have hdd : dist (Erdos634.CertCoord.mkPt a b) (Erdos634.CertCoord.mkPt 1 0) < 1/2 := by
      rw [← hq]; exact hd
    have h0 : (0:ℝ) ≤ dist (Erdos634.CertCoord.mkPt a b) (Erdos634.CertCoord.mkPt 1 0) :=
      dist_nonneg
    have := Erdos634.CertCoord.dist_sq_mkPt a b 1 0
    nlinarith
  have hax : (1:ℝ)/2 < a := by nlinarith
  have hax' : a < (3:ℝ)/2 := by nlinarith
  have hby : -(1:ℝ)/2 < b := by nlinarith
  rw [hq]
  exact Erdos634.CertCoord.mem_carrier_of_dets (by norm_num [Erdos634.CertCoord.det3])
    (by simp only [Erdos634.CertCoord.det3]; nlinarith)
    (by simp only [Erdos634.CertCoord.det3]; nlinarith)
    (by simp only [Erdos634.CertCoord.det3]; nlinarith)

end Erdos634.RouteOne
