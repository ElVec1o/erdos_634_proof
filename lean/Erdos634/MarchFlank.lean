import Erdos634.TilePlacement
import Erdos634.AngleSumDissection

/-!
# The two corners flanking an `a`-edge are the `β`- and `γ`-corners

The clause obligation (i) still needs on a boundary run: a tile laying its `a`-edge on the line
presents `β` at one end and `γ` at the other, never `α`.  The reason is that `α` is the angle
*opposite* `a`, so the `α`-corner is the apex and is not on the line at all; the two corners on the
line are those opposite `b` and `c`, which carry `β` and `γ`.

Formally the ordering does it: the angles of a triangle are ordered as their opposite sides
(`TilePlacement.angleAt_lt`), so with `a < b < c` the angle opposite `a` is strictly smallest.  A
corner *on* the `a`-edge is one of the other two, hence carries one of the two larger angles.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchFlank

open Erdos634.Geometry Erdos634.TilePlacement

/-- **The angles are ordered as their opposite sides.**  With the full chain
`sideOpp j < sideOpp (j+1) < sideOpp (j+2)` — for our tile, `a < b < c` — the angles chain the same
way, so the angle opposite the shortest side is strictly the smallest of the three. -/
theorem apex_angle_smallest (T : Tri) (j : Fin 3)
    (h1 : sideOpp T j < sideOpp T (j + 1)) (h2 : sideOpp T (j + 1) < sideOpp T (j + 2)) :
    angleAt T j < angleAt T (j + 1) ∧ angleAt T (j + 1) < angleAt T (j + 2) := by
  refine ⟨angleAt_lt T j h1, ?_⟩
  have hsh : ∀ x : Fin 3, x + 1 + 1 = x + 2 := by decide
  have h := angleAt_lt T (j + 1) (by rw [hsh]; exact h2)
  rwa [hsh] at h

/-- Neither endpoint of side `j` is the vertex `j`. -/
theorem endpoints_ne_apex : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j := by decide

/-- **The dichotomy, in the form `junction_cases` consumes.**  If the tile's three angles are
`{α, β, γ}` with `α` strictly smallest, and a corner of the tile carries an angle that is *not*
`α`, then it carries `β` or `γ`. -/
theorem beta_or_gamma {α β γ θ : ℝ} (hmem : θ = α ∨ θ = β ∨ θ = γ) (hne : θ ≠ α) :
    θ = β ∨ θ = γ := by
  rcases hmem with h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr h

/-- **Assembled**: a corner at an endpoint of the shortest side carries an angle strictly greater
than the apex angle, hence different from it, hence `β` or `γ`. -/
theorem flank_is_beta_or_gamma (T : Tri) (j : Fin 3) {α β γ : ℝ}
    (h1 : sideOpp T j < sideOpp T (j + 1)) (h2 : sideOpp T (j + 1) < sideOpp T (j + 2))
    (hapex : angleAt T j = α)
    (hmem1 : angleAt T (j + 1) = α ∨ angleAt T (j + 1) = β ∨ angleAt T (j + 1) = γ)
    (hmem2 : angleAt T (j + 2) = α ∨ angleAt T (j + 2) = β ∨ angleAt T (j + 2) = γ) :
    (angleAt T (j + 1) = β ∨ angleAt T (j + 1) = γ)
      ∧ (angleAt T (j + 2) = β ∨ angleAt T (j + 2) = γ) := by
  obtain ⟨o1, o2⟩ := apex_angle_smallest T j h1 h2
  refine ⟨beta_or_gamma hmem1 ?_, beta_or_gamma hmem2 ?_⟩
  · rw [← hapex]; exact ne_of_gt o1
  · rw [← hapex]; exact ne_of_gt (lt_trans o1 o2)

/-! ## The dichotomy as a statement about a *placed* tile

`flank_is_beta_or_gamma` speaks of `angleAt`, the tile's own corner angle.  What
`MarchRun.junction_cases` consumes is `localAngle` — what a tile of a dissection *presents* at a
point.  `Tri.localAngle_vertex` closes that seam: at its own vertex a tile's local angle is its
corner angle.  So the dichotomy transfers verbatim to a placed tile sitting at a junction. -/

/-- **What a placed tile presents at an endpoint of its `a`-edge.**  If the tile's `j`-th side is
strictly its shortest and the angles are `α, β, γ` with `angleAt T j = α`, then at either endpoint
of that side the tile presents `β` or `γ`. -/
theorem presents_beta_or_gamma (T : Tri) (j : Fin 3) {α β γ : ℝ}
    (h1 : sideOpp T j < sideOpp T (j + 1)) (h2 : sideOpp T (j + 1) < sideOpp T (j + 2))
    (hapex : angleAt T j = α)
    (hmem1 : angleAt T (j + 1) = α ∨ angleAt T (j + 1) = β ∨ angleAt T (j + 1) = γ)
    (hmem2 : angleAt T (j + 2) = α ∨ angleAt T (j + 2) = β ∨ angleAt T (j + 2) = γ) :
    (T.localAngle (T.pts (j + 1)) = β ∨ T.localAngle (T.pts (j + 1)) = γ)
      ∧ (T.localAngle (T.pts (j + 2)) = β ∨ T.localAngle (T.pts (j + 2)) = γ) := by
  obtain ⟨g1, g2⟩ := flank_is_beta_or_gamma T j h1 h2 hapex hmem1 hmem2
  constructor
  · rw [Erdos634.Geometry.Tri.localAngle_vertex]
    simpa [angleAt] using g1
  · rw [Erdos634.Geometry.Tri.localAngle_vertex]
    simpa [angleAt] using g2

/-! ## Corner angles are positive

Recorded in the research log as the revival route for `RouteOne`'s `hne0`: prove this standalone,
next to the non-degeneracy machinery, rather than inline inside a four-way `split` on `localAngle`
(where two attempts timed out).

An angle of `0` forces the degenerate distance identity `dist p₁ p₃ = |dist p₁ p₂ - dist p₃ p₂|`
(Mathlib's `dist_eq_abs_sub_dist_of_angle_eq_zero`), which the strict triangle inequality
`TilePlacement.strict_triangle_pts` forbids. -/

/-- **A tile's corner angle is strictly positive.** -/
theorem cornerAngle_pos (T : Tri) (j : Fin 3) :
    0 < cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) := by
  rcases eq_or_lt_of_le (EuclideanGeometry.angle_nonneg
    (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exfalso
    have hz : cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) = 0 := h.symm
    rw [Erdos634.Geometry.cornerAngle] at hz
    have hdeg := EuclideanGeometry.dist_eq_abs_sub_dist_of_angle_eq_zero hz
    have hstrict := strict_triangle_pts T j
    rcases abs_cases (dist (T.pts (j + 1)) (T.pts j) - dist (T.pts (j + 2)) (T.pts j)) with
      ⟨he, _⟩ | ⟨he, _⟩
    · rw [he, dist_comm (T.pts (j + 1)) (T.pts j),
        dist_comm (T.pts (j + 2)) (T.pts j)] at hdeg
      linarith
    · -- the other degeneracy: `j+1` between `j` and `j+2`; use the inequality at index `j+2`
      have h2 := strict_triangle_pts T (j + 2)
      have e1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
      have e2 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
      rw [e1, e2] at h2
      rw [he, dist_comm (T.pts (j + 1)) (T.pts j),
        dist_comm (T.pts (j + 2)) (T.pts j)] at hdeg
      rw [dist_comm (T.pts (j + 2)) (T.pts j),
        dist_comm (T.pts (j + 2)) (T.pts (j + 1))] at h2
      linarith
  · exact h

private theorem third_index : ∀ j k : Fin 3, j ≠ k → ∃ m, m ≠ j ∧ m ≠ k := by decide

private theorem index_trichotomy :
    ∀ i j k m : Fin 3, j ≠ k → m ≠ j → m ≠ k → i ≠ m → i = j ∨ i = k := by decide

/-- **A carrier point has nonzero local angle.**

The `localAngle` of a triangle vanishes only off the closed triangle.  The four cases:
at a vertex the value is a corner angle, positive by `cornerAngle_pos`; at an interior point it
is `2π`; at an edge-interior point it is `π`; and the fourth branch is impossible for a carrier
point, because a non-vertex point of the carrier has all coordinates `≥ 0` summing to `1`, so at
most one of them vanishes — two vanishing coordinates force the third to be `1` and the point to
*be* the opposite vertex, by `AffineBasis.ext_elem`.

This discharges the `hne0` field of `RouteOne.EscapeData`, which was carried as a hypothesis. -/
theorem localAngle_ne_zero_of_mem (T : Tri) {p : Plane} (hp : p ∈ T.carrier) :
    T.localAngle p ≠ 0 := by
  classical
  have hnn : ∀ i, 0 ≤ T.basis.coord i p := by
    rw [T.carrier_eq_nonneg_coord] at hp; exact hp
  rw [Tri.localAngle]
  split
  · exact ne_of_gt (cornerAngle_pos T _)
  · rename_i hv
    split
    · positivity
    · rename_i hpos
      -- not all coordinates positive: some `k` vanishes (it cannot be negative)
      push_neg at hpos
      obtain ⟨k, hk⟩ := hpos
      have hk0 : T.basis.coord k p = 0 := le_antisymm hk (hnn k)
      -- and it is the *only* one, else `p` would be a vertex
      have huniq : ∀ j, j ≠ k → 0 < T.basis.coord j p := by
        intro j hj
        rcases lt_or_eq_of_le (hnn j) with h | h
        · exact h
        · exfalso
          have hsum := T.basis.sum_coord_apply_eq_one (k := ℝ) p
          obtain ⟨m, hmj, hmk⟩ := third_index j k hj
          have hm1 : T.basis.coord m p = 1 := by
            rw [Fin.sum_univ_three] at hsum
            fin_cases j <;> fin_cases k <;> fin_cases m <;> simp_all <;> linarith
          have hpm : p = T.pts m := by
            refine T.basis.ext_elem fun i => ?_
            have hci : T.basis.coord i (T.pts m) = if i = m then 1 else 0 :=
              AffineBasis.coord_apply T.basis i m
            rw [hci]
            by_cases him : i = m
            · subst him; simp [hm1]
            · have hz : T.basis.coord i p = 0 := by
                rcases index_trichotomy i j k m hj hmj hmk him with h' | h'
                · rw [h', ← h]
                · rw [h', hk0]
              simp [him, hz]
          exact hv ⟨m, hpm⟩
      split
      · exact Real.pi_ne_zero
      · rename_i hedge
        exact absurd ⟨k, hk0, huniq⟩ hedge

end Erdos634.MarchFlank
