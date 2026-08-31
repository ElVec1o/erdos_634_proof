import Erdos634.EdgeDisjoint

/-!
# The wedge overlap at a shared vertex

Erdős #634, the march.  `MarchCoords.bg_then_gb_straddles` is the arithmetic of the `BG → GB`
exclusion: at the shared junction both tiles' wedges contain the vertical direction.  This file
supplies the geometry that turns that into a kill: **two distinct tiles of a dissection sharing a
vertex cannot both open toward a common direction** — a common `v` strictly inside both wedges
would put `x + ε•v` in both interiors, and a dissection's interiors are disjoint.

"Strictly inside the wedge at vertex `k`" is stated barycentrically: both off-vertex coordinates
increase along `v` (`0 < (coord (k+1)).linear v` and `0 < (coord (k+2)).linear v`).  This is the
vertex analogue of `Dissection.cross_disjoint_of_onEdge`, which does the same at a point interior
to an edge; the push lemma is the vertex analogue of `Tri.mem_interior_of_cross_pos`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchOverlap

open Erdos634.Geometry Erdos634.EdgeDisjoint

/-- **The vertex push.**  A direction along which both off-vertex coordinates increase leads from
the vertex into the interior: for small `ε > 0`, `pts k + ε•v` has all three coordinates positive. -/
theorem Tri.mem_interior_of_vertex_push (T : Tri) (k : Fin 3) {v : Plane}
    (h1 : 0 < ((T.basis.coord (k + 1)).linear) v)
    (h2 : 0 < ((T.basis.coord (k + 2)).linear) v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → T.pts k + ε • v ∈ interior T.carrier := by
  classical
  have hne : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have hne2 : ∀ j : Fin 3, j ≠ j + 2 := by decide
  set Lk : ℝ := ((T.basis.coord k).linear) v with hLk
  refine ⟨1 / (1 + |Lk|), by positivity, ?_⟩
  intro ε hε hεlt
  have hcoord : ∀ j : Fin 3, T.basis.coord j (T.pts k + ε • v)
      = T.basis.coord j (T.pts k) + ε * ((T.basis.coord j).linear) v := fun j =>
    coord_add_smul (T.basis.coord j) (T.pts k) v ε
  have hallpos : ∀ j : Fin 3, 0 < T.basis.coord j (T.pts k + ε • v) := by
    intro j
    have hsplit : j = k ∨ j = k + 1 ∨ j = k + 2 := by
      fin_cases j <;> fin_cases k <;> simp <;> decide
    rcases hsplit with hj | hj | hj <;> rw [hj]
    · have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
      rw [hcoord, e1]
      have habs : |Lk| * ε < 1 := by
        rcases eq_or_lt_of_le (abs_nonneg Lk) with hz | hpos
        · rw [← hz]; linarith
        · calc |Lk| * ε < |Lk| * (1 / (1 + |Lk|)) := by
                exact mul_lt_mul_of_pos_left hεlt hpos
            _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
      have : -(1 : ℝ) < ε * Lk := by
        have := neg_abs_le Lk
        nlinarith [abs_nonneg Lk]
      linarith
    · have e0 : T.basis.coord (k + 1) (T.pts k) = 0 :=
        T.basis.coord_apply_ne (Ne.symm (hne k))
      rw [hcoord, e0]
      have := mul_pos hε h1; linarith
    · have e0 : T.basis.coord (k + 2) (T.pts k) = 0 :=
        T.basis.coord_apply_ne (Ne.symm (hne2 k))
      rw [hcoord, e0]
      have := mul_pos hε h2; linarith
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hallpos
  exact mem_interior.mpr ⟨Metric.ball _ r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩

/-- **Two tiles sharing a vertex cannot open toward a common direction.**  The dissection-level
kill: `v` strictly inside both wedges puts a point in both interiors, contradicting
`interiors_disjoint`.  This is what `MarchCoords.bg_then_gb_straddles` feeds: for `BG → GB` the
vertical at the junction is such a `v`, so that transition never occurs in a dissection. -/
theorem Dissection.wedge_disjoint_at_vertex {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {k₁ k₂ : Fin 3}
    (hshare : (D.tile i₁).pts k₁ = (D.tile i₂).pts k₂) (v : Plane) :
    ¬ (0 < (((D.tile i₁).basis.coord (k₁ + 1)).linear) v
       ∧ 0 < (((D.tile i₁).basis.coord (k₁ + 2)).linear) v
       ∧ 0 < (((D.tile i₂).basis.coord (k₂ + 1)).linear) v
       ∧ 0 < (((D.tile i₂).basis.coord (k₂ + 2)).linear) v) := by
  rintro ⟨h11, h12, h21, h22⟩
  obtain ⟨ε₁, hε₁, hmem₁⟩ := Tri.mem_interior_of_vertex_push (D.tile i₁) k₁ h11 h12
  obtain ⟨ε₂, hε₂, hmem₂⟩ := Tri.mem_interior_of_vertex_push (D.tile i₂) k₂ h21 h22
  set ε := min ε₁ ε₂ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact half_pos (lt_min hε₁ hε₂)
  have h₁ := hmem₁ ε hεpos (by rw [hεdef]; have := min_le_left ε₁ ε₂; linarith)
  have h₂ := hmem₂ ε hεpos (by rw [hεdef]; have := min_le_right ε₁ ε₂; linarith)
  rw [hshare] at h₁
  exact Set.disjoint_left.mp (D.interiors_disjoint hne) h₁ h₂

end Erdos634.MarchOverlap
