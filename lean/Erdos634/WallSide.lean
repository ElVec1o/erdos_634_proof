import Mathlib
import Erdos634.WallFace
import Erdos634.EdgeDisjoint
import Erdos634.Placement

/-!
# The wall coordinate and the barycentric coordinate agree, up to a positive factor

Erdős #634, bridge (c).  `EdgeDisjoint.no_same_side_contact` needs the two tiles at a wall contact
to be on the same side, expressed as an agreement between the strict positivity of their edge
coordinates.  That agreement is not an assumption: for a tile with an edge on the wall, the
barycentric coordinate of the opposite vertex and the wall's slack `c - g` are the *same affine
functional up to a positive factor*, because they agree at all three vertices and an affine
functional is determined there.

So both tiles' edge coordinates are positive exactly where `g < c`, and the same-side hypothesis
holds globally rather than being assumed.

**Non-vacuity.**  The three `False`-concluding theorems here are kills, and each is checked the
same way: no proper subset of the hypotheses is already inconsistent.  For `no_wall_contact`,
dropping `hxS` leaves a tile with a wall edge and a point in its edge's relative interior, which is
satisfiable; for `no_two_wall_edges` and `wall_edges_same_tile`, dropping the second edge's wall
condition leaves a tile with one wall edge, likewise satisfiable.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WallSide

open Erdos634.Geometry

/-- **The slack is the barycentric coordinate, scaled.**  If the two vertices other than `k` lie on
the wall, then `c - g y = (c - g (pts k)) · coord k y` for every `y`. -/
theorem slack_eq_coord (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (k : Fin 3)
    (h1 : g (T.pts (k + 1)) = c) (h2 : g (T.pts (k + 2)) = c) (y : Plane) :
    c - g y = (c - g (T.pts k)) * T.basis.coord k y := by
  have hb := Erdos634.WallFace.affine_barycentric T g y
  have hw : T.basis.coord 0 y + T.basis.coord 1 y + T.basis.coord 2 y = 1 := by
    have := T.basis.sum_coord_apply_eq_one (k := ℝ) y
    rwa [Fin.sum_univ_three] at this
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · simp only [show ((0:Fin 3)+1) = 1 from rfl, show ((0:Fin 3)+2) = 2 from rfl] at h1 h2
    rw [hb, h1, h2]; linear_combination (-c) * hw
  · simp only [show ((1:Fin 3)+1) = 2 from rfl, show ((1:Fin 3)+2) = 0 from rfl] at h1 h2
    rw [hb, h1, h2]; linear_combination (-c) * hw
  · simp only [show ((2:Fin 3)+1) = 0 from rfl, show ((2:Fin 3)+2) = 1 from rfl] at h1 h2
    rw [hb, h1, h2]; linear_combination (-c) * hw

/-- **The side test.**  With the wall edge opposite `k` and the tile strictly inside at `pts k`,
the barycentric coordinate is positive exactly where `g` is below `c`. -/
theorem coord_pos_iff (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (k : Fin 3)
    (h1 : g (T.pts (k + 1)) = c) (h2 : g (T.pts (k + 2)) = c) (h3 : g (T.pts k) < c) (y : Plane) :
    0 < T.basis.coord k y ↔ g y < c := by
  have hs := slack_eq_coord T g c k h1 h2 y
  have hpos : 0 < c - g (T.pts k) := by linarith
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Same side, derived.**  Two tiles each carrying a wall edge have their edge coordinates
positive on the same set: the open half-plane `g < c`.  This is exactly the hypothesis
`EdgeDisjoint.interiors_meet_of_same_side` asks for. -/
theorem same_side (T S : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (k l : Fin 3)
    (hT1 : g (T.pts (k + 1)) = c) (hT2 : g (T.pts (k + 2)) = c) (hT3 : g (T.pts k) < c)
    (hS1 : g (S.pts (l + 1)) = c) (hS2 : g (S.pts (l + 2)) = c) (hS3 : g (S.pts l) < c) :
    ∀ y : Plane, 0 < T.basis.coord k y ↔ 0 < S.basis.coord l y := by
  intro y
  rw [coord_pos_iff T g c k hT1 hT2 hT3 y, coord_pos_iff S g c l hS1 hS2 hS3 y]

/-- **No wall contact between distinct tiles.**  Two distinct tiles of a dissection, each with an
edge on the wall and its opposite vertex strictly inside, share no point in the relative interiors
of those edges.  The same-side hypothesis of `no_same_side_contact` is discharged by `same_side`. -/
theorem no_wall_contact {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (i j : Fin N) (hij : i ≠ j) (k l : Fin 3) (x : Plane)
    (hxT : x ∈ (D.tile i).carrier) (hxS : x ∈ (D.tile j).carrier)
    (hT1 : g ((D.tile i).pts (k + 1)) = c) (hT2 : g ((D.tile i).pts (k + 2)) = c)
    (hT3 : g ((D.tile i).pts k) < c)
    (hS1 : g ((D.tile j).pts (l + 1)) = c) (hS2 : g ((D.tile j).pts (l + 2)) = c)
    (hS3 : g ((D.tile j).pts l) < c)
    (hTp1 : 0 < (D.tile i).basis.coord (k + 1) x) (hTp2 : 0 < (D.tile i).basis.coord (k + 2) x)
    (hSp1 : 0 < (D.tile j).basis.coord (l + 1) x) (hSp2 : 0 < (D.tile j).basis.coord (l + 2) x) :
    False :=
  Erdos634.EdgeDisjoint.no_same_side_contact D i j hij k l x hxT hxS hTp1 hTp2 hSp1 hSp2
    (same_side (D.tile i) (D.tile j) g c k l hT1 hT2 hT3 hS1 hS2 hS3)

/-- **Two distinct edges of one tile cannot both lie on the wall.**  Their endpoints exhaust the
tile's three vertices, and a functional equal at all three is constant
(`Placement.no_double_wall_tile`). -/
theorem no_two_wall_edges (T : Tri) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (hlin : ∃ y, g y ≠ c)
    (k l : Fin 3) (hkl : k ≠ l)
    (hk : g (T.pts k) = c ∧ g (T.pts (k + 1)) = c)
    (hl : g (T.pts l) = c ∧ g (T.pts (l + 1)) = c) : False := by
  have hall : ∀ j : Fin 3, g (T.pts j) = c := by
    intro j
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    have hl3 : l = 0 ∨ l = 1 ∨ l = 2 := by fin_cases l <;> simp
    have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
    rcases hk3 with rfl | rfl | rfl <;> rcases hl3 with rfl | rfl | rfl <;>
      rcases hj3 with rfl | rfl | rfl <;>
      simp_all [show ((0:Fin 3)+1) = 1 from rfl, show ((1:Fin 3)+1) = 2 from rfl,
        show ((2:Fin 3)+1) = 0 from rfl]
  exact Erdos634.Placement.no_double_wall_tile T g c hlin (hall 0) (hall 1) (hall 2)

/-- **Consecutive chain edges belong to distinct tiles.**  Two wall edges of the same tile are the
same edge. -/
theorem wall_edges_same_tile {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hlin : ∃ y, g y ≠ c) (e f : Fin N × Fin 3) (hef : e ≠ f) (htile : e.1 = f.1)
    (he : g ((D.tile e.1).pts e.2) = c ∧ g ((D.tile e.1).pts (e.2 + 1)) = c)
    (hf : g ((D.tile f.1).pts f.2) = c ∧ g ((D.tile f.1).pts (f.2 + 1)) = c) : False := by
  have hne : e.2 ≠ f.2 := by
    intro h; exact hef (Prod.ext htile h)
  rw [← htile] at hf
  exact no_two_wall_edges (D.tile e.1) g c hlin e.2 f.2 hne he hf

end Erdos634.WallSide
