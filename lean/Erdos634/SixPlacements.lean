import Erdos634.PlacementCompleteness
import Erdos634.Congruence

/-!
# The six placements at a forced corner

Erdős #634, companion to `PlacementCompleteness.lean`.  Once a tile is known to have a vertex at
`v`, a second vertex on the ray `v + ℝ₊·d` (`d` a unit vector) and its third vertex strictly
counter-clockwise of `d`, the tile is determined by which of its three side lengths lies along
`d` and which is the other side at `v`:

* `third_vertex` — for side lengths `ℓ₁` (along `d`), `ℓ₂` (the other side at `v`) and `ℓ₃`
  (opposite `v`), the third vertex is `v + p·d + q·d^⊥` with
  `p = (ℓ₁² + ℓ₂² − ℓ₃²)/(2ℓ₁)` and `q = √(ℓ₂² − p²) > 0`.  **The orientation is forced**: the
  counter-clockwise hypothesis fixes the sign of `q`.  So the paper's "two choices being mirror
  images" is the choice of *which adjacent side lies along `d`* — the reflection of the tile in
  the bisector at `v` — not a chirality choice.
* `sides_perm_of_congruent` — for a tile congruent to a model with sides `a, b, c`, the ordered
  triple `(ℓ₁, ℓ₂, ℓ₃)` is one of the six permutations of `(a, b, c)`.
* `six_placements` — the composition: the second vertex is `v + ℓ₁·d` and the third is
  `placeThird v d ℓ₁ ℓ₂ ℓ₃`, for one of the six triples.  Three corner types (which of `a, b, c`
  is `ℓ₃`, the side opposite `v`) times two (which adjacent side is `ℓ₁`).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SixPlacements

open Erdos634.Geometry Erdos634.PlacementCompleteness

/-- The third vertex of the placement with side `ℓ₁` along `d`, side `ℓ₂` at `v`, opposite side
`ℓ₃`, tile counter-clockwise of `d`. -/
noncomputable def placeThird (v d : Plane) (ℓ₁ ℓ₂ ℓ₃ : ℝ) : Plane :=
  v + ((ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) / (2 * ℓ₁)) • d
    + Real.sqrt (ℓ₂ ^ 2 - ((ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) / (2 * ℓ₁)) ^ 2) • perp d

/-- The length of `c • d` for a unit `d` and `c > 0`. -/
theorem dist_smul_unit (v d : Plane) (hunit : d 0 ^ 2 + d 1 ^ 2 = 1) {c : ℝ} (hc : 0 < c) :
    dist v (v + c • d) = c := by
  have hsq : dist v (v + c • d) ^ 2 = c ^ 2 := by
    rw [dist_sq_coord]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination c ^ 2 * hunit
  nlinarith [dist_nonneg (x := v) (y := v + c • d)]

/-- **The third vertex is determined by the three side lengths and the orientation.** -/
theorem third_vertex (v d w : Plane) (hunit : d 0 ^ 2 + d 1 ^ 2 = 1) (ℓ₁ ℓ₂ ℓ₃ : ℝ)
    (hℓ₁ : 0 < ℓ₁) (h₂ : dist w v = ℓ₂) (h₃ : dist w (v + ℓ₁ • d) = ℓ₃)
    (hccw : 0 < cross d (w - v)) :
    w = placeThird v d ℓ₁ ℓ₂ ℓ₃ := by
  set P := d 0 * (w 0 - v 0) + d 1 * (w 1 - v 1) with hP
  set Q := cross d (w - v) with hQ
  have hQ' : Q = d 0 * (w 1 - v 1) - d 1 * (w 0 - v 0) := by
    rw [hQ]; simp [cross]
  -- the orthogonal decomposition
  have hdec : w = v + P • d + Q • perp d := by
    refine plane_ext ?_ ?_
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, perp_zero, hP, hQ']
      linear_combination (-(w 0 - v 0)) * hunit
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, perp_one, hP, hQ']
      linear_combination (-(w 1 - v 1)) * hunit
  -- the two distance equations
  have e₂ : P ^ 2 + Q ^ 2 = ℓ₂ ^ 2 := by
    rw [← h₂, dist_sq_coord, hP, hQ']
    linear_combination ((w 0 - v 0) ^ 2 + (w 1 - v 1) ^ 2) * hunit
  have e₃ : (P - ℓ₁) ^ 2 + Q ^ 2 = ℓ₃ ^ 2 := by
    rw [← h₃, dist_sq_coord, hP, hQ']
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination ((w 0 - v 0) ^ 2 + (w 1 - v 1) ^ 2 - ℓ₁ ^ 2) * hunit
  have hPval : P = (ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) / (2 * ℓ₁) := by
    rw [eq_div_iff (by positivity)]
    linear_combination e₂ - e₃
  have hQval : Real.sqrt (ℓ₂ ^ 2 - ((ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) / (2 * ℓ₁)) ^ 2) = Q := by
    rw [← hPval, show ℓ₂ ^ 2 - P ^ 2 = Q ^ 2 by linarith]
    exact Real.sqrt_sq hccw.le
  rw [placeThird, hQval, ← hPval]
  exact hdec

/-- **The ordered side triple of a tile congruent to `(a, b, c)` at a chosen corner is one of
the six permutations.** `k₀` is the corner, `k₁` the vertex along the ray, `k₂` the third. -/
theorem sides_perm_of_congruent {T M : Tri} (h : T.Congruent M) {a b c : ℝ}
    (hMa : dist (M.pts 0) (M.pts 1) = a) (hMb : dist (M.pts 1) (M.pts 2) = b)
    (hMc : dist (M.pts 0) (M.pts 2) = c)
    (k₀ k₁ k₂ : Fin 3) (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂) :
    (dist (T.pts k₀) (T.pts k₁) = a ∧ dist (T.pts k₀) (T.pts k₂) = c ∧ dist (T.pts k₁) (T.pts k₂) = b) ∨
    (dist (T.pts k₀) (T.pts k₁) = c ∧ dist (T.pts k₀) (T.pts k₂) = a ∧ dist (T.pts k₁) (T.pts k₂) = b) ∨
    (dist (T.pts k₀) (T.pts k₁) = a ∧ dist (T.pts k₀) (T.pts k₂) = b ∧ dist (T.pts k₁) (T.pts k₂) = c) ∨
    (dist (T.pts k₀) (T.pts k₁) = b ∧ dist (T.pts k₀) (T.pts k₂) = a ∧ dist (T.pts k₁) (T.pts k₂) = c) ∨
    (dist (T.pts k₀) (T.pts k₁) = c ∧ dist (T.pts k₀) (T.pts k₂) = b ∧ dist (T.pts k₁) (T.pts k₂) = a) ∨
    (dist (T.pts k₀) (T.pts k₁) = b ∧ dist (T.pts k₀) (T.pts k₂) = c ∧ dist (T.pts k₁) (T.pts k₂) = a) := by
  obtain ⟨σ, hσ⟩ := h.dist_eq
  have e1 := hσ k₀ k₁
  have e2 := hσ k₀ k₂
  have e3 := hσ k₁ k₂
  have n01 : σ k₀ ≠ σ k₁ := fun e => h01 (σ.injective e)
  have n02 : σ k₀ ≠ σ k₂ := fun e => h02 (σ.injective e)
  have n12 : σ k₁ ≠ σ k₂ := fun e => h12 (σ.injective e)
  have hfin : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hfin (σ k₀) with h0 | h0 | h0 <;> rcases hfin (σ k₁) with h1 | h1 | h1 <;>
    rcases hfin (σ k₂) with h2 | h2 | h2 <;>
    rw [h0, h1] at n01 <;> rw [h0, h2] at n02 <;> rw [h1, h2] at n12 <;>
    first
    | exact absurd rfl n01
    | exact absurd rfl n02
    | exact absurd rfl n12
    | (rw [h0, h1] at e1; rw [h0, h2] at e2; rw [h1, h2] at e3
       try simp only [dist_comm (M.pts 1) (M.pts 0), dist_comm (M.pts 2) (M.pts 0),
         dist_comm (M.pts 2) (M.pts 1)] at e1 e2 e3
       simp only [hMa, hMb, hMc] at e1 e2 e3
       first
       | exact Or.inl ⟨e1, e2, e3⟩
       | exact Or.inr (Or.inl ⟨e1, e2, e3⟩)
       | exact Or.inr (Or.inr (Or.inl ⟨e1, e2, e3⟩))
       | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e1, e2, e3⟩)))
       | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e1, e2, e3⟩))))
       | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e1, e2, e3⟩)))))

/-- **THE SIX PLACEMENTS.**  A tile congruent to the model `(a, b, c)`, with a corner at `v`,
its next vertex on the ray `v + ℝ₊·d` and its third vertex counter-clockwise of `d`, is one of
exactly six explicit triangles: `(ℓ₁, ℓ₂, ℓ₃)` a permutation of `(a, b, c)`, second vertex
`v + ℓ₁·d`, third vertex `placeThird v d ℓ₁ ℓ₂ ℓ₃`.  Orientation is forced, not chosen. -/
theorem six_placements {T M : Tri} (h : T.Congruent M) {a b c : ℝ}
    (hMa : dist (M.pts 0) (M.pts 1) = a) (hMb : dist (M.pts 1) (M.pts 2) = b)
    (hMc : dist (M.pts 0) (M.pts 2) = c)
    {v d : Plane} (hunit : d 0 ^ 2 + d 1 ^ 2 = 1)
    {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂)
    (hk₀ : T.pts k₀ = v) {c' : ℝ} (hc' : 0 < c') (hk₁ : T.pts k₁ = v + c' • d)
    (hk₂ : 0 < cross d (T.pts k₂ - v)) :
    (T.pts k₁ = v + a • d ∧ T.pts k₂ = placeThird v d a c b) ∨
    (T.pts k₁ = v + c • d ∧ T.pts k₂ = placeThird v d c a b) ∨
    (T.pts k₁ = v + a • d ∧ T.pts k₂ = placeThird v d a b c) ∨
    (T.pts k₁ = v + b • d ∧ T.pts k₂ = placeThird v d b a c) ∨
    (T.pts k₁ = v + c • d ∧ T.pts k₂ = placeThird v d c b a) ∨
    (T.pts k₁ = v + b • d ∧ T.pts k₂ = placeThird v d b c a) := by
  have hℓ₁ : dist (T.pts k₀) (T.pts k₁) = c' := by
    rw [hk₀, hk₁]; exact dist_smul_unit v d hunit hc'
  have key : ∀ ℓ₁ ℓ₂ ℓ₃ : ℝ, dist (T.pts k₀) (T.pts k₁) = ℓ₁ → dist (T.pts k₀) (T.pts k₂) = ℓ₂ →
      dist (T.pts k₁) (T.pts k₂) = ℓ₃ →
      T.pts k₁ = v + ℓ₁ • d ∧ T.pts k₂ = placeThird v d ℓ₁ ℓ₂ ℓ₃ := by
    intro ℓ₁ ℓ₂ ℓ₃ e1 e2 e3
    have hc'ℓ : c' = ℓ₁ := hℓ₁.symm.trans e1
    subst hc'ℓ
    refine ⟨hk₁, ?_⟩
    refine third_vertex v d (T.pts k₂) hunit c' ℓ₂ ℓ₃ hc' ?_ ?_ hk₂
    · rw [dist_comm, ← hk₀]; exact e2
    · rw [dist_comm, ← hk₁]; exact e3
  rcases sides_perm_of_congruent h hMa hMb hMc k₀ k₁ k₂ h01 h02 h12 with
    ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · exact Or.inl (key _ _ _ e1 e2 e3)
  · exact Or.inr (Or.inl (key _ _ _ e1 e2 e3))
  · exact Or.inr (Or.inr (Or.inl (key _ _ _ e1 e2 e3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key _ _ _ e1 e2 e3))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ _ _ e1 e2 e3)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key _ _ _ e1 e2 e3)))))

/-- **The two placements sharing a corner type are mirror images**: swapping which adjacent side
lies along `d` reflects the tile in the bisector of the corner at `v`.  Stated as the identity
that reflecting `placeThird v d ℓ₁ ℓ₂ ℓ₃` in the bisector gives `placeThird v d ℓ₂ ℓ₁ ℓ₃`'s
frame — recorded here only in the weak form that both have the same corner angle (`cos`), which is
what "mirror image" means for the *shape*; the coordinate identity is not needed downstream. -/
theorem mirror_pair_same_cos (ℓ₁ ℓ₂ ℓ₃ : ℝ) (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) :
    ((ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) / (2 * ℓ₁)) / ℓ₂ = ((ℓ₂ ^ 2 + ℓ₁ ^ 2 - ℓ₃ ^ 2) / (2 * ℓ₂)) / ℓ₁ := by
  field_simp
  ring

end Erdos634.SixPlacements
