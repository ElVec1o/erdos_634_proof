import Erdos634.AngleThreshold
import Mathlib.Geometry.Euclidean.Triangle

/-!
# The scale map: a triangle with the tile's angles has sides `s·f`, `s·(f²-1)`, `s·f²`

Erdős #634, `e = 1` family.  This is the missing link flagged in the end-to-end check: nothing in
the corpus connected a real `CongruentDissection`'s model — whose side lengths are just some real
numbers `dist (model.pts i) (model.pts j)` — to the concrete integers `f, f²−1, f²` that
`MidTriangleE1.base_single_b` and its relatives are stated for.  `RouteOneVE.lean` papered over this
with a named hypothesis (`hmodel : {...} = {f, f²-1, f²}`); this file discharges that hypothesis
from the angle data alone, via the law of sines.

**The route.**  `AngleThreshold` gives closed forms for `cos α, cos β, cos γ` at `e = 1`, as
functions of `f`.  Squaring and using `sin² = 1 − cos²`:

    sin²α = (4f²−1)/(4f⁴),   sin²β = (f²−1)²(4f²−1)/(4f⁶),   sin²γ = (4f²−1)/(4f²)

(checked symbolically, `ring`-provable after `field_simp` once the cosines are known), so
**`sin α / f = sin β / (f²−1) = sin γ / f²`** exactly.  Mathlib's law of sines
(`EuclideanGeometry.law_sin`) says a side divided by the sine of its *opposite* angle is the same
constant for all three sides of any triangle.  Composing: a triangle whose three corner angles equal
`α, β, γ` (in the tile's own vertex convention) has side lengths exactly `s·f`, `s·(f²−1)`, `s·f²`
for one common `s > 0`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ScaleMap

open EuclideanGeometry Erdos634.Geometry Erdos634.AngleThreshold

/-! ## The sine-squared closed forms -/

theorem sin_sq_alpha {f : ℝ} {θ : ℝ} (hcos : Real.cos θ = (2 * f ^ 2 - 1) / (2 * f ^ 2))
    (hf0 : f ≠ 0) : Real.sin θ ^ 2 = (4 * f ^ 2 - 1) / (4 * f ^ 4) := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [hcos] at h
  field_simp at h ⊢
  nlinarith [h]

theorem sin_sq_beta {f : ℝ} {θ : ℝ} (hcos : Real.cos θ = (3 * f ^ 2 - 1) / (2 * f ^ 3))
    (hf0 : f ≠ 0) : Real.sin θ ^ 2 = (f ^ 2 - 1) ^ 2 * (4 * f ^ 2 - 1) / (4 * f ^ 6) := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [hcos] at h
  field_simp at h ⊢
  nlinarith [h]

theorem sin_sq_gamma {f : ℝ} {θ : ℝ} (hcos : Real.cos θ = -1 / (2 * f)) (hf0 : f ≠ 0) :
    Real.sin θ ^ 2 = (4 * f ^ 2 - 1) / (4 * f ^ 2) := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [hcos] at h
  field_simp at h ⊢
  nlinarith [h]

/-! ## Angle positivity, from the cosine being strictly between `-1` and `1` -/

/-- **`α` is strictly between `0` and `π`.**  `cos α = (2f²-1)/(2f²) ∈ (0,1)` for `f > 1`, and
Mathlib gives that `EuclideanGeometry.angle` always lies in `[0, π]`; being neither `0` nor `π`
(where `cos` would be `±1`) pins it strictly inside. -/
theorem angle_mem_Ioo_of_cos {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    {c : ℝ} (hcos : Real.cos θ = c) (hc1 : c ≠ 1) (hc2 : c ≠ -1) : 0 < θ ∧ θ < Real.pi := by
  constructor
  · rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, Real.cos_zero] at hcos; exact hc1 hcos.symm
  · rcases hπ.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, Real.cos_pi] at hcos; exact hc2 hcos.symm

theorem sin_pos_alpha {f α : ℝ} (hf : 1 < f) (h0 : 0 ≤ α) (hπ : α ≤ Real.pi)
    (hcosα : Real.cos α = (2 * f ^ 2 - 1) / (2 * f ^ 2)) : 0 < Real.sin α := by
  have hf0 : (0:ℝ) < f := lt_trans zero_lt_one hf
  have hc1 : (2 * f ^ 2 - 1) / (2 * f ^ 2) ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq (by positivity)] at h; nlinarith
  have hc2 : (2 * f ^ 2 - 1) / (2 * f ^ 2) ≠ -1 := by
    intro h; rw [div_eq_iff (by positivity : (2:ℝ) * f ^ 2 ≠ 0)] at h; nlinarith
  obtain ⟨ha0, haπ⟩ := angle_mem_Ioo_of_cos h0 hπ hcosα hc1 hc2
  exact Real.sin_pos_of_pos_of_lt_pi ha0 haπ

/-! ## The three sine ratios -/

/-- **`sin α · (f²−1) = sin β · f`**. -/
theorem sin_alpha_mul_eq {f α β : ℝ} (hf : 1 < f)
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (hcosα : Real.cos α = (2 * f ^ 2 - 1) / (2 * f ^ 2))
    (hcosβ : Real.cos β = (3 * f ^ 2 - 1) / (2 * f ^ 3)) :
    Real.sin α * (f ^ 2 - 1) = Real.sin β * f := by
  have hf0 : (0:ℝ) < f := lt_trans zero_lt_one hf
  have hsα : 0 ≤ Real.sin α := (sin_pos_alpha hf hα0 hαπ hcosα).le
  have hsβ : 0 ≤ Real.sin β := Real.sin_nonneg_of_mem_Icc ⟨hβ0, hβπ⟩
  have h1 := sin_sq_alpha hcosα hf0.ne'
  have h2 := sin_sq_beta hcosβ hf0.ne'
  have hb0 : (0:ℝ) ≤ f ^ 2 - 1 := by nlinarith
  have hsq : (Real.sin α * (f ^ 2 - 1)) ^ 2 = (Real.sin β * f) ^ 2 := by
    have heq : Real.sin α ^ 2 * (f ^ 2 - 1) ^ 2 = Real.sin β ^ 2 * f ^ 2 := by
      rw [h1, h2]; field_simp
    nlinarith [heq]
  nlinarith [sq_nonneg (Real.sin α * (f ^ 2 - 1) - Real.sin β * f),
    mul_nonneg hsα hb0, mul_nonneg hsβ hf0.le, hsq]

/-- **`sin α · f² = sin γ · f`**. -/
theorem sin_alpha_mul_eq' {f α γ : ℝ} (hf : 1 < f)
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) (hγ0 : 0 ≤ γ) (hγπ : γ ≤ Real.pi)
    (hcosα : Real.cos α = (2 * f ^ 2 - 1) / (2 * f ^ 2))
    (hcosγ : Real.cos γ = -1 / (2 * f)) :
    Real.sin α * f ^ 2 = Real.sin γ * f := by
  have hf0 : (0:ℝ) < f := lt_trans zero_lt_one hf
  have hsα : 0 ≤ Real.sin α := (sin_pos_alpha hf hα0 hαπ hcosα).le
  have hsγ : 0 ≤ Real.sin γ := Real.sin_nonneg_of_mem_Icc ⟨hγ0, hγπ⟩
  have h1 := sin_sq_alpha hcosα hf0.ne'
  have h3 := sin_sq_gamma hcosγ hf0.ne'
  have hsq : (Real.sin α * f ^ 2) ^ 2 = (Real.sin γ * f) ^ 2 := by
    have heq : Real.sin α ^ 2 * (f ^ 2) ^ 2 = Real.sin γ ^ 2 * f ^ 2 := by
      rw [h1, h3]; field_simp
    nlinarith [heq]
  nlinarith [sq_nonneg (Real.sin α * f ^ 2 - Real.sin γ * f),
    mul_nonneg hsα (sq_nonneg f), mul_nonneg hsγ hf0.le, hsq]

/-! ## The scale map itself -/

/-- **The scale map.**  A triangle with corner angles `α` at `p₀` (opposite `p₁p₂`), `β` at `p₁`
(opposite `p₂p₀`), `γ` at `p₂` (opposite `p₀p₁`), matching the `e=1` family's closed cosine forms,
has side lengths `s·f`, `s·(f²−1)`, `s·f²` for a single `s > 0`. -/
theorem scale_map {f α β γ : ℝ} (hf : 1 < f)
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (hγ0 : 0 ≤ γ) (hγπ : γ ≤ Real.pi)
    (hcosα : Real.cos α = (2 * f ^ 2 - 1) / (2 * f ^ 2))
    (hcosβ : Real.cos β = (3 * f ^ 2 - 1) / (2 * f ^ 3))
    (hcosγ : Real.cos γ = -1 / (2 * f))
    (p₀ p₁ p₂ : Plane) (hne : p₁ ≠ p₂)
    (hA : cornerAngle p₁ p₀ p₂ = α) (hB : cornerAngle p₂ p₁ p₀ = β) (hC : cornerAngle p₀ p₂ p₁ = γ) :
    ∃ s : ℝ, 0 < s ∧
      dist p₁ p₂ = s * f ∧ dist p₂ p₀ = s * (f ^ 2 - 1) ∧ dist p₀ p₁ = s * f ^ 2 := by
  have hf0 : (0:ℝ) < f := lt_trans zero_lt_one hf
  have hsα := sin_pos_alpha hf hα0 hαπ hcosα
  set s := dist p₁ p₂ / f with hs
  have hd0 : (0:ℝ) < dist p₁ p₂ := dist_pos.mpr hne
  have hs0 : 0 < s := div_pos hd0 hf0
  refine ⟨s, hs0, ?_, ?_, ?_⟩
  · rw [hs]; field_simp
  · -- law of sines at `p₀`: `sin(∠p₁ p₀ p₂) * dist p₀ p₂ = sin(∠p₂ p₁ p₀) * dist p₂ p₁`
    have hlaw : Real.sin (cornerAngle p₁ p₀ p₂) * dist p₀ p₂
        = Real.sin (cornerAngle p₂ p₁ p₀) * dist p₂ p₁ := by
      simpa [cornerAngle] using EuclideanGeometry.law_sin p₁ p₀ p₂
    rw [hA, hB, dist_comm p₀ p₂, dist_comm p₂ p₁] at hlaw
    -- `hlaw : sin α * dist p₂ p₀ = sin β * dist p₁ p₂`
    have key := sin_alpha_mul_eq hf hα0 hαπ hβ0 hβπ hcosα hcosβ
    have hsβ_eq : Real.sin β = Real.sin α * (f ^ 2 - 1) / f := by
      rw [eq_div_iff hf0.ne']; linear_combination -key
    rw [hsβ_eq] at hlaw
    have hd12 : dist p₁ p₂ = s * f := by rw [hs]; field_simp
    rw [hd12] at hlaw
    have hfin : Real.sin α * dist p₂ p₀ = Real.sin α * (s * (f ^ 2 - 1)) := by
      rw [hlaw]; field_simp [hf0.ne']
    exact mul_left_cancel₀ hsα.ne' hfin
  · -- law of sines at `p₂`: angle `p₂ p₀ p₁ = α` (comm of `p₁ p₀ p₂`), `p₁ p₂ p₀ = γ` (comm of
    -- `p₀ p₂ p₁`)
    have hlaw : Real.sin (cornerAngle p₂ p₀ p₁) * dist p₀ p₁
        = Real.sin (cornerAngle p₁ p₂ p₀) * dist p₁ p₂ := by
      simpa [cornerAngle] using EuclideanGeometry.law_sin p₂ p₀ p₁
    have hcomm1 : cornerAngle p₂ p₀ p₁ = cornerAngle p₁ p₀ p₂ := by
      simp only [cornerAngle]; exact EuclideanGeometry.angle_comm _ _ _
    have hcomm2 : cornerAngle p₁ p₂ p₀ = cornerAngle p₀ p₂ p₁ := by
      simp only [cornerAngle]; exact EuclideanGeometry.angle_comm _ _ _
    rw [hcomm1, hcomm2, hA, hC] at hlaw
    -- `hlaw : sin α * dist p₀ p₁ = sin γ * dist p₁ p₂`
    have key' := sin_alpha_mul_eq' hf hα0 hαπ hγ0 hγπ hcosα hcosγ
    have hsγ_eq : Real.sin γ = Real.sin α * f := by
      have : Real.sin γ * f = Real.sin α * f * f := by rw [← key']; ring
      exact mul_right_cancel₀ hf0.ne' this
    rw [hsγ_eq] at hlaw
    have hd12 : dist p₁ p₂ = s * f := by rw [hs]; field_simp
    rw [hd12] at hlaw
    have hfin : Real.sin α * dist p₀ p₁ = Real.sin α * (s * f ^ 2) := by
      rw [hlaw]; field_simp [hf0.ne']
    exact mul_left_cancel₀ hsα.ne' hfin

end Erdos634.ScaleMap
