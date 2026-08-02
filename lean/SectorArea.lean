import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# (B): the area of a unit circular sector (Erdős #634, E2 step)

`AngleSumScope.lean` reduces the interior case of `HasAngleSums` to two elementary statements, of
which this is the second: the sector of the unit disk subtending angle `θ` has area `θ/2`.

Route: polar coordinates. Mathlib's `lintegral_comp_polarCoord_symm` supplies the Jacobian `r`, so
the sector, which is `(0,1) × (0,θ)` in polar coordinates, has area `∫₀^θ ∫₀¹ r dr dφ = θ/2`.
-/

open MeasureTheory Set

namespace Erdos634.SectorArea

/-- The polar rectangle `(0,1) × (0,θ)`. -/
def polarBox (θ : ℝ) : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) θ

/-- The open sector of the unit disk of angle `θ`: the image of `polarBox θ` under
`polarCoord.symm`. -/
def sector (θ : ℝ) : Set (ℝ × ℝ) := polarCoord.symm '' polarBox θ

/-- For `θ < π` the polar box lies in `polarCoord.target = (0,∞) ×ˢ (-π,π)`. -/
theorem polarBox_subset_target {θ : ℝ} (hθ' : θ < Real.pi) :
    polarBox θ ⊆ polarCoord.target := by
  rintro ⟨r, φ⟩ ⟨⟨hr0, hr1⟩, hφ0, hφθ⟩
  exact ⟨hr0, by linarith [Real.pi_pos], by linarith⟩

/-- `∫⁻ r in (0,1), ofReal r = ofReal (1/2)`. -/
theorem lintegral_id_Ioo : ∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal r = ENNReal.ofReal (1/2) := by
  have hmeas : MeasurableSet (Ioo (0:ℝ) 1) := measurableSet_Ioo
  have hint : IntegrableOn (fun r : ℝ => r) (Ioo (0:ℝ) 1) :=
    (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0:ℝ) 1)] fun r : ℝ => r := by
    filter_upwards [ae_restrict_mem hmeas] with r hr using le_of_lt hr.1
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_id]
  norm_num

/-- **The Jacobian integral.** `∫⁻ (r,φ) in (0,1)×(0,θ), r = θ/2` for `θ ≥ 0`. -/
theorem lintegral_jacobian {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫⁻ p in polarBox θ, ENNReal.ofReal p.1 = ENNReal.ofReal (θ / 2) := by
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (polarBox θ)
      = ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) θ))) := by
    rw [Measure.prod_restrict, polarBox, ← Measure.volume_eq_prod]
  rw [hprod, MeasureTheory.lintegral_prod _ (by fun_prop)]
  have hinner : ∀ r : ℝ, ∫⁻ _ in Ioo (0:ℝ) θ, ENNReal.ofReal r
      = ENNReal.ofReal r * ENNReal.ofReal θ := by
    intro r
    rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]
    congr 1
    rw [ENNReal.ofReal_eq_ofReal_iff (by linarith) hθ]
    ring
  simp_rw [hinner]
  rw [MeasureTheory.lintegral_mul_const _ (by fun_prop), lintegral_id_Ioo,
      ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring


/-! ## The geometric form

`lintegral_jacobian` is the computation. What the angle-sum assembly consumes is a statement about a
subset of the plane, and that is obtained by pushing the integral through `polarCoord` against an
indicator. The sector is open (the image of an open box under a partial homeomorphism, inside the
target), so measurability is free. -/

/-- **The unit sector of angle `θ` has area `θ/2`.** -/
theorem volume_sector {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < Real.pi) :
    volume (sector θ) = ENNReal.ofReal (θ / 2) := by
  have hsub := polarBox_subset_target hθ'
  have hboxOpen : IsOpen (polarBox θ) := isOpen_Ioo.prod isOpen_Ioo
  have hbox : MeasurableSet (polarBox θ) := hboxOpen.measurableSet
  have hsec : MeasurableSet (sector θ) :=
    (OpenPartialHomeomorph.isOpen_image_symm_of_subset_target polarCoord hboxOpen hsub).measurableSet
  have key := lintegral_comp_polarCoord_symm ((sector θ).indicator (fun _ => (1 : ENNReal)))
  rw [lintegral_indicator hsec, setLIntegral_one] at key
  have hpt : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (sector θ).indicator (fun _ => (1 : ENNReal)) (polarCoord.symm p)
        = (polarBox θ).indicator (fun q => ENNReal.ofReal q.1) p := by
    intro p hp
    by_cases hpb : p ∈ polarBox θ
    · have hmem : polarCoord.symm p ∈ sector θ := mem_image_of_mem _ hpb
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpb, smul_eq_mul, mul_one]
    · have hnot : polarCoord.symm p ∉ sector θ := by
        rintro ⟨q, hq, hqp⟩
        exact hpb (polarCoord.symm.injOn (hsub hq) hp hqp ▸ hq)
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hpb, smul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt,
    setLIntegral_indicator hbox, Set.inter_eq_self_of_subset_left hsub,
    lintegral_jacobian hθ] at key
  exact key.symm

end Erdos634.SectorArea
