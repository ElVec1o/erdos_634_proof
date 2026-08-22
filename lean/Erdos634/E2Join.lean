import Erdos634.SectorArea
import Erdos634.Wedge
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

/-! Draft: the join. Composes the two halves of E2's geometric layer, now that cross-imports work. -/

open MeasureTheory Set

namespace Erdos634.E2Join

/-- The two `sector` definitions agree (both are `polarCoord.symm '' ((0,1) ×ˢ (0,θ))`). -/
theorem sector_agree (θ : ℝ) : Wedge.sector θ = SectorArea.sector θ := rfl

/-- **E2j: a cone of opening `θ`, cut by the unit ball, has area `θ/2`** — stated on the
half-plane description that `TangentCone` produces. This is the `hsector` hypothesis of
`AngleSumAssembled`, discharged. -/
theorem volume_halfplane_wedge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    volume ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
          ∩ {p : ℝ × ℝ | 0 < p.2}
          ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2})
      = ENNReal.ofReal (θ / 2) := by
  rw [← Wedge.sector_eq_halfplanes h0 hπ, sector_agree]
  exact SectorArea.volume_sector (le_of_lt h0) hπ

/-! ## Transport to `EuclideanSpace ℝ (Fin 2)`

`AngleSumAssembled` works in `EuclideanSpace ℝ (Fin 2)`, the wedge lives in `ℝ × ℝ`. The two are
identified by a volume-preserving chain `EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ) → ℝ × ℝ`. -/

/-- The identification of the Euclidean plane with `ℝ × ℝ`. -/
def toPair (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  MeasurableEquiv.finTwoArrow (WithLp.ofLp p)

theorem measurePreserving_toPair : MeasurePreserving toPair :=
  (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

/-- The half-plane wedge, as a subset of the Euclidean plane. -/
def wedge (θ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  toPair ⁻¹' ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
            ∩ {p : ℝ × ℝ | 0 < p.2}
            ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2})

/-- **E2k: `hsector`, in the space `AngleSumAssembled` uses.** A cone of opening `θ` cut by the unit
ball of the Euclidean plane has area `θ/2`. -/
theorem volume_wedge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    volume (wedge θ) = ENNReal.ofReal (θ / 2) := by
  have hopen : IsOpen ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
      ∩ {p : ℝ × ℝ | 0 < p.2} ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2}) := by
    refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt continuous_const (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  rw [wedge, measurePreserving_toPair.measure_preimage hopen.measurableSet.nullMeasurableSet]
  exact volume_halfplane_wedge h0 hπ

end Erdos634.E2Join
