import Erdos634.AreaDet
import Erdos634.CertGeom

/-!
# From explicit coordinates to a `Tri`

Erdős #634. A certificate holds points as exact coordinate pairs. This file is the dictionary:
`mkPt` builds a point of the plane from two reals, `indep_of_det_ne_zero` says a nonzero
determinant makes three of them affinely independent — so `mkTri` builds the `Tri` — and
`dist_sq_mkPt`, `detTri_mkTri` compute the two quantities a certificate checks (squared side
lengths and twice the signed area) as polynomials in those coordinates.

With `CertGeom` and `SssCongruent`, this is everything `CertBridge.ofCert` needs stated in terms
of arithmetic on coordinates.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CertCoord

open Erdos634.Geometry

/-- A point of the plane from its two coordinates. -/
noncomputable def mkPt (x y : ℝ) : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

@[simp] theorem mkPt_zero (x y : ℝ) : mkPt x y 0 = x := by simp [mkPt, EuclideanSpace.equiv]
@[simp] theorem mkPt_one (x y : ℝ) : mkPt x y 1 = y := by simp [mkPt, EuclideanSpace.equiv]

/-- **Squared side length in coordinates.** -/
theorem dist_sq_mkPt (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mkPt x₁ y₁) (mkPt x₂ y₂) ^ 2 = (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  rw [EuclideanSpace.dist_eq]
  rw [Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- The determinant of three coordinate points: twice the signed area. -/
def det3 (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) : ℝ := (x₁ - x₀) * (y₂ - y₀) - (x₂ - x₀) * (y₁ - y₀)

/-- **A nonzero determinant makes three points non-collinear.** -/
theorem not_collinear_of_det {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ} (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    ¬ Collinear ℝ ({mkPt x₀ y₀, mkPt x₁ y₁, mkPt x₂ y₂} : Set Plane) := by
  intro hc
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨q, v, hv⟩ := hc
  obtain ⟨r₀, h₀⟩ := hv (mkPt x₀ y₀) (by simp)
  obtain ⟨r₁, h₁⟩ := hv (mkPt x₁ y₁) (by simp)
  obtain ⟨r₂, h₂⟩ := hv (mkPt x₂ y₂) (by simp)
  have hx : ∀ (a b : ℝ) (r : ℝ), mkPt a b = r • v +ᵥ q → a = r * v 0 + q 0 := by
    intro a b r h
    have := congrArg (fun pt : Plane => pt 0) h
    simpa [mkPt, EuclideanSpace.equiv] using this
  have hy : ∀ (a b : ℝ) (r : ℝ), mkPt a b = r • v +ᵥ q → b = r * v 1 + q 1 := by
    intro a b r h
    have := congrArg (fun pt : Plane => pt 1) h
    simpa [mkPt, EuclideanSpace.equiv] using this
  have e₀ := hx _ _ _ h₀; have f₀ := hy _ _ _ h₀
  have e₁ := hx _ _ _ h₁; have f₁ := hy _ _ _ h₁
  have e₂ := hx _ _ _ h₂; have f₂ := hy _ _ _ h₂
  apply hdet
  rw [det3, e₀, e₁, e₂, f₀, f₁, f₂]
  ring

/-- **The `Tri` a certificate's three coordinate pairs name.** -/
noncomputable def mkTri (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) : Tri where
  pts := ![mkPt x₀ y₀, mkPt x₁ y₁, mkPt x₂ y₂]
  indep := (affineIndependent_iff_not_collinear_of_ne
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)).mpr (not_collinear_of_det hdet)

@[simp] theorem mkTri_pts (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    (mkTri x₀ y₀ x₁ y₁ x₂ y₂ hdet).pts = ![mkPt x₀ y₀, mkPt x₁ y₁, mkPt x₂ y₂] := rfl

/-- **`detTri` of a coordinate triangle is the coordinate determinant.** -/
theorem detTri_mkTri (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    Erdos634.AreaDet.detTri (mkTri x₀ y₀ x₁ y₁ x₂ y₂ hdet) = det3 x₀ y₀ x₁ y₁ x₂ y₂ := by
  rw [Erdos634.AreaDet.detTri_eq, det3]
  show (mkPt x₁ y₁ - mkPt x₀ y₀) 0 * (mkPt x₂ y₂ - mkPt x₀ y₀) 1
      - (mkPt x₂ y₂ - mkPt x₀ y₀) 0 * (mkPt x₁ y₁ - mkPt x₀ y₀) 1 = _
  simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]

end Erdos634.CertCoord
