import Erdos634.Dissection

/-!
# Constructing a concrete scalene `Tri` from its three side lengths (SSS)

Erdős #634. `IsoTri.isoTri` handles the isosceles case (two equal sides); the tile model itself
(sides `a=ef`, `b=f²-e²`, `c=f²`) is generically scalene, so closing `SideWalk`'s remaining gap for
the tile side (not just the target side) needs the general SSS construction. Same placement idea —
base on the x-axis, third vertex located by the law-of-cosines `x`-coordinate — generalized to three
independent side lengths instead of two equal ones.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SssTri

open Erdos634.Geometry

/-- The `x`-coordinate of the third vertex, by the law of cosines: with `A=(0,0)`, `B=(r,0)`,
`C=(x,y)`, `dist A C = q` and `dist B C = p` force `x = (r²+q²-p²)/(2r)`. -/
noncomputable def xCoord (p q r : ℝ) : ℝ := (r ^ 2 + q ^ 2 - p ^ 2) / (2 * r)

/-- The placement: base `[0,0]→[r,0]`, third vertex at `(xCoord p q r, h)`. -/
noncomputable def sssPts (p q r h : ℝ) : Fin 3 → Plane
  | 0 => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0]
  | 1 => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![r, 0]
  | 2 => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![xCoord p q r, h]

theorem coord0 (p q r h : ℝ) :
    sssPts p q r h 0 0 = 0 ∧ sssPts p q r h 1 0 = r ∧ sssPts p q r h 2 0 = xCoord p q r := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sssPts, EuclideanSpace.equiv]

theorem coord1 (p q r h : ℝ) :
    sssPts p q r h 0 1 = 0 ∧ sssPts p q r h 1 1 = 0 ∧ sssPts p q r h 2 1 = h := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sssPts, EuclideanSpace.equiv]

theorem dist01 (p q r h : ℝ) (hr : 0 ≤ r) : dist (sssPts p q r h 0) (sssPts p q r h 1) = r := by
  show dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0])
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![r, 0]) = r
  rw [EuclideanSpace.dist_eq]
  simp [EuclideanSpace.equiv, Fin.sum_univ_two]
  rw [show r ^ 2 = r * r by ring, Real.sqrt_mul_self hr]

/-- **The third vertex is at distance `q` from the origin**, given `h² = q² - x²` with
`x = xCoord p q r`. -/
theorem dist02 (p q r h : ℝ) (hq : 0 ≤ q) (hh : h ^ 2 = q ^ 2 - (xCoord p q r) ^ 2) :
    dist (sssPts p q r h 0) (sssPts p q r h 2) = q := by
  have hsq : dist (sssPts p q r h 0) (sssPts p q r h 2) ^ 2 = (xCoord p q r) ^ 2 + h ^ 2 := by
    show dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0])
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![xCoord p q r, h]) ^ 2
        = (xCoord p q r) ^ 2 + h ^ 2
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
    simp [EuclideanSpace.equiv, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  rw [hh] at hsq
  have hnn : 0 ≤ dist (sssPts p q r h 0) (sssPts p q r h 2) := dist_nonneg
  nlinarith [sq_nonneg (dist (sssPts p q r h 0) (sssPts p q r h 2) - q),
    sq_nonneg (dist (sssPts p q r h 0) (sssPts p q r h 2) + q)]

/-- **The third vertex is at distance `p` from `(r,0)`.** The law-of-cosines choice of `x` makes
this hold given exactly the same `h` as `dist02` — the algebraic identity
`(x-r)² + h² = q² + r² - 2rx = p²` (using `2rx = r²+q²-p²` from `xCoord`'s definition, valid for
`r ≠ 0`), so no further hypothesis on `p` is needed beyond `r ≠ 0` and `hh`. -/
theorem dist12 (p q r h : ℝ) (hr : r ≠ 0) (hp : 0 ≤ p)
    (hh : h ^ 2 = q ^ 2 - (xCoord p q r) ^ 2) :
    dist (sssPts p q r h 1) (sssPts p q r h 2) = p := by
  have hsq : dist (sssPts p q r h 1) (sssPts p q r h 2) ^ 2
      = (xCoord p q r - r) ^ 2 + h ^ 2 := by
    show dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![r, 0])
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![xCoord p q r, h]) ^ 2
        = (xCoord p q r - r) ^ 2 + h ^ 2
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
    simp [EuclideanSpace.equiv, Fin.sum_univ_two, Real.dist_eq, sq_abs]
    ring
  have hxr : xCoord p q r * (2 * r) = r ^ 2 + q ^ 2 - p ^ 2 := by
    unfold xCoord; field_simp
  have halg : (xCoord p q r - r) ^ 2 + (q ^ 2 - (xCoord p q r) ^ 2) = p ^ 2 := by
    nlinarith [hxr]
  rw [hh] at hsq
  rw [halg] at hsq
  have hnn : 0 ≤ dist (sssPts p q r h 1) (sssPts p q r h 2) := dist_nonneg
  nlinarith [sq_nonneg (dist (sssPts p q r h 1) (sssPts p q r h 2) - p),
    sq_nonneg (dist (sssPts p q r h 1) (sssPts p q r h 2) + p)]

/-- **Not collinear**, given `r ≠ 0` and `h ≠ 0`: same argument as `IsoTri.not_collinear`. -/
theorem not_collinear (p q r h : ℝ) (hr : r ≠ 0) (hh : h ≠ 0) :
    ¬ Collinear ℝ ({sssPts p q r h 0, sssPts p q r h 1, sssPts p q r h 2} : Set Plane) := by
  intro hc
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨p0, v, hv⟩ := hc
  obtain ⟨r0, hr0⟩ := hv (sssPts p q r h 0) (by simp)
  obtain ⟨r1, hr1⟩ := hv (sssPts p q r h 1) (by simp)
  obtain ⟨r2, hr2⟩ := hv (sssPts p q r h 2) (by simp)
  have hx0 := congrArg (fun pt : Plane => pt 0) hr0
  have hx1 := congrArg (fun pt : Plane => pt 0) hr1
  have hy0 := congrArg (fun pt : Plane => pt 1) hr0
  have hy1 := congrArg (fun pt : Plane => pt 1) hr1
  have hy2 := congrArg (fun pt : Plane => pt 1) hr2
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx0 hx1 hy0 hy1 hy2
  obtain ⟨hc00, hc10, _⟩ := coord0 p q r h
  obtain ⟨hc01, hc11, hc21⟩ := coord1 p q r h
  rw [hc00] at hx0
  rw [hc10] at hx1
  rw [hc01] at hy0
  rw [hc11] at hy1
  rw [hc21] at hy2
  have hne : r0 ≠ r1 := by
    intro heq
    rw [heq] at hx0
    apply hr
    linarith
  have hvy0 : v 1 = 0 := by
    have hdiff : (r0 - r1) * v 1 = 0 := by linarith
    rcases mul_eq_zero.mp hdiff with h1 | h1
    · exact absurd (by linarith : r0 = r1) hne
    · exact h1
  rw [hvy0] at hy0 hy2
  apply hh
  linarith

/-- **The scalene `Tri`**, given `r ≠ 0`, `h ≠ 0`. -/
noncomputable def sssTri (p q r h : ℝ) (hr : r ≠ 0) (hh : h ≠ 0) : Tri where
  pts := sssPts p q r h
  indep := (affineIndependent_iff_not_collinear_of_ne
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)).mpr (not_collinear p q r h hr hh)

end Erdos634.SssTri
