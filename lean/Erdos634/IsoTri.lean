import Erdos634.Dissection

/-!
# Constructing a concrete isosceles `Tri` from its side lengths

Erdős #634. Every remaining gap in `SideWalk.lean` (and several other `PROVED` rows across the
corpus) ultimately needs a genuine real-coordinate `Tri` — nothing in this project builds one from
numeric side lengths; confirmed by search. This file is the first step: an explicit isosceles
placement, base on the x-axis, apex above its midpoint.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.IsoTri

open Erdos634.Geometry

/-- The isosceles placement: base `[0,0]→[L,0]`, apex at `(L/2, h)`. -/
noncomputable def isoPts (L h : ℝ) : Fin 3 → Plane
  | 0 => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0]
  | 1 => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![L, 0]
  | 2 => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![L / 2, h]

theorem dist01 (L h : ℝ) (hL : 0 ≤ L) : dist (isoPts L h 0) (isoPts L h 1) = L := by
  show dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0])
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![L, 0]) = L
  rw [EuclideanSpace.dist_eq]
  simp [EuclideanSpace.equiv, Fin.sum_univ_two]
  rw [show L ^ 2 = L * L by ring, Real.sqrt_mul_self hL]

theorem dist02sq (L h : ℝ) :
    dist (isoPts L h 0) (isoPts L h 2) ^ 2 = (L / 2) ^ 2 + h ^ 2 := by
  show dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0])
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![L / 2, h]) ^ 2 = (L / 2) ^ 2 + h ^ 2
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [EuclideanSpace.equiv, Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem dist12sq (L h : ℝ) :
    dist (isoPts L h 1) (isoPts L h 2) ^ 2 = (L / 2) ^ 2 + h ^ 2 := by
  show dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![L, 0])
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![L / 2, h]) ^ 2 = (L / 2) ^ 2 + h ^ 2
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [EuclideanSpace.equiv, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  ring

/-- **Both equal sides have length `s`**, given `h² = s² - (L/2)²` (the height from the law of
Pythagoras on the isosceles bisected triangle). -/
theorem dist02 (L h s : ℝ) (hs : 0 ≤ s) (hh : h ^ 2 = s ^ 2 - (L / 2) ^ 2) :
    dist (isoPts L h 0) (isoPts L h 2) = s := by
  have hsq := dist02sq L h
  rw [hh] at hsq
  have hnn : 0 ≤ dist (isoPts L h 0) (isoPts L h 2) := dist_nonneg
  nlinarith [sq_nonneg (dist (isoPts L h 0) (isoPts L h 2) - s),
    sq_nonneg (dist (isoPts L h 0) (isoPts L h 2) + s)]

theorem dist12 (L h s : ℝ) (hs : 0 ≤ s) (hh : h ^ 2 = s ^ 2 - (L / 2) ^ 2) :
    dist (isoPts L h 1) (isoPts L h 2) = s := by
  have hsq := dist12sq L h
  rw [hh] at hsq
  have hnn : 0 ≤ dist (isoPts L h 1) (isoPts L h 2) := dist_nonneg
  nlinarith [sq_nonneg (dist (isoPts L h 1) (isoPts L h 2) - s),
    sq_nonneg (dist (isoPts L h 1) (isoPts L h 2) + s)]

/-- **Coordinate `0` (the `x`-coordinate).** -/
theorem coord0 (L h : ℝ) : isoPts L h 0 0 = 0 ∧ isoPts L h 1 0 = L ∧ isoPts L h 2 0 = L / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [isoPts, EuclideanSpace.equiv]

/-- **Coordinate `1` (the `y`-coordinate).** -/
theorem coord1 (L h : ℝ) : isoPts L h 0 1 = 0 ∧ isoPts L h 1 1 = 0 ∧ isoPts L h 2 1 = h := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [isoPts, EuclideanSpace.equiv]

/-- **Not collinear**, given `L ≠ 0` and `h ≠ 0`: points `0`,`1` share `y = 0`, forcing the
collinearity direction vector `v` to have `v.y = 0` (since `x`-coordinates differ, `v.x ≠ 0` and the
two `r`'s differ), which then forces point `2`'s `y`-coordinate `h` to be `0` too. -/
theorem not_collinear (L h : ℝ) (hL : L ≠ 0) (hh : h ≠ 0) :
    ¬ Collinear ℝ ({isoPts L h 0, isoPts L h 1, isoPts L h 2} : Set Plane) := by
  intro hc
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨p0, v, hv⟩ := hc
  obtain ⟨r0, hr0⟩ := hv (isoPts L h 0) (by simp)
  obtain ⟨r1, hr1⟩ := hv (isoPts L h 1) (by simp)
  obtain ⟨r2, hr2⟩ := hv (isoPts L h 2) (by simp)
  have hx0 := congrArg (fun p : Plane => p 0) hr0
  have hx1 := congrArg (fun p : Plane => p 0) hr1
  have hy0 := congrArg (fun p : Plane => p 1) hr0
  have hy1 := congrArg (fun p : Plane => p 1) hr1
  have hy2 := congrArg (fun p : Plane => p 1) hr2
  simp only at hx0 hx1 hy0 hy1 hy2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, vadd_eq_add] at hx0 hx1 hy0 hy1 hy2
  obtain ⟨hc00, hc10, _⟩ := coord0 L h
  obtain ⟨hc01, hc11, hc21⟩ := coord1 L h
  rw [hc00] at hx0
  rw [hc10] at hx1
  rw [hc01] at hy0
  rw [hc11] at hy1
  rw [hc21] at hy2
  have hne : r0 ≠ r1 := by
    intro heq
    rw [heq] at hx0
    apply hL
    linarith
  have hvy0 : v 1 = 0 := by
    have hdiff : (r0 - r1) * v 1 = 0 := by linarith
    rcases mul_eq_zero.mp hdiff with h1 | h1
    · exact absurd (by linarith : r0 = r1) hne
    · exact h1
  rw [hvy0] at hy0 hy2
  apply hh
  linarith

/-- **The isosceles `Tri`**, given `L ≠ 0`, `h ≠ 0`. -/
noncomputable def isoTri (L h : ℝ) (hL : L ≠ 0) (hh : h ≠ 0) : Tri where
  pts := isoPts L h
  indep := (affineIndependent_iff_not_collinear_of_ne
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)).mpr (not_collinear L h hL hh)

end Erdos634.IsoTri
