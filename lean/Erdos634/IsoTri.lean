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

end Erdos634.IsoTri
