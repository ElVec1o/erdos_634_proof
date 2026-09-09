import Erdos634.TilePlacement

/-!
# The law of sines in `sideOpp`/`angleAt` form — `prop:unify` clause (iii), member-independent

Erdős #634, obstructions note `prop:unify` (`paper/erdos-634-obstructions.tex:974`), clause (iii):

> `b sin γ = c sin β`, so an `a`-up tile spans its strip, at every member.

The corpus already used Mathlib's `EuclideanGeometry.law_sin` twice (`ScaleMap.scale_map`,
`TargetShape`), but both times at **`e = 1`**, through the closed cosine forms
`cos α = (2f²−1)/(2f²)`, `cos β = (3f²−1)/(2f³)`, `cos γ = −1/(2f)`.  Clause (iii) of `prop:unify`
is precisely the assertion that this ingredient does **not** depend on the member, and no
member-independent form of it existed.

It does not, and this file says so at the only level where "member-independent" has content: for an
*arbitrary* `Tri`, with no cosine hypotheses, no `(e,f)`, and no member at all.  The identity is the
sine rule, and Mathlib supplies it; the work is only the `Fin 3` index bookkeeping that puts it in
this project's `sideOpp`/`angleAt` notation.

**Scope, honestly.** This closes the *identity* half of clause (iii).  The clause's consequent —
"so an `a`-up tile spans its strip" — is a placement statement about a row structure that has no
Lean definition, and is untouched here.  `prop:unify`'s label does not move.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TriLawSin

open Erdos634.Geometry Erdos634.TilePlacement

/-- **The law of sines for a tile**, in `sideOpp`/`angleAt` notation and general in the vertex
index: the side opposite a vertex is proportional to the sine of the angle at that vertex.
No hypotheses — true of every `Tri`, at every member of every family. -/
theorem sin_angleAt_mul_sideOpp (T : Tri) (j : Fin 3) :
    Real.sin (angleAt T (j + 1)) * sideOpp T j
      = Real.sin (angleAt T j) * sideOpp T (j + 1) := by
  fin_cases j
  · simpa [angleAt, sideOpp, cornerAngle, EuclideanGeometry.angle_comm] using
      EuclideanGeometry.law_sin (T.pts 0) (T.pts 1) (T.pts 2)
  · simpa [angleAt, sideOpp, cornerAngle, EuclideanGeometry.angle_comm] using
      EuclideanGeometry.law_sin (T.pts 1) (T.pts 2) (T.pts 0)
  · simpa [angleAt, sideOpp, cornerAngle, EuclideanGeometry.angle_comm] using
      EuclideanGeometry.law_sin (T.pts 2) (T.pts 0) (T.pts 1)

/-- **`prop:unify` clause (iii)'s identity: `b sin γ = c sin β`.**  With the base-`β` labelling
(`a` opposite the `α`-vertex `0`, `b` opposite the `β`-vertex `1`, `c` opposite the `γ`-vertex `2`)
this is `sin_angleAt_mul_sideOpp` at `j = 1`.  It holds at every member because it holds of every
triangle: the `e = 1` derivations in `ScaleMap` used the closed cosine forms, and none of that is
needed. -/
theorem b_sin_gamma_eq_c_sin_beta (T : Tri) :
    sideOpp T 1 * Real.sin (angleAt T 2) = sideOpp T 2 * Real.sin (angleAt T 1) := by
  have h := sin_angleAt_mul_sideOpp T 1
  have h1 : (1 : Fin 3) + 1 = 2 := rfl
  rw [h1] at h
  linarith [h]

end Erdos634.TriLawSin
