import Mathlib.Tactic

/-!
# Base-β: the tile's unit directions in coordinates over `ℚ(√−D)`

Erdős #634, base-β family: sides `(ef, f²−e², f²)`, angles `α, β, γ = 2α+β` with `3α+2β = π`.
Write `D = 4f² − e²`.  Then `cos α = (2f²−e²)/(2f²)`, `sin α = e√D/(2f²)`, so

    ζ = e^{iα} = (2f²−e² + e√−D)/(2f²)

lies in `K = ℚ(√−D)`, and — this is the point — so does `ξ = e^{iβ}`, even though `β = (π−3α)/2`
is a *half* angle:

    ξ = e^{iβ} = (e(3f²−e²) + (f²−e²)√−D)/(2f³).

**Correction recorded.** The formula handed to this file by the preceding session,
`ξ = (3f²−e² + (f²−e²)√−D)/(2f³)`, is wrong unless `e = 1`: its norm is not `1`.  The factor `e`
on the real part is required, and with it the whole family works, not just `e = 1`
(`xiQ_norm_one` below is proved for all `e, f` with `f ≠ 0`).

This file is the arithmetic half: `K` is coordinatised as `ℚ × ℚ`, `(x,y) ↦ x + y√−D`, with the
multiplication `qmul`.  `BaseBetaQuadField.lean` embeds it in `ℂ` and draws the geometric
consequence.  No `sorry`; no geometry is assumed here.
-/

namespace Erdos634.BaseBetaQuad

/-- `D = 4f² − e²`, the discriminant of the base-β family. -/
def Dq (e f : ℚ) : ℚ := 4 * f ^ 2 - e ^ 2

/-- Multiplication of `x + y√−D` in coordinates. -/
def qmul (e f : ℚ) (z w : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 * w.1 - Dq e f * (z.2 * w.2), z.1 * w.2 + z.2 * w.1)

/-- Conjugation `x + y√−D ↦ x − y√−D`. -/
def qconj (z : ℚ × ℚ) : ℚ × ℚ := (z.1, -z.2)

/-- `ζ = e^{iα}` in coordinates. -/
def zetaQ (e f : ℚ) : ℚ × ℚ := ((2 * f ^ 2 - e ^ 2) / (2 * f ^ 2), e / (2 * f ^ 2))

/-- `ξ = e^{iβ}` in coordinates — note the factor `e` on the real part. -/
def xiQ (e f : ℚ) : ℚ × ℚ := (e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3), (f ^ 2 - e ^ 2) / (2 * f ^ 3))

theorem qmul_comm (e f : ℚ) (z w : ℚ × ℚ) : qmul e f z w = qmul e f w z := by
  simp only [qmul, Prod.mk.injEq]; constructor <;> ring

theorem qmul_assoc (e f : ℚ) (z w v : ℚ × ℚ) :
    qmul e f (qmul e f z w) v = qmul e f z (qmul e f w v) := by
  simp only [qmul, Prod.mk.injEq]; constructor <;> ring

theorem qmul_one (e f : ℚ) (z : ℚ × ℚ) : qmul e f z (1, 0) = z := by
  simp [qmul]

/-- **`ζ` has norm one**, i.e. `ζ · ζ̄ = 1`: the identity `(2f²−e²)² + e²(4f²−e²) = 4f⁴`. -/
theorem zetaQ_norm_one (e f : ℚ) (hf : f ≠ 0) :
    qmul e f (zetaQ e f) (qconj (zetaQ e f)) = (1, 0) := by
  simp only [qmul, qconj, zetaQ, Dq, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-- **`ξ` has norm one**: `e²(3f²−e²)² + (f²−e²)²(4f²−e²) = 4f⁶`.  This is the identity that puts
`e^{iβ}` inside `ℚ(√−D)` despite `β` being a half-angle, and it holds for every `(e,f)`. -/
theorem xiQ_norm_one (e f : ℚ) (hf : f ≠ 0) :
    qmul e f (xiQ e f) (qconj (xiQ e f)) = (1, 0) := by
  simp only [qmul, qconj, xiQ, Dq, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-- **The angle relation, algebraically**: `ξ² ζ³ = −1`, which is `2β + 3α = π` read on the unit
circle.  Proved as a rational-function identity in `(e,f)`, so it certifies that `zetaQ` and `xiQ`
really are `e^{iα}` and `e^{iβ}` for the base-β angles. -/
theorem xiQ_sq_zetaQ_cube (e f : ℚ) (hf : f ≠ 0) :
    qmul e f (qmul e f (xiQ e f) (xiQ e f))
      (qmul e f (zetaQ e f) (qmul e f (zetaQ e f) (zetaQ e f))) = (-1, 0) := by
  simp only [qmul, xiQ, zetaQ, Dq, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

end Erdos634.BaseBetaQuad
