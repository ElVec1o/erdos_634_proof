import Erdos634.Congruence
import Erdos634.TargetShape

/-!
# `TargetShape.target_shape`, for an actual `CongruentDissection`'s target

Erdős #634.  `TargetShape.target_shape` is stated for three free points `A B C`.  This file wires it
to `D.target.pts`, in the exact index convention `CornerAnglePermTarget.htarget_of_isosceles` uses:
apex at `a`, base corners at `a+1` and `a+2`.  The two base-corner hypotheses are supplied in that
file's own format (`cornerAngle (pts (a+1+1)) (pts (a+1)) (pts (a+1+2)) = β`, and similarly at
`a+2`) — the format every call site in this corpus already carries — converted to `target_shape`'s
`hB`/`hC` via `Fin 3` index arithmetic and the symmetry of `cornerAngle`.

The tile-side hypotheses (`hpq, hrq, hpr` — the model's own sides witnessing `ef, f²−e², f²`) and
the two nondegeneracy hypotheses (`hsin`, `hBC0`) are unchanged from `target_shape`; nothing in the
corpus derives them for a general `(e,f)` member (that is exactly the standing "no scale/composition
map on dissections" blocker), so they remain explicit hypotheses here too — this file adds no new
unproved content, it only relocates `target_shape`'s conclusion onto real dissection data.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TargetShapeDissection

open Erdos634.Geometry Erdos634.TargetShape

/-- **The target's shape theorem, for a real `CongruentDissection`.**  With apex at `a` and base
corners at `a+1`, `a+2` both presenting the tile's `β` (in `CornerAnglePermTarget`'s own hypothesis
format), and the model's sides `ef, f²−e², f²` witnessed at some triangle `p q r`, the target's real
side lengths are `k·f³, k·f³, k·e(3f²−e²)` for `k = dist (target.pts (a+1)) (target.pts a) / f³`. -/
theorem congruentDissection_target_shape {N : ℕ} (D : CongruentDissection N) (e f β : ℝ)
    (he : 0 < e) (hef : e < f) (a : Fin 3)
    (p q r : Plane)
    (hpq : dist p q = e * f) (hrq : dist r q = f ^ 2) (hpr : dist p r = f ^ 2 - e ^ 2)
    (hβ : cornerAngle p q r = β)
    (h₁ : cornerAngle (D.target.pts (a + 1 + 1)) (D.target.pts (a + 1)) (D.target.pts (a + 1 + 2)) = β)
    (h₂ : cornerAngle (D.target.pts (a + 2 + 1)) (D.target.pts (a + 2)) (D.target.pts (a + 2 + 2)) = β)
    (hsin : Real.sin (cornerAngle (D.target.pts (a + 1)) (D.target.pts a) (D.target.pts (a + 2))) ≠ 0)
    (hAB0 : 0 < dist (D.target.pts a) (D.target.pts (a + 1)))
    (hBC0 : dist (D.target.pts (a + 1)) (D.target.pts (a + 2)) ≠ 0) :
    ∃ k : ℝ, 0 < k ∧
      dist (D.target.pts a) (D.target.pts (a + 1)) = k * f ^ 3 ∧
      dist (D.target.pts a) (D.target.pts (a + 2)) = k * f ^ 3 ∧
      dist (D.target.pts (a + 1)) (D.target.pts (a + 2)) = k * e * (3 * f ^ 2 - e ^ 2) := by
  have hidx1 : a + 1 + 1 = a + 2 := by fin_cases a <;> decide
  have hidx2 : a + 1 + 2 = a := by fin_cases a <;> decide
  have hidx3 : a + 2 + 1 = a := by fin_cases a <;> decide
  have hidx4 : a + 2 + 2 = a + 1 := by fin_cases a <;> decide
  rw [hidx1, hidx2] at h₁
  rw [hidx3, hidx4] at h₂
  -- `h₁ : cornerAngle (pts (a+2)) (pts (a+1)) (pts a) = β`  (i.e. `∠ C B A = β`)
  -- `h₂ : cornerAngle (pts a) (pts (a+2)) (pts (a+1)) = β`  (i.e. `∠ A C B = β`)
  set A := D.target.pts a
  set B := D.target.pts (a + 1)
  set C := D.target.pts (a + 2)
  have hB : cornerAngle A B C = β := by
    rw [show cornerAngle A B C = cornerAngle C B A by
      simp only [cornerAngle]; exact EuclideanGeometry.angle_comm _ _ _]
    exact h₁
  exact target_shape A B C e f he hef β p q r hpq hrq hpr hβ hB h₂ hsin hAB0 hBC0

end Erdos634.TargetShapeDissection
