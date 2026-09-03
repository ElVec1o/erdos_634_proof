import Erdos634.Congruence
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# Congruent triangles match corner angles under a single permutation

Erdős #634. `Congruence.Tri.Congruent.dist_eq` exposes the vertex correspondence of a congruence as
a permutation matching every *distance*; `CongruentAngles.congruent_corner_angles` matches corner
angles but only one vertex at a time, existentially. The double count behind `lem:census` needs the
uniform form: **one** permutation matching all three corner angles at once.

The route is the isometry itself rather than the distances. A `Tri.Congruent` carries an
`IsometryEquiv` of the plane; Mazur–Ulam (`IsometryEquiv.toRealAffineIsometryEquiv`) makes it affine,
and `AffineIsometry.angle_map` then transports corner angles directly. The only combinatorial step
left is that `σ` sends the two vertices *other than* `k` to the two other than `σ k`, in one order or
the other — a `Fin 3` fact, settled by `decide`, with `EuclideanGeometry.angle_comm` absorbing the
swap.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry

namespace Erdos634.Geometry

/-- **Congruent triangles match corner angles under one permutation.** -/
theorem Tri.Congruent.cornerAngle_perm {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3,
      cornerAngle (U.pts (σ k + 1)) (U.pts (σ k)) (U.pts (σ k + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨σ, fun k => ?_⟩
  -- the isometry transports the corner angle at `k` to the one at `σ k`
  have hmap : cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2)))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
    rw [← hf (k + 1), ← hf k, ← hf (k + 2)]
    rw [Erdos634.Geometry.cornerAngle, Erdos634.Geometry.cornerAngle]
    rw [show (f : Plane → Plane) = f.toRealAffineIsometryEquiv from
      (IsometryEquiv.coeFn_toRealAffineIsometryEquiv f).symm]
    exact f.toRealAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _
  -- `σ` sends `{k+1, k+2}` onto `{σ k + 1, σ k + 2}`, in one order or the other
  have hidx : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
      (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by decide
  have hne : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  obtain ⟨h1, h2, h12⟩ := hne k
  rcases hidx (σ k) (σ (k + 1)) (σ (k + 2))
      (fun he => h1 (σ.injective he)) (fun he => h2 (σ.injective he))
      (fun he => h12 (σ.injective he)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← ha, ← hb]; exact hmap
  · rw [← ha, ← hb]
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]
    exact hmap

end Erdos634.Geometry
