import Mathlib.Tactic
import Erdos634.AngleSumDissection
import Erdos634.PinLemma

/-!
# The pin plumbing: the angle equation at a base junction, from the dissection layer

Erdős #634.  `PinLemma` proved the pin's forced multisets from an angle-sum *hypothesis*.  This
file discharges that hypothesis against the real machinery: for any dissection and any point of
the target's boundary that is not a target vertex — in particular any base junction interior to
the base edge — the tiles' local angles sum to exactly `π`.  This is `sum_localAngle_eq` (the
discharged `G2`) composed with `localAngle_frontier`, and nothing else.

With it, the pin argument's non-arithmetic residue shrinks to: identifying each tile's local angle
at the pin (a vertex of a tile congruent to the base tile contributes one of `α, β, γ`; a tile
with the pin interior to an edge contributes `π`; all others `0` — the definition's four cases),
and the covering data along the flanking rays (`wall_partition`).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PinPlumbing

open Erdos634.Geometry

/-- **The pin equation.**  At any boundary point of the target that is not a target vertex, the
tiles' local angles sum to exactly `π`.  A base junction is such a point. -/
theorem pin_angle_sum {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts) :
    ∑ i, (D.tile i).localAngle p = Real.pi := by
  rw [D.sum_localAngle_eq p, D.target.localAngle_frontier hp hv]

/-- **The local-angle case split**, read off the definition: at any point, a tile's local angle is
a corner angle at one of its vertices, or `2π` (interior), or `π` (edge-interior), or `0`. -/
theorem localAngle_cases (T : Tri) (p : Plane) :
    (∃ j : Fin 3, p = T.pts j ∧
        T.localAngle p = cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) ∨
    T.localAngle p = 2 * Real.pi ∨ T.localAngle p = Real.pi ∨ T.localAngle p = 0 := by
  classical
  by_cases h : ∃ j, p = T.pts j
  · left
    exact ⟨h.choose, h.choose_spec, by rw [Tri.localAngle, dif_pos h]⟩
  · by_cases h2 : ∀ j, 0 < T.basis.coord j p
    · right; left
      rw [Tri.localAngle, dif_neg h, if_pos h2]
    · by_cases h3 : ∃ k, T.basis.coord k p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j p
      · right; right; left
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_pos h3]
      · right; right; right
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_neg h3]

/-- **No tile is interior-covering at a boundary point**: a tile whose local angle at the pin is
`2π` would make the sum exceed `π` on its own.  Stated at the sum level: if some tile contributes
`2π` and the others are nonnegative, the pin equation fails. -/
theorem no_interior_tile_at_pin {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (i : Fin N) (hi : (D.tile i).localAngle p = 2 * Real.pi) : False := by
  have hsum := pin_angle_sum D hp hv
  have hle : (D.tile i).localAngle p ≤ ∑ j, (D.tile j).localAngle p :=
    Finset.single_le_sum (fun j _ => (D.tile j).localAngle_nonneg p) (Finset.mem_univ i)
  rw [hsum, hi] at hle
  nlinarith [Real.pi_pos]

end Erdos634.PinPlumbing
