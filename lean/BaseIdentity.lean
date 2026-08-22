import Mathlib.Tactic

/-!
# The base identity

Erdős #634 — the necessary condition behind the equilateral classification, formalized.

Let a triangle `T` with angles `A, B, C` tile a target triangle into `N` congruent copies.
Write `s` for the circumdiameter of `T`, so its sides are `a = s sin A`, `b = s sin B`,
`c = s sin C`.

Two facts hold of any such tiling:

* **Whole-edge boundary.**  A side of `T` lying along a side of the target lies along it
  *entirely*: the tile is inside the target, so a side of it meeting the boundary line does so
  along its whole length.  Hence each target side is partitioned into whole tile edges, and a
  target side of length `S` satisfies `S = x a + y b + z c` for nonnegative integers `x, y, z`.
* **Area.**  `N · area(T) = area(target)`, and `area(T) = (1/2) s² sin A sin B sin C`.

Eliminating `s` between the two gives a relation between the boundary word `(x,y,z)`, the tile's
angles, and `N`, with **no field or representability assumption**.  For an equilateral target of
side `S` the area is `(√3/4) S²`, and the relation is `equilateral_base_identity`:

  `r₃ · (x sin A + y sin B + z sin C)² = 2 N sin A sin B sin C`,   `r₃ = √3`.

This is the condition that reduces the rational-angle tiles of an equilateral to four candidates;
`EquilateralSpectrum` solves each of the four.  `general_base_identity` records the same
elimination for an arbitrary target triangle, where two sides `S₁, S₂` meet at angle `θ`.

Note what the identity needs: a degree of freedom in the tile.  On a family where both tile and
target are pinned by the same parameters — the base-β family of the main paper, where
`(a,b,c) = (ef, f²-e², f²)` and the target is `(f³, f³, e N₀)` — it degenerates to an identity in
`(e,f)` and constrains nothing.  That is recorded in the research log as a dead end.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BaseIdentity

/-- **The base identity for an equilateral target.**  With `ρ = x sin A + y sin B + z sin C` the
scaled boundary word, `S = s ρ` the target side, and the area equation
`N · (1/2) s² sin A sin B sin C = (√3/4) S²`, the scale `s` cancels and

  `√3 ρ² = 2 N sin A sin B sin C`. -/
theorem equilateral_base_identity (sA sB sC s S ρ N r₃ : ℝ) (hs : s ≠ 0)
    (hS : S = s * ρ)
    (harea : N * ((1 / 2) * s ^ 2 * (sA * sB * sC)) = (r₃ / 4) * S ^ 2) :
    r₃ * ρ ^ 2 = 2 * N * (sA * sB * sC) := by
  subst hS
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have h : s ^ 2 * (2 * N * (sA * sB * sC)) = s ^ 2 * (r₃ * ρ ^ 2) := by nlinarith [harea]
  exact (mul_left_cancel₀ hs2 h).symm

/-- The same with the boundary word written out: `ρ = x sin A + y sin B + z sin C`, which is what
the whole-edge boundary fact supplies. -/
theorem equilateral_base_identity_word (sA sB sC s S N x y z r₃ : ℝ) (hs : s ≠ 0)
    (hS : S = x * (s * sA) + y * (s * sB) + z * (s * sC))
    (harea : N * ((1 / 2) * s ^ 2 * (sA * sB * sC)) = (r₃ / 4) * S ^ 2) :
    r₃ * (x * sA + y * sB + z * sC) ^ 2 = 2 * N * (sA * sB * sC) := by
  refine equilateral_base_identity sA sB sC s S _ N r₃ hs ?_ harea
  rw [hS]; ring

/-- **The general target.**  If two sides `S₁, S₂` of the target meet at angle `θ`, its area is
`(1/2) S₁ S₂ sin θ`, and the same elimination gives `ρ₁ ρ₂ sin θ = N sin A sin B sin C`. -/
theorem general_base_identity (sA sB sC s S₁ S₂ ρ₁ ρ₂ sθ N : ℝ) (hs : s ≠ 0)
    (h1 : S₁ = s * ρ₁) (h2 : S₂ = s * ρ₂)
    (harea : N * ((1 / 2) * s ^ 2 * (sA * sB * sC)) = (1 / 2) * S₁ * S₂ * sθ) :
    ρ₁ * ρ₂ * sθ = N * (sA * sB * sC) := by
  subst h1; subst h2
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have h : s ^ 2 * (N * (sA * sB * sC)) = s ^ 2 * (ρ₁ * ρ₂ * sθ) := by nlinarith [harea]
  exact (mul_left_cancel₀ hs2 h).symm

/-- **Why it is vacuous on the base-β family.**  There the tile is `(ef, f²-e², f²)` and the target
`(f³, f³, e N₀)` with `N₀ = 3f² - e²`, so the general identity, cleared of the scale, reads
`S_side · S_base = N · a · c`, i.e. `f³ · e N₀ = N₀ · (e f) · f²`.  Both sides are `e f³ N₀`: it
holds for every member and every word, so it excludes nothing. -/
theorem base_beta_identity_is_vacuous (e f : ℤ) :
    f ^ 3 * (e * (3 * f ^ 2 - e ^ 2)) = (3 * f ^ 2 - e ^ 2) * (e * f) * f ^ 2 := by ring

end Erdos634.BaseIdentity

#print axioms Erdos634.BaseIdentity.equilateral_base_identity
#print axioms Erdos634.BaseIdentity.equilateral_base_identity_word
#print axioms Erdos634.BaseIdentity.general_base_identity
#print axioms Erdos634.BaseIdentity.base_beta_identity_is_vacuous
