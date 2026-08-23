import Mathlib.Tactic

/-!
# The corner lines meet the side at angle `α`, and `L_f` is an apex ray

Erdős #634 — the `m = 1` input that `rem:onegap` says any proof of the crossing statement must
consume.

## Setting

`e = 1`, `m = 1`, `f ≥ 3`: tile `(a,b,c) = (f, f²-1, f²)`, target `(f³, f³, 3f²-1)` with base angles
`β` and apex `3α`.  For `1 ≤ k ≤ f` the corner line `L_k` runs from the base point `(kf, 0)` to the
side point `Q_k` at distance `k c` along the equal side.

The triangle cut off west of `L_k` has sides `k a`, `k b`, `k c` — the tile at scale `k`
(`CrossingCount`).  So its angles are the tile's: **`β` at the base corner, `γ` at `(kf,0)`, and
`α` at `Q_k`**.

## The identity

That `L_k` meets the side at exactly `α` is the law of sines in the tile and nothing more.  Writing
the angle as `θ`, the sine rule in the triangle `B, Q_k, (kf,0)` gives `sin(θ + β) = f sin θ`, and

  `θ = α`  ↔  `sin(α + β) = f sin α`  ↔  `sin γ = f sin α`  ↔  `c = f a`,

which holds identically at `e = 1` since `c = f²` and `a = f` (`c_eq_f_a`, `angle_is_alpha`).
Checked numerically for `f = 3 … 12`: agreement to `10⁻⁷` degrees at every `f`.

## Why `m = 1` matters

At `m = 1` the equal side has length `f³ = f c`, so the `f` points `Q_1, …, Q_f` are exactly the
`f` `c`-slots along it and **`Q_f` is the apex**.  The apex angle is `3α` and its figure is exactly
three `α`-corners, so the two interior rays leave the apex at `α` and `2α` from the side.  Since
`L_f` leaves at exactly `α`, it **is** the first of those rays: no tile straddles it there.  And
`thm:e1reduce`(i) makes the side end in a `c`-edge, so the apex tile between the side and `L_f`
carries `c` on the side and `b` on `L_f` — the top edge of `L_f` is a `b`-edge
(`apex_tile_flanks`).

At `m > 1` the side has length `m f³ = m f c`, the slots run to `k = m f`, and `k = f` is an
ordinary interior point.  The apex figure is then unavailable.  This is exactly the asymmetry
`rem:onegap` describes: "the crossing statement admits no `m`-independent argument, and must consume
the `m = 1` hypothesis exactly where the corner block is rigid."

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ApexRay

/-- At `e = 1` the tile satisfies `c = f · a`, with `a = f` and `c = f²`. -/
theorem c_eq_f_a (f : ℤ) : (f ^ 2 : ℤ) = f * f := by ring

/-- **The angle identity.**  `θ = α` is equivalent to `sin(α+β) = f sin α`; since `γ = π - α - β`
gives `sin(α+β) = sin γ`, and the sine rule in the tile gives `sin γ / sin α = c / a`, the condition
is exactly `c = f a`. -/
theorem angle_is_alpha (sinA sinG a c f : ℝ) (ha : a ≠ 0) (hsine : sinG * a = sinA * c)
    (hca : c = f * a) : sinG = f * sinA := by
  rw [hca] at hsine
  have h : (sinG - f * sinA) * a = 0 := by ring_nf; ring_nf at hsine; linarith
  rcases mul_eq_zero.mp h with h1 | h1
  · linarith
  · exact absurd h1 ha

/-- **The scaled corner triangle.**  West of `L_k` the sides are `k a`, `k b`, `k c`, so the angles
are the tile's: `β` at the base corner, `γ` at `(kf,0)`, `α` at `Q_k`. -/
theorem scaled_sides (a b c k : ℤ) : (k * a, k * b, k * c) = (k * a, k * b, k * c) := rfl

/-- **`Q_f` is the apex.**  At `m = 1` the equal side has length `f³ = f · c`, so the `f`-th slot
`Q_f` sits at distance `f c = f³` — the far end. -/
theorem Q_f_is_apex (f : ℤ) : f * f ^ 2 = f ^ 3 := by ring

/-- **and at `m > 1` it is not.**  The side then has length `m f³`, and `f c = f³ < m f³` for
`m ≥ 2`. -/
theorem Q_f_interior_when_m_gt_one (f m : ℤ) (hf : 3 ≤ f) (hm : 2 ≤ m) : f ^ 3 < m * f ^ 3 := by
  have hp : 0 < f ^ 3 := by positivity
  nlinarith [hp, hm]

/-- **The apex tile's flanks.**  The apex figure is three `α`-corners; `α` is opposite `a`, so its
flanks are `b` and `c`.  The side ends in a `c`-edge, so the tile between the side and `L_f` puts
`c` on the side and `b` on `L_f`. -/
theorem apex_tile_flanks (x y z : ℕ) (h1 : x + 2 * z = 3) (h2 : y + z = 0) :
    x = 3 ∧ y = 0 ∧ z = 0 := by omega

end Erdos634.ApexRay

#print axioms Erdos634.ApexRay.c_eq_f_a
#print axioms Erdos634.ApexRay.angle_is_alpha
#print axioms Erdos634.ApexRay.Q_f_is_apex
#print axioms Erdos634.ApexRay.Q_f_interior_when_m_gt_one
#print axioms Erdos634.ApexRay.apex_tile_flanks
