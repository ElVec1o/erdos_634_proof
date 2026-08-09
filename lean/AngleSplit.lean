-- AngleSplit.lean — the bridge from an angle relation at a vertex to the Diophantine system.
--
-- Every vertex-figure result in this development (corner_beta_unique, corner_apex_unique,
-- pi_vertex_figures, two_pi_vertex_figures, pi_vertex_gamma_le_one) is stated in terms of the
-- integer system
--        2p - 3q + r = sigma,      q + r = tau,
-- and the step that produces that system from the geometry -- "since alpha/pi is irrational, an
-- angle relation splits" -- was carried in prose only. This file formalises it.
--
-- With 3a + 2b = pi and c = 2a + b one has 2b = pi - 3a and 2c = a + pi, so doubling
--        p*a + q*b + r*c = t*pi
-- gives  a*(2p - 3q + r) = pi*(2t - q - r).
-- Irrationality of a/pi forces both integer coefficients to vanish.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Erdos634.AngleSplit

/-- **The angle relation splits.** Let the tile angles satisfy `3α + 2β = π` and `γ = 2α + β`, with
`α/π` irrational. If a vertex carries `p` copies of `α`, `q` of `β` and `r` of `γ`, totalling `tπ`,
then `2p + r = 3q` and `q + r = 2t`.

This is the hypothesis shape consumed by `BaseBetaCorners.pi_vertex_figures`,
`two_pi_vertex_figures`, `corner_beta_unique` and `corner_apex_unique`; irrationality of `α/π` is
supplied at every member by `BaseBetaE1.tile_alpha_irrational`, via Niven. -/
theorem angle_relation_split {α β γ : ℝ} {p q r t : ℕ}
    (hβ : 3 * α + 2 * β = Real.pi) (hγ : γ = 2 * α + β)
    (hirr : Irrational (α / Real.pi))
    (h : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = (t : ℝ) * Real.pi) :
    2 * (p : ℤ) + r = 3 * q ∧ (q : ℤ) + r = 2 * t := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hb : β = (Real.pi - 3 * α) / 2 := by linarith
  have hg : γ = (Real.pi + α) / 2 := by rw [hγ, hb]; ring
  -- α · (2p − 3q + r) = π · (2t − q − r)
  have key : α * (2 * (p : ℝ) - 3 * (q : ℝ) + (r : ℝ))
           = Real.pi * (2 * (t : ℝ) - (q : ℝ) - (r : ℝ)) := by
    rw [hb, hg] at h; linarith [h]
  -- the α-coefficient vanishes, else α/π is rational
  have hM : 2 * (p : ℝ) - 3 * (q : ℝ) + (r : ℝ) = 0 := by
    by_contra hM0
    apply hirr
    refine ⟨(2 * (t : ℚ) - (q : ℚ) - (r : ℚ)) / (2 * (p : ℚ) - 3 * (q : ℚ) + (r : ℚ)), ?_⟩
    have hMq : ((2 * (p : ℚ) - 3 * (q : ℚ) + (r : ℚ) : ℚ) : ℝ)
             = 2 * (p : ℝ) - 3 * (q : ℝ) + (r : ℝ) := by push_cast; ring
    push_cast
    rw [div_eq_div_iff hM0 hpi]
    linarith [key]
  -- and then the π-coefficient vanishes too
  have hN : 2 * (t : ℝ) - (q : ℝ) - (r : ℝ) = 0 := by
    rw [hM, mul_zero] at key
    rcases mul_eq_zero.mp key.symm with h1 | h1
    · exact absurd h1 hpi
    · exact h1
  constructor
  · have : (2 * (p : ℤ) + r : ℤ) = 3 * q := by exact_mod_cast (by linarith [hM] : (2 * (p:ℝ) + r) = 3 * q)
    exact this
  · have : ((q : ℤ) + r : ℤ) = 2 * t := by exact_mod_cast (by linarith [hN] : ((q:ℝ) + r) = 2 * t)
    exact this

end Erdos634.AngleSplit
