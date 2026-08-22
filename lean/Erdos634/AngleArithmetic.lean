/-
AngleArithmetic.lean — the angle calculus of the base-β branch (Erdős #634).
No imports, no axioms: kernel-checked with the core toolchain only.

SETTING. The tile has angles α, β, γ with γ = 2α+β and 3α+2β = π, and α/π is irrational
(proved in the project without citation: sin(α/2) = e/(2f) ∈ (0,½) for 1 ≤ e < f, so Niven's
theorem applies). Consequently **α/β is irrational too**: if α/β = p/q then 3(p/q)β + 2β = π
gives β = qπ/(3p+2q), a rational multiple of π, hence so is α — contradiction. This is the one
geometric input; it is PROVED in the project and assumed here.

CONSEQUENCE, AND WHAT THIS FILE PINS. Because α/β is irrational, an angle has AT MOST ONE
representation x·α + y·β with x,y ≥ 0: two of them would give (x−x')α = (y'−y)β. So every angle
occurring in a dissection is faithfully encoded by its coefficient pair, and all the geometry of
vertex figures becomes linear arithmetic over ℕ:

    α ↦ (1,0)      β ↦ (0,1)      γ = 2α+β ↦ (2,1)      π = 3α+2β ↦ (3,2)

A vertex figure of angle (X,Y) is a multiset of tile angles summing to it: with `na` copies of α,
`nb` of β and `ng` of γ,
    na + 2·ng = X        and        nb + ng = Y.
Everything below is that system, solved.

  · `no_right_angle`  — π/2 has no representation: it would need 2x = 3. Hence **no piece of any
    dissection in this branch has a right angle**, for every member (e,f). This kills every
    perpendicular-cut construction outright, e.g. splitting the target along its altitude.
  · `apex_forced`     — the target's apex angle 3α admits exactly one vertex figure, three α's.
  · `pi_vertex`       — a straight angle admits exactly {α,α,α,β,β} or {γ,α,β}: at most one γ,
    which is the γ-trap used by the forcing chain.
  · `beta_lt_pi3_*`   — β < π/3 ⟺ e(3f²−e²) > f³. At e = 1 this holds only at f = 2, so the
    member (1,2) — the only one whose full spectrum is known — is atypical of its own family.
-/

namespace Erdos634.AngleArithmetic

/-! ## Representability -/

/-- **No right angle.** `π/2` would be an angle `x·α + y·β` with `2·(xα+yβ) = π = 3α+2β`, i.e.
`2x = 3` and `2y = 2`. The first is impossible. -/
theorem no_right_angle (x y : Nat) : ¬ (2 * x = 3 ∧ 2 * y = 2) := by omega

/-- The same statement in the form the geometry uses: no dissection piece has a right angle. -/
theorem no_perpendicular_cut : ¬ ∃ x y : Nat, 2 * x = 3 ∧ 2 * y = 2 := by
  intro h
  obtain ⟨x, y, hx, hy⟩ := h
  exact no_right_angle x y ⟨hx, hy⟩

/-! ## Vertex figures.  `na` α's, `nb` β's, `ng` γ's at a vertex of angle `X·α + Y·β`:
        na + 2·ng = X,   nb + ng = Y. -/

/-- **The apex is forced.** At the target's apex, `X = 3`, `Y = 0`: the only vertex figure is
three `α`-corners. -/
theorem apex_forced (na nb ng : Nat) (hx : na + 2 * ng = 3) (hy : nb + ng = 0) :
    na = 3 ∧ nb = 0 ∧ ng = 0 := by omega

/-- **A base corner is forced.** At angle `β` (`X = 0`, `Y = 1`) the only figure is a single
`β`-corner — the S1 corner lemma of the forcing chain. -/
theorem beta_corner_forced (na nb ng : Nat) (hx : na + 2 * ng = 0) (hy : nb + ng = 1) :
    na = 0 ∧ nb = 1 ∧ ng = 0 := by omega

/-- **The γ-trap.** A straight angle (`X = 3`, `Y = 2`) carries at most one `γ`, and the two
figures are exactly `{α,α,α,β,β}` and `{γ,α,β}`. -/
theorem pi_vertex (na nb ng : Nat) (hx : na + 2 * ng = 3) (hy : nb + ng = 2) :
    (na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1) := by omega

theorem gamma_trap (na nb ng : Nat) (hx : na + 2 * ng = 3) (hy : nb + ng = 2) : ng ≤ 1 := by omega

/-- The angle `α+β` (`X = Y = 1`) is filled only by one `α` and one `β`: the strip's corner. -/
theorem alpha_beta_corner (na nb ng : Nat) (hx : na + 2 * ng = 1) (hy : nb + ng = 1) :
    na = 1 ∧ nb = 1 ∧ ng = 0 := by omega

/-! ## Where β sits relative to π/3.
`3α > β ⟺ β < π/3 ⟺ cos β > 1/2 ⟺ e(3f²−e²) > f³`. -/

/-- Members with `β < π/3`, by direct computation of `e(3f²−e²) − f³`. -/
theorem beta_lt_pi3_1_2 : 1 * (3 * (2 * 2) - 1 * 1) > 2 * 2 * 2 := by decide
theorem beta_lt_pi3_2_3 : 2 * (3 * (3 * 3) - 2 * 2) > 3 * 3 * 3 := by decide
theorem beta_lt_pi3_3_4 : 3 * (3 * (4 * 4) - 3 * 3) > 4 * 4 * 4 := by decide

/-- …and the `e = 1` members with `f ≥ 3` all fail it. Seed: `f ≥ 3 ⟹ 3f² ≤ f³`. -/
theorem cube_ge_three_sq (f : Nat) (h : 3 ≤ f) : 3 * (f * f) ≤ f * (f * f) :=
  Nat.mul_le_mul_right (f * f) h

theorem beta_ge_pi3_e1 (f : Nat) (h : 3 ≤ f) : 1 * (3 * (f * f) - 1 * 1) < f * f * f := by
  have hc := cube_ge_three_sq f h
  have hf : 3 * (f * f) ≤ f * f * f := by
    have : f * (f * f) = f * f * f := by
      rw [Nat.mul_assoc]
    omega
  have hpos : 0 < f * f := Nat.mul_pos (by omega) (by omega)
  omega

/-- **(1,2) is the unique `e = 1` member with `β < π/3`.** Combining the two previous results:
`f = 2` satisfies the inequality and every `f ≥ 3` violates it. The member whose full instance
spectrum is known is therefore not typical of its family. -/
theorem unique_e1_beta_lt_pi3 (f : Nat) (h : 3 ≤ f) :
    (1 * (3 * (2 * 2) - 1 * 1) > 2 * 2 * 2) ∧ ¬ (1 * (3 * (f * f) - 1 * 1) > f * f * f) := by
  refine ⟨beta_lt_pi3_1_2, ?_⟩
  have := beta_ge_pi3_e1 f h
  omega

end Erdos634.AngleArithmetic
