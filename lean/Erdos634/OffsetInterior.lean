import Mathlib.Tactic

/-!
# The arithmetic of `lem:offsets` and `lem:interior`, formalized

Erdős #634 — closing the arithmetic half of the two lemmas that finish the `e = 1` case.

## Where these sit

`thm:e1family`'s chain ends: a terminal column's base apex is pinned by `lem:offsets` to a multiple
of `f`, and `lem:interior` then shows a `b`- or `c`-edge starting below `f²` would swallow such an
apex, so `[0, f²)` carries `a`-edges only — `f` of them, since `f·a = f²`.  The walk `a^f b c` then
ends in `b` or `c`, contradicting `thm:e1reduce`'s "first and last edges are `a`", and `e = 1`
closes.

The companion states both lemmas with proofs and calls their content the "arithmetic pivots"; the
**geometric** setup that produces the column is what it defers.  This file formalizes the
arithmetic, which was not machine-checked before.

## `lem:offsets`

A level contributes an apex offset `ε/(2f)` with `ε ∈ {3f² - 1, -(f² - 1)}` — these are exactly
`c·cos β` and `-b·|cos γ|`, since `cos β = (3f²-1)/(2f³)` and `cos γ = -1/(2f)`.  Modulo `f` they
are `-1` and `+1` (`eps_residues`), because `f² ≡ 0`.

With `j` levels, `p` taking `+1` and `q = j - p` taking `-1`, `Σε ≡ p - q` and so
`Σε - j = -2q` (`sum_minus_j`).  Integrality of a base vertex forces `f ∣ 2q` for odd `f` and
`2f ∣ 2q` for even `f`, hence `f ∣ q` either way; with `q ≤ j < f` that gives `q = 0`
(`q_is_zero`).  Every level is then `(γ,β)`-oriented and the apex lands at

  `[j(3f² - 1) - j(f² - 1)] / (2f) = j·f`  (`apex_at_multiple`),

a multiple of `f`.

## `lem:interior`

Both odd edge lengths exceed `f`: `f² - 1 > f` and `f² > f` for `f ≥ 2` (`edges_exceed_f`).  An open
interval longer than `f` always contains a multiple of `f`, and for a left end `x < f²` the first
such multiple is at most `f²` and lies strictly inside the edge (`multiple_inside`).  That multiple
is a column apex, and no tile vertex may lie interior to a boundary edge — so no `b`- or `c`-edge
starts below `f²`, and `[0, f²)` is covered by `a`-edges alone.

## Scope

This formalizes the arithmetic only.  The geometric input — that the column exists and that its
base apex has the stated form — is the deferred part and is **not** proved here, so `e = 1` is not
closed by this file.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.OffsetInterior

/-! ### `lem:offsets` -/

/-- **The two offsets are `∓1` mod `f`.**  `f² ≡ 0`, so `3f² - 1 ≡ -1` and `-(f² - 1) ≡ 1`. -/
theorem eps_residues (f : ℤ) :
    (3 * f ^ 2 - 1) % f = (-1) % f ∧ (-(f ^ 2 - 1)) % f = 1 % f := by
  constructor
  · have h : 3 * f ^ 2 - 1 = (-1) + f * (3 * f) := by ring
    rw [h, Int.add_mul_emod_self_left]
  · have h : -(f ^ 2 - 1) = 1 + f * (-f) := by ring
    rw [h, Int.add_mul_emod_self_left]

/-- **`Σε - j = -2q`.**  With `p + q = j` and `Σε ≡ p - q`. -/
theorem sum_minus_j (p q j S : ℤ) (hj : p + q = j) (hS : S = p - q) : S - j = -2 * q := by
  subst hj; subst hS; ring

/-- **`q = 0`.**  Integrality gives `f ∣ q`, and `q < f` with `q ≥ 0` finishes. -/
theorem q_is_zero (f q : ℤ) (hdvd : f ∣ q) (hq0 : 0 ≤ q) (hqf : q < f) : q = 0 := by
  obtain ⟨k, rfl⟩ := hdvd
  rcases lt_trichotomy k 0 with h | h | h
  · nlinarith
  · simp [h]
  · nlinarith

/-- `f ∣ 2q` with `f` odd gives `f ∣ q`. -/
theorem odd_case (f q : ℤ) (hodd : ¬ (2 ∣ f)) (h : f ∣ 2 * q) : f ∣ q := by
  obtain ⟨k, hk⟩ := h
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    refine ⟨m, ?_⟩
    have hexp : 2 * q = 2 * (f * m) := by rw [hk]; ring
    omega
  · subst hm
    refine absurd ⟨q - f * m, ?_⟩ hodd
    have hexp : 2 * q = 2 * (f * m) + f := by rw [hk]; ring
    omega

/-- `2f ∣ 2q` gives `f ∣ q`. -/
theorem even_case (f q : ℤ) (h : 2 * f ∣ 2 * q) : f ∣ q := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by linarith⟩

/-- **The apex lands on a multiple of `f`.**  With `q = 0` every `ε` is `-(f² - 1)`, and
`j(3f² - 1) - j(f² - 1) = 2f · (j f)`. -/
theorem apex_at_multiple (f j : ℤ) :
    j * (3 * f ^ 2 - 1) + j * (-(f ^ 2 - 1)) = 2 * f * (j * f) := by ring

/-! ### `lem:interior` -/

/-- **Both odd edges exceed `f`.**  `f² - 1 > f` and `f² > f` for `f ≥ 2`. -/
theorem edges_exceed_f (f : ℕ) (hf : 2 ≤ f) : f < f ^ 2 - 1 ∧ f < f ^ 2 := by
  have h : f + 1 < f ^ 2 := by nlinarith
  omega

/-- **A multiple of `f` lies strictly inside.**  For a left end `x < f²`, the first multiple of `f`
above `x` is at most `f²` and lies below `x + (f² - 1)`, hence strictly inside either odd edge. -/
theorem multiple_inside (f x : ℕ) (hf : 2 ≤ f) (hx : x < f ^ 2) :
    ∃ m, f ∣ m ∧ x < m ∧ m ≤ f ^ 2 ∧ m < x + (f ^ 2 - 1) := by
  have hf0 : 0 < f := by omega
  have hdm : f * (x / f) + x % f = x := Nat.div_add_mod x f
  have hmod : x % f < f := Nat.mod_lt _ hf0
  have heq : f * (x / f + 1) = f * (x / f) + f := by ring
  refine ⟨f * (x / f + 1), ⟨x / f + 1, rfl⟩, by omega, ?_, ?_⟩
  · have hxf : x / f + 1 ≤ f := by
      have h1 : x / f < f := by
        apply Nat.div_lt_of_lt_mul
        calc x < f ^ 2 := hx
          _ = f * f := by ring
      omega
    calc f * (x / f + 1) ≤ f * f := Nat.mul_le_mul_left f hxf
      _ = f ^ 2 := by ring
  · have hsq : f < f ^ 2 - 1 := (edges_exceed_f f hf).1
    omega

end Erdos634.OffsetInterior

#print axioms Erdos634.OffsetInterior.eps_residues
#print axioms Erdos634.OffsetInterior.sum_minus_j
#print axioms Erdos634.OffsetInterior.q_is_zero
#print axioms Erdos634.OffsetInterior.odd_case
#print axioms Erdos634.OffsetInterior.even_case
#print axioms Erdos634.OffsetInterior.apex_at_multiple
#print axioms Erdos634.OffsetInterior.edges_exceed_f
#print axioms Erdos634.OffsetInterior.multiple_inside
