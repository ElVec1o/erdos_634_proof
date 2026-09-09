/-
ScaleBreak.lean — why the m = 1 exclusion machinery does not reach m = 2 (Erdős #634, base-β).
No imports, no axioms: kernel-checked with the core toolchain only.

BACKGROUND. The prime theorem excludes every base-β instance at m = 1. One of its load-bearing
pillars is `side_no_b`: at m = 1 no equal side of the target carries a b-edge. Its proof is walk
arithmetic plus the γ-trap. A side of the scale-m target has length m·X₁ = m·f³, and a walk
(P,Q,R) on it satisfies P·a + Q·b + R·c = m f³ with (a,b,c) = (ef, f²−e², f²). Reducing mod f
forces f ∣ Q, say Q = f·q, and the walk equation becomes

    P·e + q·(f² − e²) + R·f = m·f² .                                    (∗)

At m = 1 and q = 1 this reads P·e + R·f = e², which together with the γ-trap (R ≥ 1) has no
solution — that is exactly `side_no_b`.

WHAT THIS FILE PINS. At m = 2 the same slot is occupied, universally: `side_walk_m2` exhibits the
walk (P,Q,R) = (e, f, f), which carries f b-edges and satisfies the length equation as a ring
identity for EVERY member. Hence `side_no_b` is false at m = 2, and the first structural step of
the m = 1 forcing chain is unavailable there.

This is not a defect of the proof: Δ₂ genuinely tiles at (1,2) (the 44-tiling, kernel-certified in
`Tiling44.lean`, and constructively as 16 + 28 via `CevianTiling28.lean`), so NO argument can
exclude Δ₂ in general. Any result about Δ₂ must therefore be member-specific — by construction, or
by exhaustive search. The file records the precise obstruction so the chain is not retried at
m = 2.
-/

namespace Erdos634.ScaleBreak

/-- **The m = 2 side walk exists for every member.** With (a,b,c) = (ef, f²−e², f²), the triple
(P,Q,R) = (e, f, f) satisfies P·a + Q·b + R·c = 2f³. Subtraction-free form (e ≤ f keeps
f² − e² a genuine natural number, and the identity is stated with it moved to the other side). -/
theorem side_walk_m2 (e f : Nat) (h : e ≤ f) :
    e * (e * f) + f * (f * f - e * e) + f * (f * f) = 2 * (f * f * f) := by
  have hle : e * e ≤ f * f := Nat.mul_le_mul h h
  have h1 : f * (f * f - e * e) + f * (e * e) = f * (f * f) := by
    rw [← Nat.mul_add]
    have : f * f - e * e + e * e = f * f := by omega
    rw [this]
  have h2 : e * (e * f) = f * (e * e) := by
    rw [Nat.mul_comm e f, ← Nat.mul_assoc, Nat.mul_comm e f, Nat.mul_assoc]
  have h3 : f * (f * f) + f * (f * f) = 2 * (f * f * f) := by
    rw [Nat.mul_assoc]
    omega
  omega

-- CONTENT-FREE (audit 2026-09-10): `side_walk_m2_has_b` is the identity function `h ↦ h`
-- (`0 < f` and `1 ≤ f` are the same proposition on `Nat`).  It asserts nothing about walks,
-- b-edges or `side_no_b`, and must not be cited as evidence that the counterexample exists.
-- The real statement is `side_no_b_fails_m2` below, which is stated in the exact hypothesis
-- shape of `BaseBetaWalks.side_no_b` and exhibits the witness.
theorem side_walk_m2_has_b (f : Nat) (h : 1 ≤ f) : 0 < f := h

/-- **`side_no_b` fails at `m = 2`, for every member.**  Stated in the exact hypothesis shape of
`BaseBetaWalks.side_no_b` (`B` the `b`-edge length with `B + e² = f²`, walk equation on the equal
side, γ-trap `1 ≤ R`), with the side length doubled to `2f³`: the witness `(P,Q,R) = (e,f,f)`
satisfies the walk equation, respects the γ-trap, **and has `Q ≠ 0`** — the conclusion `Q = 0` that
`side_no_b` proves at `m = 1`.  So the `m = 1` forcing chain's first structural step is genuinely
unavailable at `m = 2`, and this is what the `ScaleBreak` row of `PAPER_MAP.md` claims. -/
theorem side_no_b_fails_m2 (e f B : Nat) (he : 1 ≤ e) (hef : e < f) (hB : B + e ^ 2 = f ^ 2) :
    ∃ P Q R : Nat, 1 ≤ R ∧ Q ≠ 0 ∧ P * (e * f) + Q * B + R * f ^ 2 = 2 * f ^ 3 := by
  refine ⟨e, f, f, by omega, by omega, ?_⟩
  have hse : e ^ 2 = e * e := by rw [Nat.pow_succ, Nat.pow_one]
  have hsf : f ^ 2 = f * f := by rw [Nat.pow_succ, Nat.pow_one]
  have hcf : f ^ 3 = f * f * f := by rw [Nat.pow_succ, hsf]
  rw [hse] at hB
  rw [hsf, hcf]
  have hBv : B = f * f - e * e := by omega
  subst hBv
  have hwalk := side_walk_m2 e f (Nat.le_of_lt hef)
  omega

/-! ## The slot that closes at m = 1 and opens at m = 2.
With Q = f·q, the walk equation is P·e + q·(f²−e²) + R·f = m·f². At q = 1: -/

/-- m = 1, q = 1: the residual length is `e²`, and the γ-trap `R ≥ 1` needs `R·f ≤ e²`. For the
frontier members this is impossible, which is `side_no_b`. Checked per member. -/
theorem no_b_m1_1_2 (P R : Nat) (hR : 1 ≤ R) : P * 1 + R * 2 ≠ 1 * 1 := by omega
theorem no_b_m1_1_3 (P R : Nat) (hR : 1 ≤ R) : P * 1 + R * 3 ≠ 1 * 1 := by omega
theorem no_b_m1_1_4 (P R : Nat) (hR : 1 ≤ R) : P * 1 + R * 4 ≠ 1 * 1 := by omega
theorem no_b_m1_2_3 (P R : Nat) (hR : 1 ≤ R) : P * 2 + R * 3 ≠ 2 * 2 := by omega
theorem no_b_m1_3_4 (P R : Nat) (hR : 1 ≤ R) : P * 3 + R * 4 ≠ 3 * 3 := by omega

/-- m = 2, q = 1: the residual is `f² + e²`, and `(P,R) = (e,f)` solves it with `R = f ≥ 1`,
so the γ-trap does not close the slot. Same members. -/
-- CONTENT-FREE (code/trivia_audit.py, 2026-08-25): this statement asserts nothing --
-- commutativity of `+` on two numerals.
-- Kept for its docstring's exposition; it carries no mathematical content and must not be
-- cited as evidence that the surrounding claim is established.
theorem b_ok_m2_1_2 : 1 * 1 + 2 * 2 = 2 * 2 + 1 * 1 := by decide
theorem b_ok_m2_1_3 : 1 * 1 + 3 * 3 = 3 * 3 + 1 * 1 := by decide
theorem b_ok_m2_1_4 : 1 * 1 + 4 * 4 = 4 * 4 + 1 * 1 := by decide
theorem b_ok_m2_2_3 : 2 * 2 + 3 * 3 = 3 * 3 + 2 * 2 := by decide
theorem b_ok_m2_3_4 : 3 * 3 + 4 * 4 = 4 * 4 + 3 * 3 := by decide

end Erdos634.ScaleBreak
