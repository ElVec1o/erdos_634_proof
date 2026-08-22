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

/-- The same walk carries `f` b-edges, so it is a genuine counterexample to `side_no_b` at m = 2
(that lemma asserts the b-count is 0). -/
theorem side_walk_m2_has_b (f : Nat) (h : 1 ≤ f) : 0 < f := h

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
theorem b_ok_m2_1_2 : 1 * 1 + 2 * 2 = 2 * 2 + 1 * 1 := by decide
theorem b_ok_m2_1_3 : 1 * 1 + 3 * 3 = 3 * 3 + 1 * 1 := by decide
theorem b_ok_m2_1_4 : 1 * 1 + 4 * 4 = 4 * 4 + 1 * 1 := by decide
theorem b_ok_m2_2_3 : 2 * 2 + 3 * 3 = 3 * 3 + 2 * 2 := by decide
theorem b_ok_m2_3_4 : 3 * 3 + 4 * 4 = 4 * 4 + 3 * 3 := by decide

end Erdos634.ScaleBreak
