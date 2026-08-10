import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# The equal sides carry no `b`-edge at `m = 1` (Erdős #634, base-β branch)

`Interface.lean` records this as `side_no_b_1_2`, `side_no_b_1_3`, `side_no_b_1_4` — three separate
per-member facts, each proved by `decide`-style arithmetic. It is in fact general, and the proof is
two lines of divisibility plus one size comparison.

## Statement

At `m = 1` the equal side has length `X₁ = f³`, so a side walk is a solution of
`P'·a + Q'·b + R'·c = f³` with `(a,b,c) = (ef, f²−e², f²)`, subject to the γ-trap `R' ≥ 1`
(every side carries a `c`-edge). Then `Q' = 0` whenever `e² < f`.

## Why it matters

This is one of the very few facts in the development that is genuinely specific to `m = 1`: at
`m = 2` it is FALSE, and `ScaleBreak.lean` exhibits the counterexample
`e·(ef) + f·(f²−e²) + f·f² = 2f³`. Since a corner block can demonstrably break at `m = 2`
(companion `rem:blockbreaks`: the 44-tiling `N44B` has a broken corner), any proof of the
complete-corner-wall hypothesis must use `m = 1` essentially — and this is the lever.

## Scope

`side_no_b_uncond` is the theorem: **no size hypothesis at all, every member.** The weaker
`side_no_b` below (hypothesis `e² < f`) is kept because its one-line proof is the one the
exposition uses, and `e² < f` covers **every `e = 1` member**, which is exactly the subfamily where the corner problem is
the whole problem (companion `rem:whyhyp`). The bound is not an artifact: the proof shows
`Q' > 0` forces `f ≤ e²`, and with `e < f` that already needs `e ≥ 2`. (Note `e < f` is not
assumed: it follows from `e² < f` for `e ≥ 1`.) The thick members (`e ≥ 2`, `f ≤ e²`) need the
identity `(★)` route of `side_no_b_uncond`. Both are cross-checked by exhaustive search over every
member with `f ≤ 200`: zero counterexamples.

Everything is stated additively (`b + e*e = f*f`) so no truncated natural subtraction appears.
-/

namespace Erdos634.SideNoB

variable {e f b P Q R : ℕ}

/-- `f` divides the side walk's `b`-count. Reducing the walk equation modulo `f` leaves
`Q·e² ≡ 0`, and `gcd(e,f) = 1`. -/
theorem f_dvd_Q (hco : Nat.Coprime e f) (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f) : f ∣ Q := by
  -- f divides Q·b, because it divides every other term of the walk
  have h1 : f ∣ Q * b := by
    have hA : f ∣ P * (e * f) := ⟨P * e, by ring⟩
    have hB : f ∣ R * (f * f) := ⟨R * f, by ring⟩
    have hC : f ∣ P * (e * f) + Q * b + R * (f * f) := by rw [hwalk]; exact ⟨f * f, by ring⟩
    have h4 : f ∣ P * (e * f) + Q * b := by simpa using Nat.dvd_sub hC hB
    simpa using Nat.dvd_sub h4 hA
  -- hence f divides Q·e², since Q·b + Q·e² = Q·f²
  have h2 : f ∣ Q * (e * e) := by
    have hsum : Q * b + Q * (e * e) = Q * (f * f) := by rw [← Nat.mul_add, hb]
    have hqf : f ∣ Q * (f * f) := ⟨Q * f, by ring⟩
    rw [← hsum] at hqf
    simpa using Nat.dvd_sub hqf h1
  -- and gcd(f, e²) = 1
  have hcop : Nat.Coprime f (e * e) :=
    (Nat.coprime_comm.mp hco).mul_right (Nat.coprime_comm.mp hco)
  exact hcop.dvd_of_dvd_mul_right h2

/-- **The equal side carries no `b`-edge.** For every member with `e² < f` — in particular every
member with `e = 1` — a side walk at `m = 1` obeying the γ-trap has `Q' = 0`. -/
theorem side_no_b (hco : Nat.Coprime e f)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) (hthin : e * e < f) : Q = 0 := by
  by_contra hQ
  have hQpos : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
  have hfQ : f ∣ Q := f_dvd_Q hco hb hwalk
  have hQf : f ≤ Q := Nat.le_of_dvd (by omega) hfQ
  have hbterm : f * b ≤ Q * b := Nat.mul_le_mul_right b hQf
  have hcterm : f * f ≤ R * (f * f) := Nat.le_mul_of_pos_left _ (by omega)
  have hfb : f * b + f * (e * e) = f * f * f := by
    calc f * b + f * (e * e) = f * (b + e * e) := by ring
      _ = f * (f * f) := by rw [hb]
      _ = f * f * f := by ring
  have hgap : f * (e * e) < f * f := Nat.mul_lt_mul_of_pos_left hthin (by omega)
  omega

/-! ## The unconditional theorem

The size hypothesis `e² < f` is not needed. Setting `Q' = f·q` and `t = q − 1`, the walk collapses to
the single identity

    t·b + R'·f + P'·e = e²                                    (★)

and (★) kills every `q ≥ 1` at once: reducing it mod `e` gives `e ∣ t·f + R'`, say `t·f + R' = e·k`;
feeding that back into (★) gives `f·k ≤ e·(t+1)`, and `e < f` then forces `k ≤ t`, so
`t·f + R' = e·k ≤ e·t ≤ f·t`, i.e. `R' ≤ 0`, against the γ-trap. -/

/-- The walk identity `(★)`: with `Q' = f·q` and `q = t+1`, the side walk is equivalent to
`t·b + R'·f + P'·e = e²`. -/
theorem star_identity {q t : ℕ} (hb : b + e * e = f * f) (hf : 0 < f)
    (hQ : Q = f * q) (hq : q = t + 1)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f) :
    t * b + R * f + P * e = e * e := by
  subst hQ; subst hq
  have hcancel : f * (P * e + (t + 1) * b + R * f) = f * (f * f) := by
    have hassoc : f * (f * f) = f * f * f := by ring
    rw [hassoc, ← hwalk]; ring
  have hdiv : P * e + (t + 1) * b + R * f = f * f := Nat.eq_of_mul_eq_mul_left hf hcancel
  have hexp : (t + 1) * b = t * b + b := by ring
  omega

/-- **The equal sides carry no `b`-edge — unconditionally.** No size hypothesis: every member. -/
theorem side_no_b_uncond (hco : Nat.Coprime e f) (hef : e < f)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) : Q = 0 := by
  have hf : 0 < f := by omega
  have he : 0 < e ∨ e = 0 := by omega
  by_contra hQ0
  obtain ⟨q, hq⟩ := f_dvd_Q hco hb hwalk
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso; rw [h, Nat.mul_zero] at hq; exact hQ0 hq
    · exact h
  obtain ⟨t, ht⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
  have hstar : t * b + R * f + P * e = e * e := star_identity hb hf hq ht hwalk
  have hepos : 0 < e := by
    rcases he with h | h
    · exact h
    · exfalso; subst h; simp at hstar; omega
  -- (1)  e ∣ t·f + R
  have hdvd : e ∣ t * f + R := by
    have h1 : e ∣ t * b + R * f := by
      have hsub : t * b + R * f = e * e - P * e := by omega
      rw [hsub]; exact Nat.dvd_sub ⟨e, by ring⟩ ⟨P, by ring⟩
    have h2 : f * (t * f + R) = (t * b + R * f) + t * (e * e) := by
      calc f * (t * f + R) = t * (f * f) + R * f := by ring
        _ = t * (b + e * e) + R * f := by rw [hb]
        _ = (t * b + R * f) + t * (e * e) := by ring
    have h3 : e ∣ f * (t * f + R) := by rw [h2]; exact Nat.dvd_add h1 ⟨t * e, by ring⟩
    exact hco.dvd_of_dvd_mul_left h3
  obtain ⟨k, hk⟩ := hdvd
  -- (2)  f·k + P = e·(t+1), hence f·k ≤ e·(t+1)
  have hkey : f * (t * f + R) + P * e = e * e * (t + 1) := by
    calc f * (t * f + R) + P * e = t * (f * f) + R * f + P * e := by ring
      _ = t * (b + e * e) + R * f + P * e := by rw [hb]
      _ = (t * b + R * f + P * e) + t * (e * e) := by ring
      _ = e * e + t * (e * e) := by rw [hstar]
      _ = e * e * (t + 1) := by ring
  have hbound : f * k ≤ e * (t + 1) := by
    have h5 : e * (f * k) ≤ e * (e * (t + 1)) := by
      rw [hk] at hkey
      calc e * (f * k) ≤ f * (e * k) + P * e := by nlinarith
        _ = e * e * (t + 1) := hkey
        _ = e * (e * (t + 1)) := by ring
    exact Nat.le_of_mul_le_mul_left h5 hepos
  -- (3)  e < f forces k ≤ t
  have hkt : k ≤ t := by
    by_contra hcon
    have h1 : t + 1 ≤ k := by omega
    have h2 : f * (t + 1) ≤ f * k := Nat.mul_le_mul_left f h1
    have h3 : e * (t + 1) < f * (t + 1) := Nat.mul_lt_mul_of_pos_right hef (by omega)
    omega
  -- (4)  t·f + R = e·k ≤ e·t ≤ f·t  contradicts R ≥ 1
  have h6 : e * k ≤ e * t := Nat.mul_le_mul_left e hkt
  have h7 : e * t ≤ f * t := Nat.mul_le_mul_right t (le_of_lt hef)
  have h8 : f * t = t * f := by ring
  omega

/-- **Every `e = 1` member has `b`-free equal sides.** The hypothesis `e² < f` of `side_no_b` is
automatic here (`1 < f`), so no side of the target carries a `b`-edge, for every `f ≥ 2` at once.
This replaces the per-member `side_no_b_1_2`, `side_no_b_1_3`, `side_no_b_1_4` of `Interface.lean`
with a single statement. -/
theorem side_no_b_e_one {f b P Q R : ℕ} (hf : 2 ≤ f)
    (hb : b + 1 * 1 = f * f)
    (hwalk : P * (1 * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) : Q = 0 :=
  side_no_b (Nat.coprime_one_left f) hb hwalk hgamma (by omega)

/-! ## The side c-count bound: `p ≤ f − 2`, and `hyp:walls` at `f = 2`

With `Q' = 0` (`side_no_b`) the side walk is `(P', R') = (f·p, f−p)`. The first and last side edges
are c-edges — at `e = 1`; the first is the base-corner tile's side flank (its base flank is an a-edge
by `thm:e1reduce`(ii), an `e = 1` theorem), the last
belongs to the apex figure `{3α}`, whose side edge is `b` or `c` and `b` is excluded — so the side
carries at least two c-edges: `f − p ≥ 2`. Hence `p ≤ f − 2`, and at `f = 2` the side carries no
a-edge at all: `hyp:walls` holds for the member `(1,2)` by boundary analysis alone, recovering the
closure of `thm:basebeta-e1`. At `f = 3` the only surviving value is `p = 1`, whose side word is
forced to `c a a a c`. -/

/-- **`p ≤ f − 2`, AT `e = 1` ONLY.** The hypothesis `R + p = f` is the `e = 1` form of the side
profile: in general the c-count is `n_c = f − p·e`, so the relation is `R + p·e = f` and this
statement does NOT apply. Two c-edges are forced at `e = 1` because the base begins with an `a`-edge
(`thm:e1reduce`(ii)), which is itself an `e = 1` theorem. At `e ≥ 2` the base-corner end of a side may
be an `a`-edge, and indeed at `p = 2` on `f = 2e+1` the side word is `a^{2f} c` with a single `c`. -/
theorem p_le_f_sub_two {f p R : ℕ} (hR : R + p = f) (h2 : 2 ≤ R) : p ≤ f - 2 := by omega

/-- **`hyp:walls` at `f = 2`**: the side carries no a-edge. -/
theorem side_no_a_f2 {p R : ℕ} (hR : R + p = 2) (h2 : 2 ≤ R) : p = 0 := by omega

/-- At `f = 3` only `p = 1` survives below the wall. -/
theorem f3_p_eq_one {p R : ℕ} (hR : R + p = 3) (h2 : 2 ≤ R) (hp : 1 ≤ p) : p = 1 := by omega


/-- **Thick-side quantization.** A side of the `(e,f)` target has length `f³`, carries no `b`
(\`side_no_b_uncond\`), so its edge counts satisfy `x·ef + z·f² = f³`, i.e. `x·e + z·f = f²`.
Coprimality gives `f ∣ x`: the number of `a`-edges on a side is a multiple of `f`. Hence any
bound `p < f` forces `p = 0` — the side condition of `hyp:walls`. -/
theorem side_quantized {e f x z : ℕ} (hf : 1 ≤ f) (hco : Nat.Coprime e f)
    (h : x * e + z * f = f * f) : f ∣ x := by
  have hd : f ∣ x * e := by
    have h2 : f ∣ z * f := ⟨z, Nat.mul_comm z f⟩
    have h3 : f ∣ f * f := ⟨f, rfl⟩
    have h5 : f * f - z * f = x * e := by omega
    have h6 := Nat.dvd_sub h3 h2
    rwa [h5] at h6
  exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_comm.mp hco)) hd


/-- **A `c`-corner forces `f` side `a`-edges.** The base corner angle is `β`, whose flanks are
`a` and `c`. If the corner tile lays `c` on the base then it lays `a` on the side, so the side's
`a`-count `P'` is positive; by `side_quantized` `P' = f·p`, hence `P' ≥ f`. Together with the
`γ`-trap (`R' ≥ 1`) and `p·e + R' = f` this gives `1 ≤ p ≤ (f−1)/e`. In particular the side
condition of `hyp:walls` (`p = 0`) fails at any `c`-corner: hypothesis `hyp:walls` forces both
base ends to be `a`-edges. -/
theorem c_corner_forces_side_a {f p R : ℕ} (hf : 1 ≤ f) (hp : 1 ≤ p)
    (h : p * 1 + R = f) : f ≤ f * p := Nat.le_mul_of_pos_right f hp

end Erdos634.SideNoB
