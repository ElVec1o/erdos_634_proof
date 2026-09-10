import Erdos634.N1GapSubcases

/-!
# The `L = c` seam is a single boundary configuration, and it terminates immediately

Erdős #634, `e ≥ 2` branch of `thm:n1`.  `N1GapSubcases` splits the surviving crossing branch at
`V_k` into `2X + 2` configurations, `X = ⌊b/a⌋`.  `N1GapMastGap` proved the `L = b` range
homogeneous (overhang `x·a < b ≤ L'` throughout, no incidence changes type) and exhibited, at
`(e,f) = (2,5)`, a *type change* inside the `L = c` range: overhang `x·a + e²` is `4 < b = 21` at
`x = 0` and `24 > 21` at `x = X = 2`.  That single example was the only thing known about the
`c`-range, and it was the last candidate seam for a telescoping/descent argument in this branch.

This file computes the seam exactly, in general `(e,f)`.  The result is negative, and sharply so.

## 1. The transition is sharp but degenerate

* `overhang_ne_b` — `x·a + e² = b` has **no** solution `x ∈ ℕ`, at any member.  (It forces
  `f ∣ 2e²`, hence `f ∣ 2` by coprimality, against `f ≥ 3`.)  So the overhang never lands exactly
  on `b`: there is no boundary case to handle separately, and the type change, where it occurs, is
  a strict jump.  Equivalently `mod_ne_e_sq`: `b % a ≠ e²`.
* `c_below_top` — for **every** `x < X` the overhang is `< b`, because `e² < a` (`e_sq_lt_a`) and
  `(x+1)·a ≤ X·a < b`.  So the transition, if present, is at the very last index.
* `straddle_only_at_top` / `top_straddle_iff` — the straddling `x` in `0 ≤ x ≤ X` is either none at
  all or the single value `x = X`, and it is present **iff `b % a < e²`**.

So the `c`-range is not a range with a monovariant: it is `X` interior configurations followed by
at most one straddle at the top index.  Its non-homogeneity is one point, not a gradient.

## 2. On three quarters of members it is not even one point

`c_range_dichotomy`: either `b % a < e²` — the seam exists, at `x = X` only — or `e² < b % a`, and
then `x·a + e² < b` for every admissible `x`, i.e. the `c`-range is **exactly as homogeneous as the
`b`-range**.  Equality is impossible (`mod_ne_e_sq`).

The second alternative is the common one.  Heuristically the seam needs an integer in an interval
of length `e/f`, so its density is `e/f`; over the `45292` separated coprime members with `f < 600`
the seam is present in `11259`, i.e. `24.9%`, against a mean `e/f` of `20.7%`.  In particular
`e_one_no_straddle`: at `e = 1` — where `thm:n1` is *proved* — the seam never exists, since
`b % a = f − 1 ≥ 2 > 1 = e²`.  Any argument built on the seam therefore cannot be the missing
`e ≥ 2` argument in the form "the `e = 1` proof, transported": at `e = 1` there is nothing to
transport.

## 3. The seam does not recurse: the chain has length two and stops in a legal T-junction

When the seam is present the geometry is exactly this.  `Q'` is a `c`-edge of the far-side run with
near end at `X·a = b − b % a`, and `two_vertices_iff` says the seam condition `b % a < e²` is
*equivalent* to `2b < X·a + c`, i.e. to

> the single edge `Q'` contains **two** consecutive near-side vertices in its interior: `V_k` at
> distance `b` and `W' = 2b`, the far end of `R`'s `b`-edge along the chord's extension.

This is the configuration `rem:overrunshape` calls circular by construction: the `c − b = e²`
residue is closed by an edge overrunning its *other* end.  The hope was that the induced overrun is
a strictly smaller instance of the same problem.  It is strictly smaller — `straddle_amount` gives
the overrun past `W'` as exactly

  `X·a + c − 2b = e² − b % a`,  with  `0 < e² − b % a < e² < a`,

so the quantity does drop from `e²` to `e² − b % a`.  **But there is no next term to apply it to.**
`straddle_end_interior`: `e² − b % a < a ≤ L` for every tile side `L`, so the far endpoint of `Q'`
lies *strictly inside* whichever edge follows `W'` — a plain interior T-junction, legal, with no
further overrun.  The recursion stops after one step, in a configuration that is not a crossing.

Two further reasons the same wall is intact, recorded so they are not re-derived:

* `overhang_lt_c` — `x·a + e² < c` at every admissible `x`, so the far end can never straddle an
  `L' = c` edge.  The seam lives **only** in the `L' = b` sub-branch, one of `rem:overrunshape`'s
  two free choices for `R`'s chord-extension edge; the other choice is homogeneous outright.
* Self-similarity fails at the level of hypotheses, not just of quantities.  The enumeration
  `N1GapSubcases.adm_iff` rests on `prefix_all_a`, which needs the far-side run to be **anchored at
  `∂ABC`** so that every partial sum below `V_k` is `< b`.  At `W'` the crossing edge's near end is
  at distance `b + b % a > b` before `W'`, so that hypothesis is consumed at the first step and no
  enumeration is available at the second.  A descent would need a self-similar statement; there is
  none.

**Verdict.**  Negative, and it closes the named route.  The seam is at most one configuration, on
at most a quarter of members, never at `e = 1`, only against `L' = b`, and its induced overrun —
though genuinely smaller — has no successor to descend to.  No sub-configuration is killed, no
Rule 0 label moves.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.N1GapCRange

open Erdos634.N1Gap Erdos634.N1GapSubcases

variable {e f a b c : ℕ}

/-! ## Two arithmetic facts about a separated member -/

/-- Separation forces `f ≥ 3`: at `f ≤ 2` the only candidate is `(e,f) = (1,2)`, where
`2ef + e² = 5 > 4 = f²`. -/
theorem f_ge_three (M : Member e f a b c) : 3 ≤ f := by
  obtain ⟨he, hef, -, -, -, -, hsep⟩ := M
  by_contra h
  have he1 : e = 1 := by omega
  have hf2 : f = 2 := by omega
  subst he1; subst hf2
  omega

/-- `e² < a`: the `c`-overrun is smaller than the shortest tile side.  This is what forces the
`c`-range transition, when it exists at all, to sit at the very last index. -/
theorem e_sq_lt_a (M : Member e f a b c) : e * e < a := by
  obtain ⟨he, hef, -, ha, -, -, -⟩ := M
  subst ha
  nlinarith

/-! ## The transition is sharp: the overhang never lands on `b` -/

/-- **`x·a + e² = b` has no solution.**  Unfolding, `x·ef + 2e² = f²` forces `f ∣ 2e²`, hence
`f ∣ 2` by `gcd(e,f) = 1`, contradicting `f ≥ 3`.

So the `L = c` overhang never equals `b`: the far end of the crossing edge never coincides with
`R`'s far vertex, and the transition from interior T-junction to straddle — where it happens — is
a strict jump with no boundary case in between. -/
theorem overhang_ne_b (M : Member e f a b c) (x : ℕ) : x * a + e * e ≠ b := by
  have hf3 := f_ge_three M
  obtain ⟨he, hef, hco, ha, hb, -, -⟩ := M
  subst ha
  intro h
  have hkey : f * (x * e) + 2 * (e * e) = f * f := by
    rw [← hb, ← h]; ring
  have hfpos : 0 < f := by omega
  have hxef : x * e ≤ f := Nat.le_of_mul_le_mul_left (by omega) hfpos
  obtain ⟨k, hk⟩ : ∃ k, f = x * e + k := ⟨f - x * e, by omega⟩
  have hexp : f * f = f * (x * e) + f * k := by
    have h1 : f * (x * e + k) = f * (x * e) + f * k := by ring
    rw [← hk] at h1; exact h1
  have hfk : 2 * (e * e) = f * k := by omega
  have hcop : Nat.Coprime f (e * e) := (hco.symm).mul_right hco.symm
  have hd : f ∣ 2 := hcop.dvd_of_dvd_mul_right ⟨k, hfk⟩
  have := Nat.le_of_dvd (by norm_num) hd
  omega

/-- The same fact stated on the remainder: `b % a ≠ e²`, so the dichotomy below is genuinely a
dichotomy. -/
theorem mod_ne_e_sq (M : Member e f a b c) : b % a ≠ e * e := by
  have hdm : b % a + a * (b / a) = b := Nat.mod_add_div b a
  have hcomm : (b / a) * a = a * (b / a) := Nat.mul_comm _ _
  have h := overhang_ne_b M (b / a)
  omega

/-! ## Below the top index the range is interior, always -/

/-- `X·a < b` strictly, since `a ∤ b`. -/
theorem top_mul_lt (M : Member e f a b c) : (b / a) * a < b := by
  have hle : (b / a) * a ≤ b := Nat.div_mul_le_self b a
  have hne : (b / a) * a ≠ b := fun h =>
    a_not_dvd_b M ⟨b / a, by rw [Nat.mul_comm]; exact h.symm⟩
  omega

/-- **Every `x` strictly below the top index gives an interior T-junction.**  `x·a + e² < b` for
all `x < ⌊b/a⌋`, because `e² < a` and `(x+1)·a ≤ ⌊b/a⌋·a < b`.  So the `c`-range's type change,
when it occurs, occurs only at the single top index `x = ⌊b/a⌋`. -/
theorem c_below_top (M : Member e f a b c) {x : ℕ} (hx : x < b / a) : x * a + e * e < b := by
  have hea := e_sq_lt_a M
  have hstep : (x + 1) * a ≤ (b / a) * a := Nat.mul_le_mul_right a (by omega)
  have hexp : (x + 1) * a = x * a + a := by ring
  have htop := top_mul_lt M
  linarith

/-- **The seam criterion.**  The top configuration straddles `R`'s `b`-edge iff `b % a < e²`. -/
theorem top_straddle_iff (_M : Member e f a b c) :
    b < (b / a) * a + e * e ↔ b % a < e * e := by
  have hdm : b % a + a * (b / a) = b := Nat.mod_add_div b a
  have hcomm : (b / a) * a = a * (b / a) := Nat.mul_comm _ _
  omega

/-- **The straddle, if any, is at the top index only.** -/
theorem straddle_only_at_top (M : Member e f a b c) {x : ℕ} (hx : x ≤ b / a)
    (h : b < x * a + e * e) : x = b / a := by
  by_contra hne
  have := c_below_top M (lt_of_le_of_ne hx hne)
  omega

/-- **When `e² < b % a`, the whole `c`-range is homogeneous** — every admissible `x` gives a strict
interior T-junction, exactly as on the `L = b` range (`N1GapMastGap.b_range_homogeneous`). -/
theorem c_range_homogeneous_of_mod_ge (M : Member e f a b c) (h : e * e < b % a)
    {x : ℕ} (hx : x ≤ b / a) : x * a + e * e < b := by
  rcases Nat.lt_or_ge x (b / a) with h1 | h1
  · exact c_below_top M h1
  · have hxe : x = b / a := le_antisymm hx h1
    subst hxe
    have h2 : ¬ (b < (b / a) * a + e * e) := fun hc => by
      have := (top_straddle_iff M).mp hc; omega
    have h4 := overhang_ne_b M (b / a)
    omega

/-- **The dichotomy.**  Either the seam exists and is the single configuration `x = ⌊b/a⌋`, or the
`c`-range is homogeneous throughout.  There is no third case (`mod_ne_e_sq`). -/
theorem c_range_dichotomy (M : Member e f a b c) :
    (b % a < e * e ∧ ∀ x, x ≤ b / a → (b < x * a + e * e ↔ x = b / a)) ∨
    (e * e < b % a ∧ ∀ x, x ≤ b / a → x * a + e * e < b) := by
  rcases Nat.lt_or_ge (b % a) (e * e) with h | h
  · refine Or.inl ⟨h, fun x hx => ⟨fun hc => straddle_only_at_top M hx hc, ?_⟩⟩
    rintro rfl; exact (top_straddle_iff M).mpr h
  · have h' : e * e < b % a := lt_of_le_of_ne h (Ne.symm (mod_ne_e_sq M))
    exact Or.inr ⟨h', fun x hx => c_range_homogeneous_of_mod_ge M h' hx⟩

/-! ## The seam only ever meets an `L' = b` edge -/

/-- **The overhang is always below `c`.**  So the far end of the crossing edge can never straddle
an `L' = c` edge of `R`: the seam lives entirely in `rem:overrunshape`'s `L' = b` sub-branch. -/
theorem overhang_lt_c (M : Member e f a b c) {x : ℕ} (hx : x ≤ b / a) : x * a + e * e < c := by
  have hcb : c = b + e * e := by have h1 := M.hb; have h2 := M.hc; omega
  have hle : x * a ≤ (b / a) * a := Nat.mul_le_mul_right a hx
  have := top_mul_lt M
  omega

/-! ## What the seam is, and why it stops -/

/-- **The seam is exactly "one `c`-edge covers two consecutive near-side vertices".**  `Q'` runs
from `X·a` to `X·a + c`; it contains `V_k = b` in its interior always, and it contains
`W' = 2b` — the far end of `R`'s `b`-edge — in its interior **iff** `b % a < e²`, the seam
condition. -/
theorem two_vertices_iff (M : Member e f a b c) :
    ((b / a) * a < b ∧ b < (b / a) * a + c) ∧ (2 * b < (b / a) * a + c ↔ b % a < e * e) := by
  have htop := top_mul_lt M
  have hdm : b % a + a * (b / a) = b := Nat.mod_add_div b a
  have hcomm : (b / a) * a = a * (b / a) := Nat.mul_comm _ _
  have hcb : c = b + e * e := by have h1 := M.hb; have h2 := M.hc; omega
  have hepos : 0 < e * e := Nat.mul_pos M.he M.he
  refine ⟨⟨htop, by omega⟩, ?_⟩
  constructor
  · intro h; omega
  · intro h; omega

/-- **The induced overrun, exactly.**  In the seam configuration the far end of `Q'` passes `W'`
by `X·a + c − 2b = e² − b % a`.  It is positive, strictly smaller than the original overrun `e²`,
and — decisively — strictly smaller than `a`. -/
theorem straddle_amount (M : Member e f a b c) (h : b % a < e * e) :
    (b / a) * a + c - 2 * b = e * e - b % a ∧ 0 < e * e - b % a ∧
      e * e - b % a < e * e ∧ e * e - b % a < a := by
  have hea := e_sq_lt_a M
  have hdm : b % a + a * (b / a) = b := Nat.mod_add_div b a
  have hcomm : (b / a) * a = a * (b / a) := Nat.mul_comm _ _
  have hmodpos : 0 < b % a := by
    rcases Nat.eq_zero_or_pos (b % a) with h0 | h0
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) (a_not_dvd_b M)
    · exact h0
  have hcb : c = b + e * e := by have h1 := M.hb; have h2 := M.hc; omega
  omega

/-- **The chain stops.**  The induced overrun `e² − b % a` is smaller than every tile side, so the
far endpoint of `Q'` is a strict interior T-junction on whichever edge follows `W'` — legal, and
not a crossing.  There is therefore no second term for a descent to act on: the seam's smaller
quantity has nothing to be smaller *than*. -/
theorem straddle_end_interior (M : Member e f a b c) (h : b % a < e * e)
    {L : ℕ} (hL : L = a ∨ L = b ∨ L = c) : e * e - b % a < L := by
  have hea := e_sq_lt_a M
  have hab := M.a_lt_b
  have hbc := M.b_lt_c
  rcases hL with rfl | rfl | rfl <;> omega

/-! ## At `e = 1` the seam does not exist -/

/-- **No seam at `e = 1`.**  There `a = f` and `b = f² − 1`, so `b % a = f − 1 ≥ 2 > 1 = e²`, and
`c_range_homogeneous_of_mod_ge` applies to the whole range.  Since `thm:n1` is proved at `e = 1`,
the seam is absent exactly where the theorem is known — so it cannot be the transported form of the
`e = 1` argument. -/
theorem e_one_no_straddle (M : Member e f a b c) (he1 : e = 1) : e * e < b % a := by
  have hf3 := f_ge_three M
  have hnd := a_not_dvd_b M
  obtain ⟨he, hef, hco, ha, hb, hc, hsep⟩ := M
  subst he1
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have ha1 : a = g + 1 := by rw [ha]; ring
  have hbg : b = g + (g + 1) * g := by
    have h1 : (g + 1) * (g + 1) = g * g + 2 * g + 1 := by ring
    have h2 : (g + 1) * g = g * g + g := by ring
    omega
  have hmod1 : b % a = g := by
    rw [ha1, hbg, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  omega

/-! ## Non-vacuity: both sides of the dichotomy, at `e ≥ 2` -/

/-- The seam side, `(e,f) = (2,5)`: `b % a = 21 % 10 = 1 < 4 = e²`, so the top configuration
`x = X = 2` straddles, the induced overrun is `4 − 1 = 3`, and `3 < 10 = a` — the chain stops.
This is `N1GapMastGap.c_range_type_changes`'s example, now identified as the top-index case. -/
theorem witness_seam_two_five :
    (21 : ℕ) % 10 = 1 ∧ (1 : ℕ) < 2 * 2 ∧
    (21 : ℕ) / 10 * 10 + 25 - 2 * 21 = 3 ∧ (3 : ℕ) < 10 := by norm_num

/-- The homogeneous side at `e ≥ 2`, `(e,f) = (2,9)`, tile `(18, 77, 81)`: separated
(`2·2·9 + 4 = 40 < 81`), `b % a = 77 % 18 = 5 > 4 = e²`.  So this member's `c`-range is *entirely*
interior, exactly like its `b`-range — the seam is not a general feature of `e ≥ 2`. -/
theorem member_witness_two_nine : Member 2 9 18 77 81 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem witness_homogeneous_two_nine :
    (77 : ℕ) % 18 = 5 ∧ (2 * 2 : ℕ) < 5 ∧ ∀ x, x ≤ 77 / 18 → x * 18 + 2 * 2 < 77 := by
  refine ⟨by norm_num, by norm_num, fun x hx => ?_⟩
  exact c_range_homogeneous_of_mod_ge member_witness_two_nine (by norm_num) hx

end Erdos634.N1GapCRange
