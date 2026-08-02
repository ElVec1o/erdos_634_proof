import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# The accumulated-offset forcing, both parities of `f` (Erdős #634, W2 pillar 3 / W-B5)

`W2Core.lean` proves this per member and **only for `f` even**, as `sum_forcing_*`. Its header states
the mechanism: mod `2f`, the two step-offsets `−(f²−1)` and `3f²−1` are `+1` and `−1`, and then
"for `j < f` and `|s| ≤ j`, `2f ∣ (s − j)` implies `s = j`". The restriction to even `f` is real:
`f² ≡ 0 (mod 2f)` holds only when `f` is even, and for odd `f` the two residues are `f+1` and `f−1`
instead, so the even-`f` computation does not transfer. This is the gap logged as **W-B5** (odd-`f`
`e = 1` appendix), which `thm:e1family` avoids by assuming `f` even while `thm:basebeta-full` claims
every coprime `(e,f)`.

## The observation that closes it

Work modulo `f` rather than `2f`. There, `−(f²−1) ≡ 1` and `3f²−1 ≡ −1` for **every** `f`, with no
parity hypothesis, since `f² ≡ 0 (mod f)`.

Now parametrise the accumulated offset honestly. Over `j` levels let `p` be the number of `+1` steps
and `q` the number of `−1` steps, so

    j = p + q,      s = p − q,      s − j = −2q .

The forcing hypothesis `f ∣ (s − j)` is therefore exactly `f ∣ 2q`, and the conclusion `s = j` is
exactly `q = 0`. Stated this way no parity check is needed anywhere: it is absorbed into the
parametrisation, because `s − j` is visibly even.

* `f` odd: `f ∣ 2q` and `gcd(f,2) = 1` give `f ∣ q`, and `q ≤ j < f` forces `q = 0`.
* `f` even: the available hypothesis is the stronger `2f ∣ (s − j)`, i.e. `2f ∣ 2q`, i.e. `f ∣ q`,
  and again `q = 0`.

Both parities land on `f ∣ q` and finish identically. The even case is recovered, the odd case is
new, and the per-member `sum_forcing_*` theorems of `W2Core.lean` are subsumed.
-/

namespace Erdos634.OffsetForcing

variable {f p q : ℕ}

/-- The shared core: `f ∣ q` together with `p + q < f` forces `q = 0`. -/
theorem q_eq_zero_of_dvd (hlt : p + q < f) (hdvd : f ∣ q) : q = 0 := by
  rcases Nat.eq_zero_or_pos q with h | h
  · exact h
  · exact absurd (Nat.le_of_dvd h hdvd) (by omega)

/-- **Odd `f`.** Every step took the `+1` branch. -/
theorem forcing_odd (hodd : ¬ 2 ∣ f) (hlt : p + q < f) (hdvd : f ∣ 2 * q) : q = 0 := by
  have hcop : Nat.Coprime f 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm
  exact q_eq_zero_of_dvd hlt (hcop.dvd_of_dvd_mul_left hdvd)

/-- **Even `f`.** Same conclusion from the stronger hypothesis `2f ∣ 2q` available there. -/
theorem forcing_even (hlt : p + q < f) (hdvd : 2 * f ∣ 2 * q) : q = 0 := by
  refine q_eq_zero_of_dvd hlt ?_
  obtain ⟨k, hk⟩ := hdvd
  have hk' : 2 * q = 2 * (f * k) := by rw [hk]; ring
  exact ⟨k, by omega⟩

/-- **Both parities.** The accumulated offset over `j = p + q` levels is `s = p − q`; the forcing
hypothesis is `f ∣ (j − s) = 2q` for odd `f` and `2f ∣ (j − s)` for even `f`. Either way `s = j`. -/
theorem forcing (hlt : p + q < f)
    (hdvd : (¬ 2 ∣ f ∧ f ∣ 2 * q) ∨ (2 * f ∣ 2 * q)) : q = 0 := by
  rcases hdvd with ⟨hodd, h⟩ | h
  · exact forcing_odd hodd hlt h
  · exact forcing_even hlt h

end Erdos634.OffsetForcing
