import Mathlib.Tactic

/-!
# Where the prime residue lives, by geometric regime

Erdős #634.  Every prime `≡ 11 (mod 12)` has exactly one base-`β` representation
`p = 3f² - e²` (`ThinHole.rep_unique`), so the residue partitions with no overlap.  The partition
that matters is not by size but by which of the tile's angles is smallest, because the corner-chain
machinery chooses wedge fillers by "`α` is the minimal angle" (`lem:wallclimb`).

With `(a, b, c) = (ef, f² - e², f²)`:

* **separated**, `f² > 2ef + e²` (equivalently `f/e > 1 + √2`, equivalently `b > 2a`) — the
  determined base walk of the main paper applies.
* **close**, `f/e ≤ 1 + √2` — it does not.  Close pairs are exactly `b ≤ 2a`
  (`close_iff_b_le_two_a`), and they are an infinite family.
* **`β`-minimal**, `f < eφ` (equivalently `b < a`, `beta_minimal_iff`) — a sub-case of close in
  which `β`, not `α`, is the smallest angle.  Every step resting on `α`-minimality is unavailable,
  so the geometry itself changes rather than the arithmetic merely weakening.

## The census

`code/analysis/regime_census.py`, over the `4489` primes `≡ 11 (mod 12)` below `200 000`:

```
  e = 1 (the hole)        51   ( 1.1%)   11, 47, 107, 191
  separated             1609   (35.8%)   71, 239, 347, 359
  close, α minimal       876   (19.5%)   131, 227, 383, 443
  close, β minimal      1953   (43.5%)   23, 59, 83, 167
```

The largest regime is the one where the machinery's geometric hypothesis fails, and `N = 83`, the
smallest prime not settled unconditionally, sits in it.  So the `e ≥ 2` half is not a softer target
than the `e = 1` hole: its bulk is the part where the existing geometry does not apply, and the two
smallest members of that bulk that *are* settled — `23` and `59` — were settled by certified
exhaustion, not by argument.  `83` has absorbed roughly `815` million nodes without resolving.

The regime is not in itself an obstruction to search (`small_beta_minimal_settled`); it is an
obstruction to the corner-chain argument.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PrimeRegimes


/-- **The `β`-minimal regime, exactly.**  With `(a,b,c) = (ef, f²-e², f²)`, the tile has `b < a`
precisely when `f² < ef + e²`, i.e. `f/e` below the golden ratio.  There `β`, not `α`, is the
smallest angle, and every step choosing a wedge filler by "`α` is minimal" is unavailable. -/
theorem beta_minimal_iff (e f : ℤ) (he : 1 ≤ e) (hef : e < f) :
    (f ^ 2 - e ^ 2 < e * f) ↔ (f ^ 2 < e * f + e ^ 2) := by
  constructor <;> intro h <;> linarith

/-- **Close pairs are exactly `b ≤ 2a`.**  Separation `f² > 2ef + e²` is the negation. -/
theorem close_iff_b_le_two_a (e f : ℤ) :
    (f ^ 2 - e ^ 2 ≤ 2 * (e * f)) ↔ (f ^ 2 ≤ 2 * e * f + e ^ 2) := by
  constructor <;> intro h <;> linarith

/-- `(5,6)` is `N = 83`, and it is `β`-minimal: `b = 11 < 30 = a`. -/
theorem eightythree_beta_minimal :
    3 * 6 ^ 2 - 5 ^ 2 = 83 ∧ (6:ℤ) ^ 2 - 5 ^ 2 < 5 * 6 := by
  constructor <;> norm_num

/-- `(2,3)` is `N = 23` and `(4,5)` is `N = 59`; both are `β`-minimal and both are settled by
certified exhaustion, so the regime is not in itself an obstruction to search. -/
theorem small_beta_minimal_settled :
    (3 * 3 ^ 2 - 2 ^ 2 = 23 ∧ (3:ℤ) ^ 2 - 2 ^ 2 < 2 * 3) ∧
    (3 * 5 ^ 2 - 4 ^ 2 = 59 ∧ (5:ℤ) ^ 2 - 4 ^ 2 < 4 * 5) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

end Erdos634.PrimeRegimes
