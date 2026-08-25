import Mathlib.Tactic

/-!
# Where the prime residue lives, by geometric regime

Erdős #634.  Every prime `≡ 11 (mod 12)` has exactly one base-`β` representation `p = 3f² - e²`
(`ThinHole.rep_unique`), so the residue partitions with no overlap.

The partition that matters is by the **wedge-filler condition**, not by which angle is smallest.
Several corner-chain steps fill a wedge of angle exactly `α` with a single `α`-tile.  `lem:wallclimb`
justifies this by "`α` is the minimal angle", but `Frontier` records that this is *not* the
load-bearing fact: what is needed is that no two smaller angles fit, `2β > α`, which with
`3α + 2β = π` reads `α < π/4`.  Since `cos α = 1 - e²/(2f²)`, that is the integer criterion

  **`e⁴ - 4e²f² + 2f⁴ > 0`.**

The two conditions genuinely disagree.  At `(3,4)` one has `b < a`, so `β` is minimal, yet
`α < π/4` holds and the step survives.  An earlier version of this file partitioned by
`β`-minimality (`f < eφ`) and reported the blocked regime as `43.5%`; that was the wrong criterion
and the wrong number.

## The census

`code/analysis/regime_census.py`, over the `4489` primes `≡ 11 (mod 12)` below `200 000`:

```
  e = 1 (the hole)           51   ( 1.1%)   11, 47, 107, 191
  separated, wedge ok      1609   (35.8%)   71, 239, 347, 359
  close, wedge ok          1576   (35.1%)   23, 131, 167, 227
  WEDGE CONDITION FAILS    1253   (27.9%)   59, 83, 179, 263
```

So `27.9%` of the residue is beyond the corner-chain machinery, and `N = 83`, the smallest prime not
settled unconditionally, sits there.  `N = 23` does not: it is a close pair on which the wedge step
survives, which is consistent with its having been settled.  `N = 59` does fail the condition and was
settled by certified exhaustion anyway, so the regime obstructs the argument, not the search.

Every failing pair is a close pair.  Enumerating `e ≤ 11`, `f ≤ 19`, `gcd(e,f) = 1`, the condition
fails exactly at

  `(4,5) (5,6) (6,7) (7,8) (7,9) (8,9) (9,10) (9,11) (10,11) (10,13) (11,12) (11,13) (11,14)`.

`Frontier`'s list of the same range omits `(11,14)`, where
`11⁴ - 4·11²·14² + 2·14⁴ = 14641 - 94864 + 76832 = -3391 < 0`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PrimeRegimes

/-- **The wedge-filler condition, as an integer criterion.**  `α < π/4` iff `2f² - e² > √2 f²`;
squaring (both sides positive since `f > e`) gives `e⁴ - 4e²f² + 2f⁴ > 0`. -/
def WedgeOK (e f : ℤ) : Prop := e ^ 4 - 4 * e ^ 2 * f ^ 2 + 2 * f ^ 4 > 0

/-- **`β`-minimality is not the criterion.**  At `(3,4)` the tile has `b < a`, so `β` is the minimal
angle, yet the wedge condition holds and the step survives. -/
theorem three_four_beta_minimal_but_ok :
    ((4:ℤ) ^ 2 - 3 ^ 2 < 3 * 4) ∧ WedgeOK 3 4 := by
  refine ⟨by norm_num, ?_⟩
  unfold WedgeOK; norm_num

/-- **`(5,6)` is `N = 83` and the wedge condition fails there.** -/
theorem eightythree_wedge_fails : 3 * 6 ^ 2 - 5 ^ 2 = 83 ∧ ¬ WedgeOK 5 6 := by
  refine ⟨by norm_num, ?_⟩
  unfold WedgeOK; norm_num

/-- **`(2,3)` is `N = 23`, a close pair on which the wedge condition SURVIVES.**  So the failing set
is not simply the close pairs. -/
theorem twentythree_close_but_ok :
    3 * 3 ^ 2 - 2 ^ 2 = 23 ∧ ((3:ℤ) ^ 2 ≤ 2 * 2 * 3 + 2 ^ 2) ∧ WedgeOK 2 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold WedgeOK; norm_num

/-- **`(11,14)`, omitted from `Frontier`'s enumeration, does fail.** -/
theorem eleven_fourteen_fails : ¬ WedgeOK 11 14 := by
  unfold WedgeOK; norm_num

end Erdos634.PrimeRegimes
