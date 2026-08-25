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

## CRUX-2, gated (I1)

The wedge-failing regime is a distinct wall from CRUX-1 and gets its own ledger entry rather than a
reuse of that one.

**Statement.**  Let `1 ≤ e < f`, `gcd(e,f) = 1`, with `e⁴ - 4e²f² + 2f⁴ ≤ 0` (equivalently
`α ≥ π/4`, equivalently `2β ≤ α`).  Supply a replacement for the wedge-filler step: a wedge of angle
exactly `α` need no longer be filled by a single `α`-tile, since two smaller angles now fit.
Determine the admissible fills and re-derive the corner chain from them.

**What it blocks.**  Atom A15 on `1253` of the `4489` primes `≡ 11 (mod 12)` below `200 000`,
`27.9%` of the residue — a strictly larger set than the `e = 1` hole's `51`.

**Smallest instance.**  `(e,f) = (4,5)`, `N = 59`; settled by certified exhaustion, so the smallest
*unsettled* instance is `(5,6)`, `N = 83`, which has absorbed roughly `815` million nodes without
resolving.

**Unblocking criterion.**  The replacement fill lemma at PROVED clears the wall for the whole
regime, since the criterion is uniform in `(e,f)`.

**What is already known, and it is not much.**  The condition is exact and integral
(`Frontier`), the failing pairs are enumerated for `e ≤ 11`, `f ≤ 19`, and every one is a close
pair.  No autopsies: unlike CRUX-1, this wall has no logged dead ends, because it has had almost no
attack.  That is the argument for going at it — and also the reason to expect the standard sweep
(I2) to be required first rather than skipped.

**Not to be confused with `β`-minimality.**  `f < eφ` is a different and wrong criterion; see above.

## TENSION (I12): the wedge condition may be unnecessary, and CRUX-2 may be empty

Nothing is to be built on CRUX-2 until this is resolved, and it is recorded before any further work.

`lem:wallclimb`'s step is: the west fan at `Q_{j-1}` is `β`, `C_j`'s `γ`, and a wedge of exactly
`π - γ - β`, which the branch relations make exactly `α` (`wedge_is_alpha`).  The tiles meeting that
apex inside the wedge each have a vertex there, so their angles sum to exactly `α`, and a fill is a
solution of the integer system `n_α + 2n_γ = 1`, `n_β + n_γ = 0`.  That system has the single
solution `(1,0,0)` (`wedge_fill_unique`), by nothing more than `α/β` irrational
(`BaseBetaE1.tile_alpha_irrational`).

So the fill is forced at **every** member.  The parenthetical "(`α` is the minimal angle)" in the
proof is redundant, and `Frontier`'s replacement — that what the step needs is `α < π/4` — appears
to be redundant too, since neither is used in deriving the unique solution.

If that is right then the wedge step is safe everywhere, the `27.9%` regime is not blocked at all,
and CRUX-2 as gated above is empty.  The alternative is that some *other* part of `lem:wallclimb`
consumes the condition — the proof also excludes the reflected partner "by the wedge's `α`", and
that step is not the fill — in which case `Frontier`'s claim is right but attached to the wrong
sentence.

Either way one of the two must be corrected.  **The condition has not been shown to be needed, and
CRUX-2's gate is suspended pending resolution.**  Resolving it is worth more than attacking it: one
outcome unblocks `1253` primes.
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


/-- **The wedge is exactly `α`.**  `π - γ - β = α` for the branch relations `γ = 2α + β` and
`3α + 2β = π`. -/
theorem wedge_is_alpha (a b g p : ℝ) (hg : g = 2*a + b) (hp : p = 3*a + 2*b) :
    p - g - b = a := by rw [hg, hp]; ring

/-- **The exact fill of a wedge of angle `α` is unique**, and the proof uses only the integer
system: `n_α + 2n_γ = 1` and `n_β + n_γ = 0`, which come from `α/β` irrational
(`BaseBetaE1.tile_alpha_irrational`).  No minimality of `α`, and no `α < π/4`. -/
theorem wedge_fill_unique (na nb ng : ℕ) (h1 : na + 2 * ng = 1) (h2 : nb + ng = 0) :
    na = 1 ∧ nb = 0 ∧ ng = 0 := by omega

/-- The same for the neighbouring wedges the chain meets, so the phenomenon is not special to `α`. -/
theorem wedge_fill_unique_two_alpha (na nb ng : ℕ) (h1 : na + 2 * ng = 2) (h2 : nb + ng = 0) :
    na = 2 ∧ nb = 0 ∧ ng = 0 := by omega

end Erdos634.PrimeRegimes
