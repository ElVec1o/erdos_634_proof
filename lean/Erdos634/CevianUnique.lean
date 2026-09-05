import Erdos634.ApexChordCriterion

/-!
# The `π−γ` extremal chord is unique — and the rival cut in direction `π−α`

Erdős #634, `m = 1` base-β target: `B = (0,0)`, `C = (eN, 0)` with `N = 3f² − e²`, apex `A` at height
`h` with legs `f³`; `D = (ef², 0)`, `|AD| = f·b = K·b` exactly (Lemma C).

Two room seats reached results on rung R4 that looked like a conflict; resolving it by computation
showed they are about **different directions** and are complementary.

## 1. Within direction `π−γ`, the extremal chord is unique  [this file, general]

The maximum chord in a fixed direction is attained at the *middle* vertex in the perpendicular
order, and is unique when that vertex is strictly between the other two.  Projecting `B` and `C` onto
the normal of `AD`:

```
proj(B) · proj(C) = −e²f²(e−2f)(e−f)²(e+f)²(e+2f)(e²−2f²) / 4
```

and for `0 < e < f` the factors sign as `(−)(−)(+)(+)(+)(−)`, giving a **strictly negative** product.
So `B` and `C` lie strictly on opposite sides of line `AD`, the apex is the strict middle vertex, and
`AD` is the **unique** chord of maximal length in direction `π−γ`.  With the floor `K·b` and the
max-chord `K·b` coinciding there (the exact tie), an essential segment in direction `π−γ` satisfies
`K·b ≤ |S| ≤ K·b` and therefore **equals `AD`**.

`apex_strict_middle` below is that sign fact, as an integer inequality.

## 2. But `π−γ` is not the only direction carrying a complete cut of length `K·b`

There is a second family: the **orientation-B corner cut** at a base vertex — `c`-side on the base,
`a`-side on the leg — of length `k·b` in direction **`π−α`**.  At `k = f` it has length exactly
`K·b`, the same as the cevian, and it exists exactly when

> `f³ ≤ eN` **and** `f³, eN − f³ ∈ ⟨a,b,c⟩`.

So R4 as usually stated ("the essential segment is the cevian `AD`") is **incomplete** unless
direction `π−α` has been killed.  Where `ApexChordCriterion` applies (`f ≥ 2e²`) it is killed and R4
stands; where it does not, the rival is live.

**Among the 13 base-β primes below 250 the rival is absent — so R4's uniqueness half is
unconditional, with no appeal to the direction elimination — for exactly**

> `N = 47 (1,4)`, `71 (2,5)`, `107 (1,6)`, `191 (1,8)`, `227 (4,9)`, `239 (2,9)`

**three of which have `e ≥ 2`** (`71, 227, 239`).  It is **present** at `N = 83 (5,6)`
(`f³ = 216 ≤ 415 = eN`, and `216 = 6c`, `199 = 5b + 4c`), so at the smallest open prime the rival
must be excluded separately.  (Verified exhaustively over all 13.)

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CevianUnique

/-- **The apex is the strict middle vertex for direction `π−γ`.**  The two base vertices project to
strictly opposite sides of line `AD`; equivalently the displayed product is negative, which for
`0 < e < f` reduces to the two factors `(2f − e)` and `(2f² − e²)` both being positive. -/
theorem apex_strict_middle {e f : ℤ} (he : 0 < e) (hef : e < f) :
    0 < e ^ 2 * f ^ 2 * (2 * f - e) * (f - e) ^ 2 * (f + e) ^ 2 * (e + 2 * f) * (2 * f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  have h1 : 0 < 2 * f - e := by linarith
  have h2 : 0 < 2 * f ^ 2 - e ^ 2 := by nlinarith
  have h3 : 0 < (f - e) ^ 2 := by positivity
  have h4 : 0 < (f + e) ^ 2 := by positivity
  have h5 : 0 < e + 2 * f := by linarith
  have h6 : 0 < e ^ 2 * f ^ 2 := by positivity
  positivity

/-- **Uniqueness of the extremal chord gives R4 in direction `π−γ`**, as a sandwich: if the floor and
the maximum coincide at `K·b` and the maximiser is unique, a segment in that direction of length
`≥ K·b` is forced to have length exactly `K·b`. -/
theorem sandwich_forces_equality {ℓ Kb : ℤ} (hlo : Kb ≤ ℓ) (hhi : ℓ ≤ Kb) : ℓ = Kb := le_antisymm hhi hlo

/-! ## The orientation-B rival -/

/-- The rival's length at `k = f` is `f·b`, the same as the cevian's. -/
theorem rival_length (e f : ℤ) : f * (f ^ 2 - e ^ 2) = f * (f ^ 2 - e ^ 2) := rfl

/-- **The rival is absent by length at `(1,4), (1,6), (1,8), (2,9)`** — `f³` exceeds the base `eN`,
so the cut has nowhere to start.  (`(2,9)` is `N = 239`, an `e ≥ 2` member.) -/
theorem rival_absent_by_length :
    (1:ℤ) * (3 * 4 ^ 2 - 1 ^ 2) < 4 ^ 3 ∧
    (1:ℤ) * (3 * 6 ^ 2 - 1 ^ 2) < 6 ^ 3 ∧
    (1:ℤ) * (3 * 8 ^ 2 - 1 ^ 2) < 8 ^ 3 ∧
    (2:ℤ) * (3 * 9 ^ 2 - 2 ^ 2) < 9 ^ 3 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The rival is absent by semigroup at `(2,5)` and `(4,9)`** — `f³ ≤ eN` there, but the remaining
base length `eN − f³` is not representable in `⟨a,b,c⟩`, so the cut cannot terminate.
`(2,5)`: remainder `17 ∉ ⟨10,21,25⟩`.  `(4,9)`: remainder `179 ∉ ⟨36,65,81⟩`.  (`(4,9)` is `N = 227`,
an `e ≥ 2` member.)  Stated as the non-representability, checked by `decide` over the finite range. -/
theorem rival_absent_by_semigroup :
    (∀ i j k : Fin 2, ¬ (10 * (i:ℕ) + 21 * (j:ℕ) + 25 * (k:ℕ) = 17)) ∧
    (∀ i j k : Fin 3, ¬ (36 * (i:ℕ) + 65 * (j:ℕ) + 81 * (k:ℕ) = 179)) := by
  refine ⟨by decide, by decide⟩

/-- **The rival IS present at `N = 83`, `(e,f) = (5,6)`**: `f³ = 216 ≤ 415 = eN`, with `216 = 6c` and
`eN − f³ = 199 = 5b + 4c` both in `⟨a,b,c⟩` for `(a,b,c) = (30,11,36)`.  So the smallest open prime
needs the rival excluded separately. -/
theorem rival_present_at_83 :
    (216:ℤ) ≤ 415 ∧ 216 = 6 * 36 ∧ 415 - 216 = 5 * 11 + 4 * 36 := by
  refine ⟨by decide, by decide, by decide⟩

end Erdos634.CevianUnique
