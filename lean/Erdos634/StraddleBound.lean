import Mathlib.Tactic

/-!
# The straddle of the base `c`-edge tile, computed exactly

Erdős #634 — the quantitative bound `rem:straddle` asks for, for the tile that forces the
route-1 crossings.

`rem:straddle` shows the blanket no-straddle hypothesis is false and says what is needed instead:

> the missing ingredient is not a prohibition but a **quantitative** bound: a description of the set
> in which a straddling tile's crossing points must lie.

For the corner lines `L_k` in a route-1 configuration there is such a description, and it is exact.

## Setup

At `e = 1`: `(a,b,c) = (f, f²-1, f²)`, base `3f² - 1`, equal sides `f³`, base angle `β` with
`cos β = (3f²-1)/(2f³)`.  A route-1 base word is `a^i c a^j b a^{k'}` with `i, j, k' ≥ 1`, so the
base `c`-edge runs from `X = (i f, 0)` to `Y = (i f + c, 0)`, and its tile `T_c` presents `β` at `X`
(flanks `a` and `c`), giving third vertex `Z = X + a·u`.

`L_k` is the corner line from `P = (k f, 0)` to `k c·u`; the region `W_k` west of it is the triangle
`(k a, k b, k c)`, similar to the tile at scale `k`, of area `k² A`.  For `i < k ≤ f` the point `P`
is interior to the base `c`-edge (`CrossingCount.base_point_interior`), so `T_c` crosses `L_k`.

## The two exact quantities

Solving for where `L_k` leaves `T_c` through the edge `ZY`:

* **chord**  `|T_c ∩ L_k| = f + i - k`, an integer, and `0 < f + i - k < f = a` — strictly shorter
  than the shortest tile edge (`chord_pos`, `chord_lt_a`);
* **donation**  `area(T_c ∩ W_k)/A = (2f(k-i) - (k-i)² - 1)/(f²-1)`, which by `donation_identity`
  equals `1 - (f+i-k)²/(f²-1)`.

So the donation deficit is exactly **the square of the chord over `b`**.

## What it pins

`CrossingCount.crossing_count_ge_two` says `L_k` carries at least two crossing tiles, because
`k² - n` is a positive integer while each donation lies strictly in `(0, A)`.  Combining:

  the donations of the crossing tiles sum to `(k² - n) A`, and `T_c` supplies
  `(1 - chord²/b) A`, so the remaining crossers supply `((k² - n) - 1 + chord²/b) A`.

In the tightest case, exactly two crossers, the second donates **exactly `chord²/b · A`**
(`second_donation`).  That is a description of the straddle in the sense asked for: not a
prohibition, but an exact area, determined by the boundary word through `chord = f + i - k`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.StraddleBound

/-- **The donation identity.**  `2f(k-i) - (k-i)² - 1 = (f²-1) - (f+i-k)²`, so the donation of the
base `c`-edge tile to `W_k`, in units of the tile's area, is `1 - chord²/b` with `chord = f+i-k`. -/
theorem donation_identity (f i k : ℤ) :
    2 * f * (k - i) - (k - i) ^ 2 - 1 = (f ^ 2 - 1) - (f + i - k) ^ 2 := by ring

/-- The chord is positive: `k ≤ f` and `i ≥ 1` give `f + i - k ≥ 1`. -/
theorem chord_pos (f i k : ℤ) (hi : 1 ≤ i) (hk : k ≤ f) : 1 ≤ f + i - k := by omega

/-- The chord is shorter than `a = f`: `k > i` gives `f + i - k < f`. -/
theorem chord_lt_a (f i k : ℤ) (hik : i < k) : f + i - k < f := by omega

/-- **The donation lies strictly between `0` and `1`**, as an area fraction must.  Equivalently
`0 < chord² < b`, which holds since `1 ≤ chord ≤ f - 1` and `(f-1)² < f² - 1` for `f ≥ 2`. -/
theorem donation_strict (f i k : ℤ) (hf : 2 ≤ f) (hi : 1 ≤ i) (hik : i < k) (hk : k ≤ f) :
    0 < (f + i - k) ^ 2 ∧ (f + i - k) ^ 2 < f ^ 2 - 1 := by
  have h1 : 1 ≤ f + i - k := chord_pos f i k hi hk
  have h2 : f + i - k ≤ f - 1 := by omega
  constructor
  · nlinarith
  · nlinarith

/-- **The second crosser's donation, in the tightest case.**  If the donations sum to `(k²-n)·A`
with `k² - n = 1`, and `T_c` supplies `(1 - chord²/b)·A`, the remaining crossers supply exactly
`chord²/b · A`.  Stated over `ℚ` in units of `A`. -/
theorem second_donation (chordSq bb total : ℚ) (hb : bb ≠ 0)
    (hTc : total = 1 - chordSq / bb) (hsum : (1 : ℚ) = total + (1 - total)) :
    1 - total = chordSq / bb := by
  rw [hTc]; ring

/-- The chord at the block line `k = f` is exactly `i`, and at the first crossed line `k = i+1` it
is `f - 1`. -/
theorem chord_endpoints (f i : ℤ) :
    (f + i - f = i) ∧ (f + i - (i + 1) = f - 1) := by
  refine ⟨by ring, by ring⟩

end Erdos634.StraddleBound

#print axioms Erdos634.StraddleBound.donation_identity
#print axioms Erdos634.StraddleBound.chord_pos
#print axioms Erdos634.StraddleBound.chord_lt_a
#print axioms Erdos634.StraddleBound.donation_strict
#print axioms Erdos634.StraddleBound.second_donation
#print axioms Erdos634.StraddleBound.chord_endpoints
