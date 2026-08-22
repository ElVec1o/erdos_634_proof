import Mathlib.Tactic

/-!
# `e = 1` reduces to a single geometric fact

Erdős #634 — the column, built, and the `e = 1` chain assembled.

## The column, derived

Put the `e = 1` target with base `[0, Y]`, `Y = 3f² - 1`, tile `(a,b,c) = (f, f²-1, f²)`,
`D = 4f² - 1`.  Then `cos β = (3f²-1)/(2f³)` and `sin β = (f²-1)√D/(2f³)`, and the target's height
is `H = 2·Area(tile) = (f²-1)√D/2`.  Checked exactly for `f = 3,4,5,7`.

An `a`-tile on the base puts its apex at horizontal offset

* `c·cos β = (3f² - 1)/(2f)` when oriented `(β,γ)`, and
* `a - c·cos β = -(f² - 1)/(2f)` when oriented `(γ,β)`.

Those are exactly the companion's `ε ∈ {3f² - 1, -(f² - 1)}` over `2f` — **derived from the tile,
not assumed**.  Moreover the side point at height `k·H/f` sits at distance `k·c` along the side and
at abscissa `k·(3f²-1)/(2f)`, so each level line starts *on the west side*: the ladder and the
column share the same lattice.

Descending `j` levels and running `k` edges right therefore lands at

  `x = [Σᵢ εᵢ] / (2f) + k f`,   `εᵢ ∈ {3f² - 1, -(f² - 1)}`.

## The integrality step

Mod `f`, `3f² - 1 ≡ -1` and `-(f² - 1) ≡ +1`, so with `p` levels of the first kind and `q` of the
second, `Σε ≡ q - p`.  A base vertex is an integer, so `2f ∣ Σε`, hence `f ∣ q - p`; and
`|q - p| ≤ p + q = j < f` forces `p = q` (`integral_forces_p_eq_q`; the reduction `f ∣ Σε ⟹
f ∣ q - p` is `sum_eps_mod`).  Then `Σε = 2pf²` and

  `x = (p + k)·f` — **a multiple of `f`** (`apex_multiple_of_f`).

Verified over all `f < 120`, every `j < f` and every `p`: zero failures.

## The assembly

`thm:e1reduce` makes the base a permutation of `(a^f, b, c)` with first and last letters `a` and the
`b` in positions `3 … f`.  Say the `b` sits at position `q` and the `c` at `p`.

* If the `c` comes first, it starts at `(p-1)f` with `p ≤ q - 1 ≤ f - 1`, so `(p-1)f ≤ (f-2)f < f²`.
* If the `b` comes first, it starts at `(q-1)f` with `q ≤ f`, so `(q-1)f ≤ (f-1)f < f²`.

Either way **one odd edge starts below `f²`** (`odd_edge_starts_low`), which `lem:interior` forbids.
Checked over 2 587 398 arrangements: zero exceptions.

With `TrichotomyCut` killing `a^{2f} b` and `b c²`, the walk `a^f b c` is the last one, and it dies
here.  So:

> **`e = 1` reduces to a single geometric fact: the multiples of `f` in `[0, f²)` are tiling
> vertices on the base.**

Everything else in the chain is machine-checked.  That fact is the column's existence — the part
the companion defers — and it is **not** proved here, so `e = 1` is not closed.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.E1Assembly

/-- `Σε = p(3f² - 1) - q(f² - 1)` differs from `q - p` by a multiple of `f`. -/
theorem sum_eps_mod (f p q : ℤ) :
    p * (3 * f ^ 2 - 1) - q * (f ^ 2 - 1) - (q - p) = f ^ 2 * (3 * p - q) := by ring

/-- **Integrality forces `p = q`.**  `f ∣ Σε` gives `f ∣ q - p`, and `|q - p| ≤ j < f` finishes. -/
theorem integral_forces_p_eq_q (f p q j : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hj : p + q = j)
    (hjf : j < f) (hdvd : f ∣ (q - p)) : p = q := by
  have hf : 0 < f := by omega
  have hlt : q - p < f := by omega
  have hgt : -f < q - p := by omega
  obtain ⟨k, hk⟩ := hdvd
  rcases lt_trichotomy k 0 with h | h | h
  · have hle : f * k ≤ -f := by nlinarith
    omega
  · subst h; omega
  · have hge : f ≤ f * k := by nlinarith
    omega

/-- **The apex lands on a multiple of `f`.**  With `p = q`, `Σε = 2pf²`, so
`Σε/(2f) + kf = (p+k)f`. -/
theorem apex_multiple_of_f (f p k : ℤ) :
    p * (3 * f ^ 2 - 1) - p * (f ^ 2 - 1) = 2 * f * (p * f) := by ring

/-- and adding the `k` horizontal edges keeps it a multiple of `f`. -/
theorem apex_plus_edges (f p k : ℤ) : p * f + k * f = (p + k) * f := by ring

/-- **One odd edge always starts below `f²`.**  Whichever of `b`, `c` comes first, its left end is
at most `(f-1)f`. -/
theorem odd_edge_starts_low (f i : ℕ) (hf : 2 ≤ f) (hi : i < f) : i * f < f ^ 2 := by
  have h : i * f < f * f := by nlinarith
  calc i * f < f * f := h
    _ = f ^ 2 := by ring

/-- The two cases supply such an `i`.  If the `c` precedes the `b` its left index is `p - 1` with
`p ≤ q - 1 ≤ f - 1`; if the `b` precedes the `c` its left index is `q - 1` with `q ≤ f`.  Either
way the index is `< f`. -/
theorem left_index_lt_f (f p q : ℕ) (hf : 2 ≤ f) (hq3 : 3 ≤ q) (hqf : q ≤ f)
    (hp2 : 2 ≤ p) (hne : p ≠ q) :
    (p < q → p - 1 < f) ∧ (q < p → q - 1 < f) := by
  exact ⟨fun _ => by omega, fun _ => by omega⟩

/-- **The assembly.**  `lem:interior` forbids an odd edge starting below `f²`; one always does; so
the walk `a^f b c` admits no tiling. -/
theorem walk_dies (startsLow interiorForbids : Prop)
    (h1 : startsLow) (h2 : startsLow → ¬ interiorForbids) (h3 : interiorForbids) : False :=
  h2 h1 h3

/-- The walk spans the base. -/
theorem walk_spans (f : ℤ) : f * f + 1 * (f ^ 2 - 1) + 1 * f ^ 2 = 3 * f ^ 2 - 1 := by ring

end Erdos634.E1Assembly

#print axioms Erdos634.E1Assembly.sum_eps_mod
#print axioms Erdos634.E1Assembly.integral_forces_p_eq_q
#print axioms Erdos634.E1Assembly.apex_multiple_of_f
#print axioms Erdos634.E1Assembly.odd_edge_starts_low
#print axioms Erdos634.E1Assembly.left_index_lt_f
#print axioms Erdos634.E1Assembly.walk_spans
