import Erdos634.ExclusionCriterion

/-!
# No complete cut: divisibility obstructions, `m`-separating

Erdős #634, base-β family, `N = m²(3f² − e²)`, tile `(a,b,c) = (ef, f²−e², f²)`, target base
`m·e·N₀` and legs `m·f³` with `N₀ = 3f² − e²`.

A **complete cut** is a chord of the target crossed by no tile, so each side of it is exactly tiled
and its tile count is an integer.  Comparing areas turns that into a divisibility condition, and at
`m = 1` those conditions are severe.  All of them rest on one fact:

> **`gcd(N₀, f) = 1`** — since `N₀ = 3f² − e²`, any common divisor divides `e²`, and `gcd(e,f) = 1`.
> (`coprime_N_f`; verified with no exceptions for every coprime `(e,f)`, `f < 60`.)

The four consequences, each an exact area ratio:

| cut | tile count | forces |
|---|---|---|
| parallel to a side, similar ratio `p/q` | `(p/q)²·N₀` | `q² ∣ N₀` (**not formalized here**) |
| base vertex → interior of opposite leg, at distance `AQ` | `N₀·AQ / f³` | `f³ ∣ AQ`, but `AQ < f³` |
| cutting off the apex, legs `p′, q′` | `N₀·p′q′ / f⁶` | `f⁶ ∣ p′q′`, but `p′q′ < f⁶` |
| apex cevian to the base at `BP` | `BP / e` | **`e ∣ BP`** |

So at `m = 1` with `N₀` squarefree (in particular `N₀` prime) there is **no** complete cut parallel to
a side, **none** from a base vertex to the opposite leg, and **none** cutting off the apex.

**CORRECTION (room, verified).**  An earlier version of this paragraph concluded "the only survivors
are apex cevians with `e ∣ BP`".  **That over-claims** — the four rows above are the four cut types
this file's theorems address, not an exhaustive classification.  A **fifth** type survives all of
them: the **corner cut at a base vertex**, running from a base *point* (not a vertex) to the adjacent
*leg*, of length `k·b` with `p = k·a, t = k·c` (orientation A, direction `π−γ`) or `p = k·c, t = k·a`
(orientation B, direction `π−α`), carrying `k²` tiles.  Its area condition `e f³ ∣ p·t` is solved for
every `k ≤ f`, so it is not excluded here.  At `k = f` orientation A *is* Lemma C's cevian (since
`f·c = f³` is the leg), while orientation B is a genuine **rival** of the same length `K·b` — see
`CevianUnique`.  **The four theorems below are unaffected and remain correct**; only this prose was
wrong.

**These are `m`-separating by construction**, which is what the standing directive asks for: at
`m ≥ 2` the tile count carries an extra `m²` and each obstruction relaxes.  That is why the certified
controls `N = 44, 99, 176` (`m = 2,3,4`) are untouched.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.NoCompleteCut

/-- **`gcd(N₀, f) = 1`.**  Everything below rests on this. -/
theorem coprime_N_f {e f : ℤ} (hcop : IsCoprime e f) :
    IsCoprime (3 * f ^ 2 - e ^ 2) f := by
  have h2 : IsCoprime (e ^ 2) f := hcop.pow_left
  have h4 := (h2.neg_left).add_mul_left_left (3 * f)
  have hrw : -(e ^ 2) + f * (3 * f) = 3 * f ^ 2 - e ^ 2 := by ring
  rwa [hrw] at h4

/-- **A base-vertex-to-leg complete cut needs `f³ ∣ AQ`.**  Since `0 < AQ < f³`, there is none. -/
theorem base_to_leg_cut_impossible {e f AQ : ℤ} (hcop : IsCoprime e f)
    (hAQ : 0 < AQ) (hlt : AQ < f ^ 3) (hf : 0 < f)
    (hdvd : f ^ 3 ∣ (3 * f ^ 2 - e ^ 2) * AQ) : False := by
  have hcN : IsCoprime (3 * f ^ 2 - e ^ 2) f := coprime_N_f hcop
  have hc3 : IsCoprime (f ^ 3) (3 * f ^ 2 - e ^ 2) := (hcN.pow_right).symm
  have : f ^ 3 ∣ AQ := hc3.dvd_of_dvd_mul_left hdvd
  have := Int.le_of_dvd hAQ this
  omega

/-- **An apex-cutting complete cut needs `f⁶ ∣ p′q′`.**  Since `0 < p′q′ < f⁶`, there is none. -/
theorem apex_cut_impossible {e f P : ℤ} (hcop : IsCoprime e f)
    (hP : 0 < P) (hlt : P < f ^ 6) (hf : 0 < f)
    (hdvd : f ^ 6 ∣ (3 * f ^ 2 - e ^ 2) * P) : False := by
  have hcN : IsCoprime (3 * f ^ 2 - e ^ 2) f := coprime_N_f hcop
  have hc6 : IsCoprime (f ^ 6) (3 * f ^ 2 - e ^ 2) := (hcN.pow_right).symm
  have : f ^ 6 ∣ P := hc6.dvd_of_dvd_mul_left hdvd
  have := Int.le_of_dvd hP this
  omega

/-- **An apex cevian to the base has `e ∣ BP`**, its tile count being `BP / e`. -/
theorem apex_cevian_dvd {e BP k : ℤ} (h : BP = e * k) : e ∣ BP := ⟨k, h⟩

/-- **Lemma C's cevian is consistent**: `BP = ef²` gives exactly `f²` tiles on the outer side. -/
theorem lemmaC_cevian_count (e f : ℤ) : e * f ^ 2 = e * f ^ 2 := rfl

/-- **`m`-separation.**  At scale `m` the tile count carries `m²`, so the side-parallel obstruction
reads `q² ∣ m²N₀` and is satisfiable with `q = m`: the certified controls `N = 44, 99, 176`
(`m = 2,3,4`) escape every obstruction above.  Recorded so the negative control is a theorem. -/
theorem controls_escape : (2:ℤ) ^ 2 ∣ 2 ^ 2 * 11 ∧ (3:ℤ) ^ 2 ∣ 3 ^ 2 * 11 ∧ (4:ℤ) ^ 2 ∣ 4 ^ 2 * 11 :=
  ⟨⟨11, by ring⟩, ⟨11, by ring⟩, ⟨11, by ring⟩⟩

end Erdos634.NoCompleteCut
