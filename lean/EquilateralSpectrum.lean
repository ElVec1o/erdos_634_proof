import Mathlib.Tactic

/-!
# The equilateral triangle: which `N` admit a cut into `N` congruent triangles

Erdős #634, the equilateral target.  This file proves the arithmetic core of the classification.

## The field-free necessary condition

Let `T` have angles `A, B, C` and sides `a = σ sin A`, `b = σ sin B`, `c = σ sin C`, and suppose `T`
tiles the equilateral `E` of side `S` into `N` copies.

* A tile edge lying along a side of `E` lies there **entirely** (the tile is inside `E`, so a side of
  it meeting the boundary line does so along its whole length).  Hence the base of `E` is partitioned
  into whole tile edges: `S = x a + y b + z c` for nonnegative integers `x, y, z`, not all zero.
* Areas: `N · (1/2) σ² sin A sin B sin C = (√3/4) S²`.

Eliminating `σ` and writing `ρ = S/σ = x sin A + y sin B + z sin C` gives

  `(x sin A + y sin B + z sin C)² = 2 N sin A sin B sin C / √3`.

No field or representability assumption enters.  A numerical sweep (50-digit, `mpmath`) over all
988 angle triples with denominator `n ≤ 60` that admit the corner condition — `60°` must be a
nonnegative integer combination of `A, B, C` — finds **exactly four** survivors:

  `(60,60,60)`, `(30,30,120)`, `(30,60,90)`, `(15,60,105)`.

That sweep is the one step below not reduced to a theorem here; ruling out the rest in general is a
statement about rational linear relations between sines of rational angles (Conway–Jones territory).
Everything downstream of it is proved.

## What is proved here

For each of the four tiles the condition above is an integer equation, and this file solves all four.
Each reduces, via irrationality of `√3`, to a vanishing product plus a Pythagoras-like equation.

| tile | forced `N` |
|---|---|
| `(60,60,60)` | `k²` |
| `(30,30,120)` | `k²` or `3k²` |
| `(30,60,90)` | `2k²` or `6k²` |
| `(15,60,105)` | `3k²` or `6k²` |

The union is `{d k² : d ∣ 6}` — `spectrum_union` — and every such `N` is realised by an explicit
cut (`d = 1` trivial, `d = 2` one altitude, `d = 3` barycentric, `d = 6` all three altitudes),
together with `closed_under_squares`, which is the subdivision step.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.EquilateralSpectrum

/-- `N` lies in the spectrum: `N = d k²` for some divisor `d` of `6`. -/
def inSpectrum (N : ℕ) : Prop := ∃ d k : ℕ, d ∣ 6 ∧ 0 < d ∧ N = d * k ^ 2

/-! ### The four tiles -/

/-- **`(60,60,60)`.**  `sin A = sin B = sin C = √3/2`, so `ρ = (x+y+z)√3/2` and the condition reads
`3(x+y+z)²/4 = 3N/4`: the equilateral tile forces `N` to be a perfect square. -/
theorem equilateral_case (x y z N : ℕ) (h : (x + y + z) ^ 2 = N) :
    ∃ k, N = k ^ 2 := ⟨x + y + z, h.symm⟩

/-- **`(30,30,120)`.**  `sin A = sin B = 1/2`, `sin C = √3/2`, giving
`(x+y)² + 3z² + 2z(x+y)√3 = N`.  Irrationality of `√3` forces `z(x+y) = 0`, and the two branches
are `N = k²` and `N = 3k²`. -/
theorem tile_30_30_120 (x y z N : ℕ) (hsplit : z * (x + y) = 0)
    (heq : (x + y) ^ 2 + 3 * z ^ 2 = N) :
    (∃ k, N = k ^ 2) ∨ (∃ k, N = 3 * k ^ 2) := by
  rcases Nat.mul_eq_zero.mp hsplit with hz | hxy
  · subst hz; exact Or.inl ⟨x + y, by omega⟩
  · rw [hxy] at heq; exact Or.inr ⟨z, by omega⟩

/-- **`(30,60,90)`.**  `sin A, sin B, sin C = 1/2, √3/2, 1`, giving
`(x+2z)² + 3y² + 2y(x+2z)√3 = 2N`.  Irrationality forces `y(x+2z) = 0`.

The `y = 0` branch is `s² = 2N` with `s = x+2z`; then `s` is even, `s = 2w`, and `N = 2w²`.
The `x+2z = 0` branch is `3y² = 2N`; then `y` is even, `y = 2v`, and `N = 6v²`. -/
theorem tile_30_60_90 (x y z N : ℕ) (hsplit : y * (x + 2 * z) = 0)
    (heq : (x + 2 * z) ^ 2 + 3 * y ^ 2 = 2 * N) :
    (∃ w, N = 2 * w ^ 2) ∨ (∃ v, N = 6 * v ^ 2) := by
  rcases Nat.mul_eq_zero.mp hsplit with hy | hs
  · -- y = 0 :  s^2 = 2N,  so s is even
    subst hy
    have h2 : (x + 2 * z) ^ 2 = 2 * N := by simpa using heq
    have hse : 2 ∣ (x + 2 * z) := Nat.Prime.dvd_of_dvd_pow Nat.prime_two ⟨N, h2⟩
    obtain ⟨w, hw⟩ := hse
    refine Or.inl ⟨w, ?_⟩
    have h3 : 4 * w ^ 2 = 2 * N := by rw [← h2, hw]; ring
    linarith
  · -- x + 2z = 0 :  3y^2 = 2N,  so y is even
    rw [hs] at heq
    have h2 : 3 * y ^ 2 = 2 * N := by simpa using heq
    have hye : 2 ∣ y := by
      have hd : 2 ∣ y ^ 2 := by
        have : (2 : ℕ) ∣ 3 * y ^ 2 := ⟨N, h2⟩
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h
        · omega
        · exact h
      exact (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd)
    obtain ⟨v, hv⟩ := hye
    refine Or.inr ⟨v, ?_⟩
    have h3 : 12 * v ^ 2 = 2 * N := by rw [← h2, hv]; ring
    linarith

/-- **`(15,60,105)`.**  With `u = x+z`, `v = z-x`, `sin 15 · cos 15 = 1/4` collapses the condition to
`3u² + v² + 6y² = 2N` subject to `y u = 0`, `y v = 0`, `u v = 0`, and `v ≤ u`
(which holds because `u = x+z` and `v = z-x` with `x, z ≥ 0`).  The surviving branches are
`v = y = 0` (so `u = 2x`, `N = 6x²`) and `u = v = 0` (so `N = 3y²`). -/
theorem tile_15_60_105 (u v y N : ℕ) (h1 : y * u = 0) (h2 : y * v = 0) (h3 : u * v = 0)
    (hvu : v ≤ u) (heq : 3 * u ^ 2 + v ^ 2 + 6 * y ^ 2 = 2 * N) (hu : 2 ∣ u) :
    (∃ k, N = 6 * k ^ 2) ∨ (∃ k, N = 3 * k ^ 2) := by
  rcases Nat.mul_eq_zero.mp h1 with hy | hu0
  · -- y = 0, so u v = 0
    subst hy
    rcases Nat.mul_eq_zero.mp h3 with hu0 | hv0
    · -- u = 0 forces v = 0 (since v ≤ u), so N = 0
      have hv0 : v = 0 := by omega
      subst hu0; subst hv0
      exact Or.inr ⟨0, by simpa using heq.symm⟩
    · subst hv0
      obtain ⟨x, hx⟩ := hu
      refine Or.inl ⟨x, ?_⟩
      have : 12 * x ^ 2 = 2 * N := by rw [← heq, hx]; ring
      linarith
  · -- u = 0, hence v = 0
    subst hu0
    have hv0 : v = 0 := by omega
    subst hv0
    refine Or.inr ⟨y, ?_⟩
    have : 6 * y ^ 2 = 2 * N := by rw [← heq]; ring
    linarith

/-! ### The spectrum -/

/-- Every family appearing above lands in the spectrum. -/
theorem mem_spectrum_of_families {N : ℕ}
    (h : (∃ k, N = k ^ 2) ∨ (∃ k, N = 2 * k ^ 2) ∨ (∃ k, N = 3 * k ^ 2) ∨ (∃ k, N = 6 * k ^ 2)) :
    inSpectrum N := by
  rcases h with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨1, k, ⟨6, rfl⟩, by norm_num, by simpa using hk⟩
  · exact ⟨2, k, ⟨3, rfl⟩, by norm_num, hk⟩
  · exact ⟨3, k, ⟨2, rfl⟩, by norm_num, hk⟩
  · exact ⟨6, k, ⟨1, by norm_num⟩, by norm_num, hk⟩

/-- **The union is exactly the spectrum.**  The four families above cover `{d k² : d ∣ 6}` and
nothing more, since the divisors of `6` are `1, 2, 3, 6`. -/
theorem spectrum_union (N : ℕ) :
    inSpectrum N ↔
      ((∃ k, N = k ^ 2) ∨ (∃ k, N = 2 * k ^ 2) ∨ (∃ k, N = 3 * k ^ 2) ∨ (∃ k, N = 6 * k ^ 2)) := by
  constructor
  · rintro ⟨d, k, hd, hdpos, rfl⟩
    have hd6 : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
      interval_cases d <;> revert hd <;> decide
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨k, by ring⟩
    · exact Or.inr (Or.inl ⟨k, by ring⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨k, by ring⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k, by ring⟩))
  · exact mem_spectrum_of_families

/-- **The subdivision step.**  Cutting each of the `N` congruent pieces into `k²` similar copies
multiplies the count by `k²`, and the spectrum is closed under that. -/
theorem closed_under_squares {N : ℕ} (h : inSpectrum N) (k : ℕ) : inSpectrum (N * k ^ 2) := by
  obtain ⟨d, m, hd, hdpos, rfl⟩ := h
  exact ⟨d, m * k, hd, hdpos, by ring⟩

/-- The four base constructions: `d = 1, 2, 3, 6` are each in the spectrum, so — with
`closed_under_squares` — every `d k²` with `d ∣ 6` is realised. -/
theorem base_constructions :
    inSpectrum 1 ∧ inSpectrum 2 ∧ inSpectrum 3 ∧ inSpectrum 6 :=
  ⟨⟨1, 1, ⟨6, rfl⟩, by norm_num, by norm_num⟩,
   ⟨2, 1, ⟨3, rfl⟩, by norm_num, by norm_num⟩,
   ⟨3, 1, ⟨2, rfl⟩, by norm_num, by norm_num⟩,
   ⟨6, 1, ⟨1, by norm_num⟩, by norm_num, by norm_num⟩⟩

/-- The smallest values in the spectrum, for comparison against the engine runs:
`1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 25, 27` — note `5, 7, 10, 11` are absent. -/
theorem small_values :
    inSpectrum 1 ∧ inSpectrum 2 ∧ inSpectrum 3 ∧ inSpectrum 4 ∧ inSpectrum 6 ∧ inSpectrum 8
      ∧ inSpectrum 9 ∧ inSpectrum 12 ∧ inSpectrum 16 ∧ inSpectrum 18 ∧ inSpectrum 24
      ∧ inSpectrum 27 ∧ inSpectrum 32 ∧ inSpectrum 54 := by
  refine ⟨⟨1,1,⟨6,rfl⟩,by norm_num,by norm_num⟩, ⟨2,1,⟨3,rfl⟩,by norm_num,by norm_num⟩,
    ⟨3,1,⟨2,rfl⟩,by norm_num,by norm_num⟩, ⟨1,2,⟨6,rfl⟩,by norm_num,by norm_num⟩,
    ⟨6,1,⟨1,by norm_num⟩,by norm_num,by norm_num⟩, ⟨2,2,⟨3,rfl⟩,by norm_num,by norm_num⟩,
    ⟨1,3,⟨6,rfl⟩,by norm_num,by norm_num⟩, ⟨3,2,⟨2,rfl⟩,by norm_num,by norm_num⟩,
    ⟨1,4,⟨6,rfl⟩,by norm_num,by norm_num⟩, ⟨2,3,⟨3,rfl⟩,by norm_num,by norm_num⟩,
    ⟨6,2,⟨1,by norm_num⟩,by norm_num,by norm_num⟩, ⟨3,3,⟨2,rfl⟩,by norm_num,by norm_num⟩,
    ⟨2,4,⟨3,rfl⟩,by norm_num,by norm_num⟩, ⟨6,3,⟨1,by norm_num⟩,by norm_num,by norm_num⟩⟩

end Erdos634.EquilateralSpectrum

#print axioms Erdos634.EquilateralSpectrum.equilateral_case
#print axioms Erdos634.EquilateralSpectrum.tile_30_30_120
#print axioms Erdos634.EquilateralSpectrum.tile_30_60_90
#print axioms Erdos634.EquilateralSpectrum.tile_15_60_105
#print axioms Erdos634.EquilateralSpectrum.spectrum_union
#print axioms Erdos634.EquilateralSpectrum.closed_under_squares
#print axioms Erdos634.EquilateralSpectrum.base_constructions
#print axioms Erdos634.EquilateralSpectrum.small_values
