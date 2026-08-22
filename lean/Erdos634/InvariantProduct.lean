import Mathlib.Tactic

/-!
# The product of the two signed-direction invariants

For a `2π/3` tile `(a,b,c)` with `c² = a² + ab + b²` and a target of one of the eleven admissible
shapes, the two invariants of the main paper,

  `M_α = Φ_{f_α}(∂ABC) / (c+a-b)`,   `M_β = Φ_{f_β}(∂ABC) / (c+b-a)`,

are both integers (Corollary `cor:int`).  Their *product* turns out to be a fixed rational multiple
of the tile count `N` on every shape, the multiplier depending only on the shape:

| shape                      | `M_α M_β / N`              |
|----------------------------|----------------------------|
| equilateral                | `3`                        |
| tile-similar               | `1`                        |
| `F₁` and its reflection    | `1`                        |
| `F₂`                       | `3ab/((a+2b)(2a+b))`       |
| iso base-`α`, `F₃`, `F₄'`  | `-a/(a+2b)`                |
| iso base-`β`, `F₄`, `F₃'`  | `-b/(2a+b)`                |

This file machine-checks the arithmetic of the two entries that equal `N` on the nose, and the
number-theoretic step they feed.  The multiplier table itself is a symbolic computation over
`ℚ(a,b,c,√3)` (`code/verify_shapes.py`); the identities below are its load-bearing consequences.

Two consequences, both **citation-free** — in particular neither uses the Beeson–Zhang rationality
theorem, which is the single most load-bearing unrefereed input of the main theorem:

* **tile-similar target**: `N = M_α²`, so `N` is a perfect square and never prime;
* **`F₁` target**: `M_α M_β = N`, so a prime `N` forces `M_α = ±1` and pins the tile ratio to
  `a/c = (N-1)/(N+1)`; `N² + 14N + 1` is then forced to be a perfect square, which fails for every
  `N > 6`.  So on `F₁` a prime count forces an *irrational* tile, which the boundary-walk argument
  of the paper then kills outright.

Nothing here touches the open base-`β` branch of `3α+2β=π`; that is a different branch with a
different tile, and this file says nothing about it.

`#print axioms` is checked after each theorem.
-/

namespace Erdos634.InvariantProduct

/-- The `F₁` numerator identity: `(2a+b)² - c² = 3a(a+b)` for a `120°`-triple. -/
theorem F1_num (a b c : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (2 * a + b - c) * (2 * a + b + c) = 3 * a * (a + b) := by
  linear_combination -hc

/-- The universal denominator identity: `(c+a-b)(c+b-a) = 3ab`. -/
theorem XY_eq (a b c : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c + a - b) * (c + b - a) = 3 * (a * b) := by
  linear_combination hc

/-- `M_α` in closed form on the `F₁` target: `M_α · b = k(c-a)`. -/
theorem F1_Ma (a b c k Ma : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (ha : a ≠ 0)
    (hMa : Ma * (c + a - b) = k * (2 * a + b - c)) :
    Ma * b = k * (c - a) := by
  have h3a : (3 : ℤ) * a ≠ 0 := by simpa using ha
  refine mul_left_cancel₀ h3a ?_
  have e1 : (3 * a) * (Ma * b) = Ma * ((c + a - b) * (c + b - a)) := by
    rw [XY_eq a b c hc]; ring
  have e2 : (3 * a) * (k * (c - a)) = k * ((2 * a + b - c) * (c + b - a)) := by
    linear_combination k * hc
  rw [e1, e2, ← mul_assoc, hMa, mul_assoc]

/-- `M_β` in closed form on the `F₁` target: `M_β · b = k(c+a)`. -/
theorem F1_Mb (a b c k Mb : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (ha : a ≠ 0)
    (hMb : Mb * (c + b - a) = k * (2 * a + b + c)) :
    Mb * b = k * (c + a) := by
  have h3a : (3 : ℤ) * a ≠ 0 := by simpa using ha
  refine mul_left_cancel₀ h3a ?_
  have e1 : (3 * a) * (Mb * b) = Mb * ((c + b - a) * (c + a - b)) := by
    rw [show (c + b - a) * (c + a - b) = (c + a - b) * (c + b - a) by ring, XY_eq a b c hc]; ring
  have e2 : (3 * a) * (k * (c + a)) = k * ((2 * a + b + c) * (c + a - b)) := by
    linear_combination (-k) * hc
  rw [e1, e2, ← mul_assoc, hMb, mul_assoc]

/-- **The `F₁` product theorem.**  On the `F₁` target the two invariant counts multiply to the tile
count: `M_α M_β = N`.  Hypotheses are exactly the paper's: the `120°`-relation, the area equation
`N b = k²(a+b)`, and the two integrality equations defining `M_α`, `M_β`. -/
theorem F1_product (a b c k N Ma Mb : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hN : N * b = k ^ 2 * (a + b))
    (hMa : Ma * (c + a - b) = k * (2 * a + b - c))
    (hMb : Mb * (c + b - a) = k * (2 * a + b + c)) :
    Ma * Mb = N := by
  have e1 := F1_Ma a b c k Ma hc ha hMa
  have e2 := F1_Mb a b c k Mb hc ha hMb
  have key : (Ma * Mb) * (b * b) = N * (b * b) :=
    calc (Ma * Mb) * (b * b) = (Ma * b) * (Mb * b) := by ring
      _ = (k * (c - a)) * (k * (c + a)) := by rw [e1, e2]
      _ = k ^ 2 * (a + b) * b := by linear_combination (k ^ 2) * hc
      _ = (N * b) * b := by rw [hN]
      _ = N * (b * b) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hb hb) key

/-- The ratio consequence: `M_β (c-a) = M_α (c+a)`. -/
theorem F1_ratio (a b c k Ma Mb : ℤ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hMa : Ma * (c + a - b) = k * (2 * a + b - c))
    (hMb : Mb * (c + b - a) = k * (2 * a + b + c)) :
    Mb * (c - a) = Ma * (c + a) := by
  have e1 := F1_Ma a b c k Ma hc ha hMa
  have e2 := F1_Mb a b c k Mb hc ha hMb
  refine mul_right_cancel₀ hb ?_
  calc Mb * (c - a) * b = (Mb * b) * (c - a) := by ring
    _ = (k * (c + a)) * (c - a) := by rw [e2]
    _ = (k * (c - a)) * (c + a) := by ring
    _ = (Ma * b) * (c + a) := by rw [e1]
    _ = Ma * (c + a) * b := by ring

/-- With `M_α = 1` and `M_β = N` the tile ratio is pinned: `c(N-1) = a(N+1)`. -/
theorem F1_pin (a c N : ℤ) (h : N * (c - a) = 1 * (c + a)) : c * (N - 1) = a * (N + 1) := by
  linear_combination h

/-- The discriminant that rationality of the tile would require is never a square beyond `N = 6`:
`N² + 14N + 1 = q²` has no solution with `N > 6`.  (Equivalently `(N+7)² - q² = 48`.) -/
theorem disc_not_square (N q : ℤ) (hN : 6 < N) : N ^ 2 + 14 * N + 1 ≠ q ^ 2 := by
  intro h
  obtain ⟨r, habs, hq⟩ : ∃ r : ℤ, 0 ≤ r ∧ N ^ 2 + 14 * N + 1 = r ^ 2 :=
    ⟨|q|, abs_nonneg q, by rw [h, sq_abs]⟩
  -- r < N + 7, since (N+7)^2 = N^2 + 14N + 49 exceeds r^2 = N^2 + 14N + 1
  have hlt : r < N + 7 := by nlinarith
  -- for N ≥ 18 we would also have r > N + 6, leaving no integer room
  have hbig : N ≤ 17 := by
    by_contra hcon
    push_neg at hcon
    have h1 : N + 6 < r := by nlinarith
    omega
  -- 7 ≤ N ≤ 17 and 0 ≤ r ≤ 23: finitely many pairs, all refuted numerically
  have hr23 : r ≤ 23 := by omega
  interval_cases N <;> interval_cases r <;> omega

#print axioms F1_num
#print axioms XY_eq
#print axioms F1_Ma
#print axioms F1_Mb
#print axioms F1_product
#print axioms F1_ratio
#print axioms F1_pin
#print axioms disc_not_square

/-- **Tile-similar target.**  If `ABC` is similar to the tile at ratio `μ`, then
`Φ_{f_α}(∂ABC) = ±μ(c+a-b)` by the tile-value lemma applied to `ABC` itself, so `M_α = ±μ`, while
the area identity gives `N = μ²`.  Hence `N = M_α²` is a perfect square — and in particular never
prime.  No rationality input is used. -/
theorem tile_similar_not_prime (N Ma : ℤ) (hN : N = Ma ^ 2) : ¬ Prime N :=
  fun hp => hp.irreducible.not_isSquare ⟨Ma, by rw [hN]; ring⟩

#print axioms tile_similar_not_prime

end Erdos634.InvariantProduct
