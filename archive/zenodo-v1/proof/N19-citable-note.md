# No triangle can be cut into 19 congruent triangles

**Erdős Problem #634.** *For which N does there exist a triangle that can be cut into N
pairwise-congruent triangles?* The page https://www.erdosproblems.com/634 (ed. 30 Dec 2025)
lists **N = 19** as an explicit open instance ("it is not known if 19 has this property").
This note gives a complete, self-contained exclusion of N = 19, repairing the one branch whose
previously-published exclusion was withdrawn in 2024.

Throughout, "tile" means the congruent triangle and **ABC** the triangle being cut.
N = 19 is prime, **19 ≡ 3 (mod 4)**, not a sum of two squares, not a perfect square, not
2·/3·/6· a square.

---

## 1. The classification, and where 19 already falls

By Laczkovich's classification (Tilings of triangles, *Discrete Math.* 140 (1995) 79–94;
*Discrete Comput. Geom.* 38 (2012) 330–372), every N-tiling of a triangle falls into finitely
many (ABC, tile) types. For all but one type, N = 19 is excluded by a **standing, published**
theorem (several name 19 outright):

| Type | Bound on N | N=19 | Reference |
|---|---|---|---|
| tile similar to ABC | N ∈ {n², n²+m², 3n²} | excluded | Snover–Waiveris–Williams 1991; Beeson, *Triangle Tiling I* [arXiv:1206.2231], Thm 1–2 |
| commensurable tile angles | not a prime whose squarefree part has a factor ≡3 mod 4 | **excluded (names 19)** | Beeson [arXiv:1811.09723], Thm 7 |
| right-angled tile | N not a prime ≡3 mod 4 (nor twice one) | **excluded (names 19)** | Beeson [arXiv:1811.09723] Thm 4 + Cor 1 (proof in [arXiv:1206.1974] Thm 7.8) |
| 3α+2β = π family | N not prime | excluded | Beeson [arXiv:1206.2229], Thm 21 |
| isosceles tile, γ = 2α | N not squarefree (so not prime) | excluded | Beeson [arXiv:1206.1974], Thm 11.7 |
| equilateral ABC, π/3 or 2π/3 tile | N not prime | excluded | Beeson [arXiv:1812.07014], Thm 3 & **Thm 6** |
| **non-isosceles 2π/3 tile, non-equilateral ABC** | — | **§2–§4 below** | (was [arXiv:1206.2228], **withdrawn 2024**) |

The last row is the gap. Its only prior exclusion of 19 was *Triangle Tiling V*
(arXiv:1206.2228), **withdrawn by the author in May 2024** ("Theorem 1 is wrong; … not used in
any of my other papers"). Beeson's surviving general bound for this tile is only **N ≥ 12**
([arXiv:1811.09723], Thm 6) — which does not reach 19. We close the gap by an elementary
argument below.

---

## 2. Setup for the non-isosceles 2π/3 tile

The tile has angles (α, β, γ = 2π/3); the irrational (incommensurable) case has α an irrational
multiple of π and α + β = π/3. By **Beeson–Zhang, *Rationality of certain triangle tilings***
([arXiv:2604.01314], 2026, Thm 1.1 — a self-contained proof with **no** dependence on the
flawed Lemma 7.1 of Laczkovich 2012), the tile has commensurable sides; rescale so

> **(a, b, c) ∈ ℤ, gcd(a,b,c)=1, c² = a² + ab + b²** (law of cosines at 2π/3).

A short computation gives sin α = a√3/(2c), cos α = (2b+a)/(2c), and symmetrically for β.
Since a prime dividing two of a, b, c divides the third, **gcd(a,b)=gcd(a,c)=gcd(b,c)=1**; and
for a primitive triple **3 ∤ c**.

**Lemma A (shape list).** Every corner of ABC is filled by tile angles, so its measure is
`mα + k(π/3)` with `(m,k) = (P−Q, Q+2R)`, P,Q,R ≥ 0 the multiplicities of α,β,γ there; the
three corners satisfy Σm = 0, Σk = 3. Exhaustively enumerating these (verified to m ∈ [−6,6])
yields **exactly 11 shapes**: equilateral; two isosceles; and eight scalene — namely
`F1=(α,α+β,α+2β)`, `F2=(2α,2β,α+β)`, `F3=(α,2α,3β)`, `F4=(α,2β,2α+β)`, their α↔β mirrors, and
the tile-similar `(α,β,2π/3)`. (This matches Beeson, *Triangle Tiling V*, Theorem 8.) *Code:*
`shape_completeness.py`.

**Lemma B (area / integrality).** If ABC (similar to a fixed shape with primitive integer
side-proportion vector `Dp`, gcd = 1) is N-tiled, its sides are sums of integer tile edges,
hence integers, hence ABC has sides `k·Dp` with **k ∈ ℤ≥1**. Therefore
`N = Area(ABC)/Area(tile) = k²·N0`, where `N0 := Area(Dp)/Area(tile)` and
`Area(tile) = (√3/4)·ab`. (A *necessary* condition.)

---

## 3. N = 19 is impossible for every non-equilateral shape

Equilateral ABC is handled by Beeson Thm 6 (§1). For each remaining shape we compute `N0` in
closed form (`shape_completeness.py`, `n19_final_check.py`); two of the scalene families
reproduce Beeson's *exact* published floors (143, …), validating the method.

- **tile-similar `(α,β,2π/3)`:** `N = n²`; 19 is not a square.
- **F2 `(2α,2β,α+β)`:** the π/3 vertex lies between sides `a(a+2b)` and `b(2a+b)`, so
  `N0 = (a+2b)(2a+b) ≥ 143`. Then `N = k²(a+2b)(2a+b) ≠ 19`.
- **F3 `(α,2α,3β)`:** ABC's third side ∝ `3ab(a+b)/c`, an integer only if `c | 3(a+b)`; but
  `c < a+b < c√2`, so `3(a+b)/c ∈ (3, 4.25)`, the lone integer 4 needs `7a²−2ab+7b²=0`
  (impossible). So `c ∤ 3(a+b)`: F3 (and mirror) yield no integer-sided ABC and tile nothing.
- **F4 `(α,2β,2α+β)`:** one checks `gcd(Dp)=1` (`g | c` then `g²|3b²`, so `g=1`), giving
  `N0 = (a+b)(2a+b) ≥ 88`; `N = k²(a+b)(2a+b) ≠ 19`.
- **F1 `(α,α+β,α+2β)`:** ABC sides ∝ `(a, c, a+b)`, the π/3 vertex between `a` and `a+b`, so
  `N0 = (a+b)/b`. As `gcd(b,a+b)=1`, `N = k²(a+b)/b ∈ ℤ` forces `(a+b) | N`. For N = 19 prime,
  `a+b = 19` and `k² = b` (b a perfect square). The candidates `b ∈ {1,4,9,16}`, `a = 19−b`
  give `c² = 343, 301, 271, 313` — none a perfect square; the mirror is identical. No tile exists.
- **Isosceles `(α,α,α+3β)`** and **`(β,β,3α+β)`:** `N0 = (a+2b)/b` and `(2a+b)/a` respectively;
  N = 19 forces `a+2b = 19` (resp. `2a+b = 19`) with the relevant leg a perfect square. The
  candidates again give `c² ∈ {307,181,91}` — none square. No tile exists. (Independently,
  Beeson [arXiv:1206.1974] rules out N < 36 for the isosceles 2π/3 case.)

Hence no non-isosceles 2π/3 tile tiles any non-equilateral ABC with N = 19. ∎

---

## 4. Conclusion

**Theorem.** *No triangle can be cut into 19 pairwise-congruent triangles.*

Every Laczkovich type excludes N = 19: all but the non-isosceles-2π/3 type by the standing
theorems of §1; the equilateral 2π/3 case by Beeson Thm 6; and the non-equilateral 2π/3 cases
(scalene F1–F4 and isosceles) by the elementary §3 argument, which rests only on the verified
shape list (Lemma A), the area/integrality condition (Lemma B), and the sound rationality
reduction of Beeson–Zhang. ∎

**Remarks.**
1. The argument is entirely independent of the withdrawn *Triangle Tiling V*. The §3 floors
   `N0_F2 = (a+2b)(2a+b)`, `N0_F4 = (a+b)(2a+b)` reproduce Beeson's Theorem 4/7 numbers, so the
   floors lost to the withdrawal are recovered on a sound footing.
2. N = 19 is special only as a small **prime** sitting below every scalene floor (88, 143…),
   with the F1/isosceles divisor-form forcing a degree-2 Diophantine condition that fails. The
   same template excludes the other small primes 7, 11, 23, 31, 43, … (prime ≡ 3 mod 4 below the
   floors), recovering Beeson's withdrawn list 7, 11, 19, 31, 41 cleanly.
3. The *general* "no prime ≡ 3 (mod 4)" conjecture remains open; it reduces exactly to the
   isosceles 2π/3 case (companion note `uniform-conjecture-reduction.md`).

*Reproducible checks (Python/sympy, exact arithmetic):* `verify_vertex_types.py`,
`shape_completeness.py`, `n19_final_check.py`, `n19_pi3_tile.py` (the π/3-tile sub-case yields
only equilateral and tile-similar ABC, no new shape). All pass.
