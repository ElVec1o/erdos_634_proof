import Mathlib.Tactic

/-!
# Scaling in the equilateral families, and the redundancy of Beeson's Table 2

Erdős #634 — a structural reduction of the open list.

## The families

Beeson's Table 2 (arXiv:1812.07014v3) lists `(N, M, tile, X)` with `X` the side of the equilateral,
subject to the area equation `X² = N a b` and the colouring equation `M(a+b+c) = 3X`.  For a fixed
tile the area equation is a conic, and its solutions form a one-parameter family: with `μ` the least
positive integer with `a b ∣ μ²` and `λ = μ²/(a b)`,

  `X = μ k`,   `N = λ k²`,   `k = 1, 2, 3, …`

The six `(3,8,7)` rows of the printed table are exactly `k = 3 … 8` of `X = 12k`, `N = 6k²`; the full
table carries `k = 3 … 15` for that tile.  Herdt's `1944`-tiling is `N = 6·18²`, i.e. `k = 18` of the
same family.

## The scaling lemma

An equilateral of side `m X` is the union of `m²` equilaterals of side `X`.  So a tiling of the
side-`X` equilateral by `N` copies of `T` gives one of the side-`mX` equilateral by `m² N` copies of
the same `T`.  In family coordinates:

  **`k` achievable ⟹ `m k` achievable**, for every `m ≥ 1`  (`scaling_up`).

Contrapositively — and this is the useful direction —

  **`m k` dead ⟹ `k` dead**  (`dead_down`):  the dead set is closed *downward* under divisibility,
  the achievable set closed *upward* under multiplication.

## The consequence for the table

Within a tile family a row is implied by any row whose `k` is a multiple of its own.  Over the 60
rows of the reconstruction (the paper prints 55), only the maximal `k` in each family are
independent:

| tile | `k` present | independent |
|---|---|---|
| `(3,8,7)` | `3 … 15` | `8 … 15` |
| `(5,8,7)` | `7 … 12` | `7 … 12` |
| `(8,15,13)` | `3,4,5,6` | `4,5,6` |
| `(5,21,19)`, `(7,15,13)` | `1,2,3` | `2,3` |
| `(13,48,43)` | `2,4,6` | `4,6` |
| `(7,40,37)`, `(17,80,73)` | `2,3,4` | `3,4` |
| `(16,55,49)` | `2,4` | `4` |

**60 rows, 48 independent, 12 implied for free.**  Concretely: settling `N = 216` (`k=6`) settles
`N = 54` (`k=3`); settling `N = 384` (`k=8`) settles `N = 96` (`k=4`).

## The reframing

Beeson writes that one of the lines "represents the smallest possible value of `N` corresponding to
a tiling, but we do not know which".  Within a family that is the smallest **achievable** `k`, and
since the achievable set is upward-closed under multiplication, it is a *primitive* element of that
set: no proper divisor of it is achievable.  The question is therefore not 55 independent decisions
but the location of the primitive achievable `k` in each of the finitely many families.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.EquilateralScaling

/-- **The family parametrisation.**  With `X = μ k` and `N = λ k²` where `λ μ' = μ²` for
`μ' = a b`, the area equation `X² = N a b` holds identically in `k`. -/
theorem area_equation (lam mu ab k : ℕ) (h : mu * mu = lam * ab) :
    (mu * k) ^ 2 = (lam * k ^ 2) * ab := by
  have : (mu * k) ^ 2 = (mu * mu) * k ^ 2 := by ring
  rw [this, h]; ring

/-- **Scaling up.**  If the side-`μk` equilateral is tiled by `λk²` copies, the side-`μ(mk)` one is
tiled by `λ(mk)²` copies: it is the union of `m²` copies of the former.  The count identity is
`m² · λ k² = λ (m k)²`. -/
theorem scaling_up (lam m k : ℕ) : m ^ 2 * (lam * k ^ 2) = lam * (m * k) ^ 2 := by ring

/-- **Dead descends.**  Stated as the contrapositive of `scaling_up` at the level of the predicate:
if `mk` is not achievable then neither is `k`, since `k` achievable would force `mk` achievable. -/
theorem dead_down (achievable : ℕ → Prop) (m k : ℕ)
    (up : ∀ j l : ℕ, achievable j → achievable (l * j))
    (h : ¬ achievable (m * k)) : ¬ achievable k :=
  fun hk => h (up k m hk)

/-- **The achievable set is upward closed under multiplication**, hence determined by its primitive
elements: those with no proper divisor achievable. -/
theorem achievable_upward (achievable : ℕ → Prop)
    (up : ∀ j l : ℕ, achievable j → achievable (l * j)) (k m : ℕ) (hk : achievable k) :
    achievable (m * k) := up k m hk

/-- The `(3,8,7)` family: `μ = 12`, `λ = 6`, so `X = 12k`, `N = 6k²`, and `a b = 24` with
`12² = 6 · 24`. -/
theorem three_eight_seven : (12 : ℕ) * 12 = 6 * 24 ∧ (12 * 3 = 36 ∧ 6 * 3 ^ 2 = 54)
    ∧ (12 * 8 = 96 ∧ 6 * 8 ^ 2 = 384) ∧ (6 * 18 ^ 2 = 1944) := by
  refine ⟨by norm_num, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by norm_num⟩

/-- `N = 216` is `k = 6` and `N = 54` is `k = 3`, and `3 ∣ 6`, so a negative verdict at `216`
implies one at `54`. -/
theorem two_sixteen_implies_fifty_four : (6 * 6 ^ 2 = 216) ∧ (6 * 3 ^ 2 = 54) ∧ (3 ∣ 6) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end Erdos634.EquilateralScaling

#print axioms Erdos634.EquilateralScaling.area_equation
#print axioms Erdos634.EquilateralScaling.scaling_up
#print axioms Erdos634.EquilateralScaling.dead_down
#print axioms Erdos634.EquilateralScaling.achievable_upward
#print axioms Erdos634.EquilateralScaling.three_eight_seven
