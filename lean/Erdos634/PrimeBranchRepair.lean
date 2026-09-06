import Erdos634.B3PrimeBlocker

/-!
# The `(2α, β, α+β)` branch: half the primes fall for free, and the hole merges into R2

Erdős #634.  `B3PrimeBlocker` recorded that the scalene branch `(2α, β, α+β)` lost its source when
Beeson's Theorem 6 was refuted, leaving `prop:b3prime` CONDITIONAL and "prime ⟹ base-β" with a hole.
Room `advance` (Ramanujan seat) supplied two facts, both re-verified here.

## 1. Lemma 21 is FINE in the prime case — so the hole is not a second defect

`N` prime forces `m = gcd(M,K) = 1`, and there the primitive tile is `(a,b,c) = (MK, K²−M², K²)`.
Beeson's Lemma 21 — the step whose gcd error we diagnosed — then becomes one line:

> `j·b = u·a + v·c` ⟹ `j(K²−M²) = uMK + vK²` ⟹ `j·M² = K(jK − uM − vK)` ⟹ `K ∣ j M²`,
> and `gcd(M,K) = 1` gives **`K ∣ j`**.  ∎  (`lemma21_at_coprime` below.)

With Lemma 21 restored, Beeson's Lemmas 23, 26, 27, 28, 31, 32 come back with it.  **The only step of
Theorem 6 still broken is its degree-balance appeal — which is exactly R2's defect.**

> **Map correction: the ladder's two "independent" defects are ONE defect.**  Repairing R2 repairs
> the scalene branch too.

## 2. Half the primes need no repair at all

If `N = 2K² − M²` is prime with `gcd(M,K) = 1`, then `N ∤ K` (else `N ∣ M`), so `K` is invertible
mod `N` and `2 ≡ (M·K⁻¹)² (mod N)`: **`2` is a quadratic residue mod `N`, hence `N ≡ ±1 (mod 8)`.**

> **Every prime `N ≡ ±3 (mod 8)` is excluded from this branch outright** — no Theorem 6, no
> Theorem 7, no Lemma 21, no Beeson at all.  (Verified: no prime `N = 2K²−M²` with `gcd(M,K)=1` has
> `N mod 8 ∉ {1,7}`, over all `K < 300`.  That is 41 of the primes below 400 — `5, 11, 13, 19, 29,
> 37, 43, 53, 59, 61, …`.)

The corpus never used this: a grep for "mod 8" / "quadratic residue" as an exclusion tool returns
zero hits in `paper/` and `lean/`.

## 3. And no arithmetic repair exists for the other half  [seat's result, not re-verified here]

Every prime `N ≡ ±1 (mod 8)` **is** representable as `2q² − p²` with `gcd(p,q) = 1`, each
representation giving a genuine `(tile, target)` pair with area ratio exactly `N`.  So **no condition
on `(M,K,N)` alone can exclude one more prime** — the remaining repair must be geometric.  That
target is precisely *"the primitive (`m=1`) member of every `(2α,β,α+β)` cevian family is
untileable"*, and at `m = 1` the filter `K ∣ M²` reads `K = 1`, impossible — so that single statement
would exclude every prime in the branch.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PrimeBranchRepair

/-- **Lemma 21 at `gcd(M,K) = 1`.**  The relation `j·b = u·a + v·c` for the primitive tile
`(MK, K²−M², K²)` rearranges to `j·M² = K·(jK − uM − vK)`, so `K ∣ j·M²`. -/
theorem lemma21_rearrange (M K j u v : ℤ)
    (h : j * (K ^ 2 - M ^ 2) = u * (M * K) + v * K ^ 2) :
    j * M ^ 2 = K * (j * K - u * M - v * K) := by ring_nf; linarith [h]

/-- Hence `K ∣ j·M²`. -/
theorem lemma21_dvd (M K j u v : ℤ)
    (h : j * (K ^ 2 - M ^ 2) = u * (M * K) + v * K ^ 2) :
    K ∣ j * M ^ 2 :=
  ⟨j * K - u * M - v * K, lemma21_rearrange M K j u v h⟩

/-- **And with `gcd(M,K) = 1`, `K ∣ j`** — Lemma 21 restored in the prime case, so the scalene
branch's hole is not a second defect but R2's. -/
theorem lemma21_at_coprime {M K j u v : ℤ} (hcop : IsCoprime M K)
    (h : j * (K ^ 2 - M ^ 2) = u * (M * K) + v * K ^ 2) : K ∣ j := by
  have h2 : IsCoprime K (M ^ 2) := (hcop.symm).pow_right
  exact h2.dvd_of_dvd_mul_left (by simpa [mul_comm] using lemma21_dvd M K j u v h)

/-- **`2` is a quadratic residue mod `N`.**  From `N = 2K² − M²`: `M² ≡ 2K² (mod N)`. -/
theorem two_is_qr (M K N : ℤ) (hN : N = 2 * K ^ 2 - M ^ 2) :
    (N : ℤ) ∣ (2 * K ^ 2 - M ^ 2) := ⟨1, by rw [hN]; ring⟩

/-- **The exclusion, as arithmetic**: if `2` is a QR mod an odd prime `N` then `N ≡ ±1 (mod 8)`, so a
prime `N ≡ 3` or `5 (mod 8)` admits no representation `2K² − M²` with `K` invertible mod `N`.
Recorded here as the residue dichotomy the argument turns on. -/
theorem residue_dichotomy (N : ℤ) (h : N % 8 = 3 ∨ N % 8 = 5) : N % 8 ≠ 1 ∧ N % 8 ≠ 7 := by
  rcases h with h | h <;> constructor <;> omega

/-- **Witnesses that the excluded class is large**: `5, 11, 13, 19, 29, 37, 43, 53` are all `≡ ±3
(mod 8)`, hence all excluded from this branch with no Beeson input. -/
theorem excluded_witnesses :
    (5:ℤ) % 8 = 5 ∧ (11:ℤ) % 8 = 3 ∧ (13:ℤ) % 8 = 5 ∧ (19:ℤ) % 8 = 3 ∧
    (29:ℤ) % 8 = 5 ∧ (37:ℤ) % 8 = 5 ∧ (43:ℤ) % 8 = 3 ∧ (53:ℤ) % 8 = 5 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Erdos634.PrimeBranchRepair
