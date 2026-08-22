import Mathlib.Tactic

/-!
"No prime `N` when `ABC` is isosceles with base angles `α+β`" (the `3α+2β=π` branch) — a **correct**
arithmetic replacement for Beeson III, Theorem 18, whose printed proof is unsound.

Beeson's Theorem 18 argues mod `N` that `c²b ≡ M⁴(M²+1)`, forcing `N = M²+1`.  Under his own
scaling `a = N−M²`, `c = N+M²`, `b = c − a²/c` one has `bc = c²−a² = 4NM²` and hence
`c²b = 4NM²(N+M²) ≡ 0 (mod N)` identically — no primality used — so the residue `M⁴(M²+1)` is wrong
(a dropped factor of `a`), the "`N = M²+1`" step is vacuous, and Theorem 18 as printed proves nothing.

The conclusion is nonetheless **true**, via the base-length obstruction Beeson's own program actually
checks (Lemmas 6, 42, 45(iii) + Theorem 17).  For prime `N` and coloring number `M` with `M² < N`,
let `d = gcd(N−M², N+M²)`; then `d ∣ 2`, the reduced tile is `a = g·â`, `c = g²`, `b = g²−â²` with
`g = (N+M²)/d`, `â = (N−M²)/d`, and the base side has integer length `Y = M·â·(g+â)`.  A tiling
forces the base to carry `≥ g−M` edges of length `b` and `≥ 2` edges of length `c` (Lemmas 6, 45(iii)),
so `Y ≥ (g−M)b + 2c`.  But `d ∣ 2` gives `â + M ≤ g`, whence the identity
`(g−M)(g²−â²) − M·â·(g+â) = g(g+â)(g−â−M) ≥ 0` yields `Y ≤ (g−M)b < (g−M)b + 2c` — contradiction.

This file machine-checks the two arithmetic pillars (`d ∣ 2` and the obstruction inequality),
axiom-clean.  The geometric bridge (a tiling ⟹ `Y ≥ (g−M)b + 2c`) is Beeson's refereed covering
lemmas, cited, not formalized.
-/

namespace Erdos634.BaseAlphaBeta

/-- Number-theoretic pillar: for a prime `N` and `1 ≤ M` with `M² < N`, the gcd of the difference
and sum `N ∓ M²` divides `2`.  (`d ∣ 2N`, `d ∣ 2M²`, and `gcd(N, M²) = 1` since `N ∤ M²`.) -/
theorem gcd_dvd_two (N M : ℕ) (hN : N.Prime) (hM : 1 ≤ M) (hM2 : M ^ 2 < N) :
    Nat.gcd (N - M ^ 2) (N + M ^ 2) ∣ 2 := by
  set d := Nat.gcd (N - M ^ 2) (N + M ^ 2) with hd
  have h1 : d ∣ N - M ^ 2 := Nat.gcd_dvd_left _ _
  have h2 : d ∣ N + M ^ 2 := Nat.gcd_dvd_right _ _
  have hsum : d ∣ 2 * N := by
    have he : (N + M ^ 2) + (N - M ^ 2) = 2 * N := by omega
    have := Nat.dvd_add h2 h1; rwa [he] at this
  have hdiff : d ∣ 2 * M ^ 2 := by
    have h3 : (N - M ^ 2) + 2 * M ^ 2 = N + M ^ 2 := by omega
    have h2' : d ∣ (N - M ^ 2) + 2 * M ^ 2 := by rw [h3]; exact h2
    exact (Nat.dvd_add_right h1).mp h2'
  have hnd : ¬ N ∣ M ^ 2 := by
    intro h
    have hNM : N ∣ M := hN.dvd_of_dvd_pow h
    have : N ≤ M := Nat.le_of_dvd hM hNM
    nlinarith [hM2, this]
  have hcop : Nat.gcd N (M ^ 2) = 1 := (hN.coprime_iff_not_dvd.mpr hnd)
  have hg : d ∣ Nat.gcd (2 * N) (2 * M ^ 2) := Nat.dvd_gcd hsum hdiff
  rwa [Nat.gcd_mul_left, hcop, Nat.mul_one] at hg

/-- Geometric-arithmetic pillar (over `ℤ`): with reduced data `g > â ≥ 1`, coloring `M ≥ 1`, and the
`d ∣ 2` consequence `â + M ≤ g`, the base-length lower bound a tiling forces,
`(g−M)(g²−â²) + 2g² ≤ M·â·(g+â)`, is impossible. -/
theorem base_obstruction (g ah M : ℤ) (hah : 1 ≤ ah) (hM : 1 ≤ M) (hle : ah + M ≤ g)
    (hbridge : (g - M) * (g ^ 2 - ah ^ 2) + 2 * g ^ 2 ≤ M * ah * (g + ah)) : False := by
  have hid : (g - M) * (g ^ 2 - ah ^ 2)
      = M * ah * (g + ah) + g * (g + ah) * (g - ah - M) := by ring
  have hnn : 0 ≤ g * (g + ah) * (g - ah - M) := by
    have hg : (0:ℤ) ≤ g := by linarith
    have hga : (0:ℤ) ≤ g + ah := by linarith
    have hgam : (0:ℤ) ≤ g - ah - M := by linarith
    positivity
  nlinarith [hbridge, hid, hnn, hah, hM, hle]

/-- The two pillars combined: for prime `N`, `1 ≤ M`, `M² < N`, with the reduced tile data
`d·g = N+M²`, `d·â = N−M²` (so `d = gcd`), Beeson's geometric base-length necessary condition
`(g−M)(g²−â²) + 2g² ≤ M·â·(g+â)` cannot hold.  Hence no base-`(α+β)` `N`-tiling exists — `N` prime
is excluded, correctly (unlike Beeson III Thm 18). -/
theorem base_alphabeta_not_prime (N M d g ah : ℕ)
    (hN : N.Prime) (hM : 1 ≤ M) (hM2 : M ^ 2 < N)
    (hd : d = Nat.gcd (N - M ^ 2) (N + M ^ 2))
    (hah0 : 1 ≤ ah)
    (hdg : d * g = N + M ^ 2) (hdah : d * ah = N - M ^ 2)
    (hbridge : ((g : ℤ) - M) * ((g : ℤ) ^ 2 - (ah : ℤ) ^ 2) + 2 * (g : ℤ) ^ 2
        ≤ (M : ℤ) * ah * (g + ah)) : False := by
  have hd2 : d ∣ 2 := hd ▸ gcd_dvd_two N M hN hM hM2
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso; rw [h, Nat.zero_mul] at hdg; have := hN.two_le; omega
    · exact h
  have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd2
  -- â + M ≤ g :  d·(â+M) = (N−M²) + d·M ≤ (N−M²) + 2M² = N+M² = d·g
  have hle : ah + M ≤ g := by
    have key : d * (ah + M) ≤ d * g := by
      have h1 : d * (ah + M) = (N - M ^ 2) + d * M := by rw [Nat.mul_add, hdah]
      have h2 : d * M ≤ 2 * M ^ 2 := by nlinarith [hdle, hM]
      rw [h1, hdg]; omega
    exact Nat.le_of_mul_le_mul_left key hdpos
  exact base_obstruction g ah M (by exact_mod_cast hah0) (by exact_mod_cast hM)
    (by exact_mod_cast hle) hbridge

end Erdos634.BaseAlphaBeta

#print axioms Erdos634.BaseAlphaBeta.gcd_dvd_two
#print axioms Erdos634.BaseAlphaBeta.base_obstruction
#print axioms Erdos634.BaseAlphaBeta.base_alphabeta_not_prime
