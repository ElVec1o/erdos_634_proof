/-
GeneralPillars.lean — the general-e pillars of the base-β campaign (Erdős #634, Program B).
No imports, no axioms: kernel-checked with the core toolchain only (`decide`, `omega`).

The four pillars that carry over from the e = 1 proof to every coprime (e, f), 1 ≤ e < f:
  P1 column reach: b·sinγ = c·sinβ (law of sines — no formalization needed beyond the identity);
  P2 THE FILLER IDENTITY, denominators cleared by 4f². The two filler triangles share one value
       of c²sin²β; eliminating it between
         (e(3f²−e²)/(2f))² + c²sin²β = f⁴      (c-side)
         (e(f²−e²)/(2f))²  + c²sin²β = (f²−e²)² (b-side)
       leaves, after clearing by 4f², the single identity
         e²(f²−e²)² + 4f⁶ − e²(3f²−e²)² = 4f²(f²−e²)².
       Checked per frontier member below. NOTE (2026-09-10): this is a polynomial identity in
       (e,f) over any commutative ring, and is now proved as such in
       `FillerGeneral.filler_b_general_ef` (with `.filler_c_general_ef`, `.filler_consistent_ef`);
       every `filler_b_*` below is an instance of it. They are kept here only to preserve this
       file's no-import property.
  P3 sector kills: γ − (α+β) = α > 0 and cosγ = −e/(2f) < 0 (identities; no arithmetic content);
  P4 interior multiples: b = (f−e)(f+e) > f and c = f² > f: any sub-f² placement of b or c
     contains an interior multiple of f (witness p/f + 1), per member.
Certificates: the (2,3) side-break refutation joins (1,3), (1,4)×2 (companion §"Scope,
certificates, verification"). NOTE 2026-09-10: this header previously gave "251 nodes" for the
(2,3) run; that figure is corroborated nowhere in `paper/`, `data/SETTLED.tsv` or the log, so it
is removed rather than repeated. The companion records node counts only for (1,2), (1,3), (1,4)
(267, 1809, 1728).
-/

namespace Erdos634.GeneralPillars

/-! ## P2: the general filler b-side identity  e²(f²−e²)² + 4f⁶ − e²(3f²−e²)² = 4f²(f²−e²)²
    (e = 1 instances live in W2Core.lean; here the e ≥ 2 frontier members) -/

theorem filler_b_e2f3 : 4*(9-4)^2 + 4*3^6 - 4*(27-4)^2 = 4*9*(9-4)^2 := by decide
theorem filler_b_e2f5 : 4*(25-4)^2 + 4*5^6 - 4*(75-4)^2 = 4*25*(25-4)^2 := by decide
theorem filler_b_e4f5 : 16*(25-16)^2 + 4*5^6 - 16*(75-16)^2 = 4*25*(25-16)^2 := by decide
theorem filler_b_e5f6 : 25*(36-25)^2 + 4*6^6 - 25*(108-25)^2 = 4*36*(36-25)^2 := by decide
theorem filler_b_e4f7 : 16*(49-16)^2 + 4*7^6 - 16*(147-16)^2 = 4*49*(49-16)^2 := by decide
theorem filler_b_e2f9 : 4*(81-4)^2 + 4*9^6 - 4*(243-4)^2 = 4*81*(81-4)^2 := by decide
theorem filler_b_e4f9 : 16*(81-16)^2 + 4*9^6 - 16*(243-16)^2 = 4*81*(81-16)^2 := by decide

/-! ## P4: interior multiples, e ≥ 2 members (b-edge form; c is a fortiori) -/

theorem b_lattice_e2f3 (p : Nat) : ∃ m, p < 3*m ∧ 3*m < p + 5 := ⟨p/3+1, by omega, by omega⟩
theorem b_lattice_e4f5 (p : Nat) : ∃ m, p < 5*m ∧ 5*m < p + 9 := ⟨p/5+1, by omega, by omega⟩
theorem b_lattice_e5f6 (p : Nat) : ∃ m, p < 6*m ∧ 6*m < p + 11 := ⟨p/6+1, by omega, by omega⟩
theorem b_lattice_e4f7 (p : Nat) : ∃ m, p < 7*m ∧ 7*m < p + 33 := ⟨p/7+1, by omega, by omega⟩
theorem b_lattice_e2f9 (p : Nat) : ∃ m, p < 9*m ∧ 9*m < p + 77 := ⟨p/9+1, by omega, by omega⟩

/-! ## The new e ≥ 2 fact: c − a = f(f−e) has NO whole-edge decomposition
    (x·ef + y(f²−e²) + z·f² = f(f−e) has no solution: mod f kills y; xe + zf = f−e forces
     x ≡ −1 (mod f), xe ≥ (f−1)e > f−e for e ≥ 2) — so runs must extend past c:
     the generalized column is unavoidable. Per-member: -/

theorem c_minus_a_undec_e2f3 : ∀ x y z : Nat, x*6 + y*5 + z*9 ≠ 3 := by omega
theorem c_minus_a_undec_e4f5 : ∀ x y z : Nat, x*20 + y*9 + z*25 ≠ 5 := by omega
theorem c_minus_a_undec_e5f6 : ∀ x y z : Nat, x*30 + y*11 + z*36 ≠ 6 := by omega
theorem c_minus_a_undec_e4f7 : ∀ x y z : Nat, x*28 + y*33 + z*49 ≠ 21 := by omega
theorem c_minus_a_undec_e2f9 : ∀ x y z : Nat, x*18 + y*77 + z*81 ≠ 63 := by omega

end Erdos634.GeneralPillars
