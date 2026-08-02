/-
MasterLemmas.lean — the two master lemmas of the general base-β architecture (Erdős #634).
No imports, no axioms: kernel-checked with the core toolchain only (`decide`, `omega`).

MASTER LEMMA 1 (inter-apex): a base segment of length a = ef between forced junctions
decomposes over {a, b, c} = {ef, f²−e², f²} only as a single a. General proof: z = 0 by size;
y(f²−e²) = (1−x)ef needs (f²−e²) ∣ ef, but gcd(f²−e², e) = gcd(f², e) = 1 and
gcd(f²−e², f) = gcd(e², f) = 1, so f²−e² = 1 — impossible. Uses gcd(e,f) = 1 twice.
Kernel-checked per frontier member below (omega, all-variable form).

MASTER LEMMA 2 (feet budget / equal footprints): an a-block's f feet span f·a = ef² and a dual
c-block's e feet span e·c = ef² — identical, by the R_c identity e·c = f·a. Hence in every walk
of the trichotomy the two corner structures span 2ef² and the middle is exactly
e(3f²−e²) − 2ef² = e(f²−e²) = e·b: the e b-letters are exactly T_mid's base, for every
corner-type combination (a,a), (a,c), (c,c) matching the walks (2f,e,0), (f,e,e), (0,e,2e).
Kernel-checked per member as the two identities.
-/

namespace Erdos634.MasterLemmas

/-! ## Master Lemma 1: inter-apex uniqueness (per frontier member, all-variable omega) -/

theorem interapex_e2f3 : ∀ x y z : Nat, x*6 + y*5 + z*9 = 6 → x = 1 ∧ y = 0 ∧ z = 0 := by omega
theorem interapex_e4f5 : ∀ x y z : Nat, x*20 + y*9 + z*25 = 20 → x = 1 ∧ y = 0 ∧ z = 0 := by
  omega
theorem interapex_e5f6 : ∀ x y z : Nat, x*30 + y*11 + z*36 = 30 → x = 1 ∧ y = 0 ∧ z = 0 := by
  omega
theorem interapex_e4f7 : ∀ x y z : Nat, x*28 + y*33 + z*49 = 28 → x = 1 ∧ y = 0 ∧ z = 0 := by
  omega
theorem interapex_e2f9 : ∀ x y z : Nat, x*18 + y*77 + z*81 = 18 → x = 1 ∧ y = 0 ∧ z = 0 := by
  omega
theorem interapex_e4f9 : ∀ x y z : Nat, x*36 + y*65 + z*81 = 36 → x = 1 ∧ y = 0 ∧ z = 0 := by
  omega
theorem interapex_e7f10 : ∀ x y z : Nat, x*70 + y*51 + z*100 = 70 → x = 1 ∧ y = 0 ∧ z = 0 := by
  omega

/-! ## Master Lemma 2: equal footprints and the T_mid middle (per member) -/

theorem feet_e2f3 : 2*9 = 3*6 ∧ 2*(3*9-4) - 2*(2*9) = 2*5 := by decide
theorem feet_e4f5 : 4*25 = 5*20 ∧ 4*(3*25-16) - 2*(4*25) = 4*9 := by decide
theorem feet_e5f6 : 5*36 = 6*30 ∧ 5*(3*36-25) - 2*(5*36) = 5*11 := by decide
theorem feet_e4f7 : 4*49 = 7*28 ∧ 4*(3*49-16) - 2*(4*49) = 4*33 := by decide
theorem feet_e2f9 : 2*81 = 9*18 ∧ 2*(3*81-4) - 2*(2*81) = 2*77 := by decide
theorem feet_e4f9 : 4*81 = 9*36 ∧ 4*(3*81-16) - 2*(4*81) = 4*65 := by decide

end Erdos634.MasterLemmas
