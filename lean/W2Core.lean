/-
W2Core.lean — arithmetic cores of the W2 level recursion (Erdős #634, e = 1 family).
No imports, no axioms: kernel-checked with the core toolchain only (`decide`, `omega`).

W2 pillar 1 (filler-mesh identity), denominators cleared by 4f²:
  |J_i apex_i|²·4f²    = (3f²−1)² + (4f⁶ − (3f²−1)²) = 4f⁶       = 4f²·c²   (side c)
  |J_i apex_{i+1}|²·4f² = (f²−1)² + 4f⁶ − (3f²−1)²    = 4f²(f²−1)² = 4f²·b²  (side b)
The first is trivial; the second is the load-bearing identity, kernel-checked per member.

W2 pillar 3 (accumulated-offset congruence, f even): mod 2f, −(f²−1) ≡ +1 and 3f²−1 ≡ −1
(checked per member), and the forcing: for j < f and |s| ≤ j, 2f ∣ (s − j) implies s = j —
kernel-checked per member as `sum_forcing_*` (over ℤ, `omega`).
-/

namespace Erdos634.W2Core

/-! ## Pillar 1: the filler b-side identity  (f²−1)² + 4f⁶ − (3f²−1)² = 4f²(f²−1)² -/

theorem filler_b_f2 : (4-1)^2 + 4*2^6 - (3*4-1)^2 = 4*4*(4-1)^2 := by decide
theorem filler_b_f3 : (9-1)^2 + 4*3^6 - (27-1)^2 = 4*9*(9-1)^2 := by decide
theorem filler_b_f4 : (16-1)^2 + 4*4^6 - (48-1)^2 = 4*16*(16-1)^2 := by decide
theorem filler_b_f6 : (36-1)^2 + 4*6^6 - (108-1)^2 = 4*36*(36-1)^2 := by decide
theorem filler_b_f8 : (64-1)^2 + 4*8^6 - (192-1)^2 = 4*64*(64-1)^2 := by decide
theorem filler_b_f12 : (144-1)^2 + 4*12^6 - (432-1)^2 = 4*144*(144-1)^2 := by decide

/-! ## Pillar 3: the congruence data (f even) and the sum forcing -/

theorem offsets_f4 : (3*16-1) % 8 = 7 ∧ (8 - (16-1) % 8) = 1 := by decide
theorem offsets_f6 : (3*36-1) % 12 = 11 ∧ (12 - (36-1) % 12) = 1 := by decide
theorem offsets_f8 : (3*64-1) % 16 = 15 ∧ (16 - (64-1) % 16) = 1 := by decide
theorem offsets_f12 : (3*144-1) % 24 = 23 ∧ (24 - (144-1) % 24) = 1 := by decide

/-- the forcing: |s| ≤ j < f and 2f ∣ (s − j) imply s = j (all levels (γ,β)) — member f = 4 -/
theorem sum_forcing_f4 (j s : Int) (hj : 0 ≤ j) (hjf : j < 4)
    (hs : -j ≤ s) (hs2 : s ≤ j) (hd : (8:Int) ∣ (s - j)) : s = j := by
  obtain ⟨t, ht⟩ := hd; omega
theorem sum_forcing_f6 (j s : Int) (hj : 0 ≤ j) (hjf : j < 6)
    (hs : -j ≤ s) (hs2 : s ≤ j) (hd : (12:Int) ∣ (s - j)) : s = j := by
  obtain ⟨t, ht⟩ := hd; omega
theorem sum_forcing_f8 (j s : Int) (hj : 0 ≤ j) (hjf : j < 8)
    (hs : -j ≤ s) (hs2 : s ≤ j) (hd : (16:Int) ∣ (s - j)) : s = j := by
  obtain ⟨t, ht⟩ := hd; omega
theorem sum_forcing_f12 (j s : Int) (hj : 0 ≤ j) (hjf : j < 12)
    (hs : -j ≤ s) (hs2 : s ≤ j) (hd : (24:Int) ∣ (s - j)) : s = j := by
  obtain ⟨t, ht⟩ := hd; omega

end Erdos634.W2Core
