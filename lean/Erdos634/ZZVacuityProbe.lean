import Erdos634.BaseDecomposition
import Erdos634.SideWalk

namespace Erdos634.VacuityProbe

/-- Conclusion of `BaseDecomposition.base_decomposition_general` and `.base_decomposition_2e`,
verbatim, with **no dissection and no hypotheses**. -/
theorem basedecomp_vacuous (e0 f0 : ℕ) :
    ∃ x y z : ℕ, (x = 0 ∧ y = e0 ∧ z = 2 * e0) ∨ (x = f0 ∧ y = e0 ∧ z = e0) :=
  ⟨0, e0, 2 * e0, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- Conclusion of `SideWalk.equal_side_no_b_of_dissection`, verbatim, with no hypotheses. -/
theorem equal_side_no_b_of_dissection_vacuous : ∃ _Pc Qc : ℕ, Qc = 0 := ⟨0, 0, rfl⟩

/-- Conclusion of `SideWalk.equal_side_shape_of_gammatrap`, verbatim, from `0 ≤ f0` alone. -/
theorem equal_side_shape_vacuous (e0 f0 : ℤ) (hf0 : 0 ≤ f0) :
    ∃ Pc Rc kk : ℕ, (Pc : ℤ) = f0 * kk ∧ (Rc : ℤ) = f0 - kk * e0 :=
  ⟨0, f0.toNat, 0, by simp, by simp [Int.toNat_of_nonneg hf0]⟩

/-- Conclusion of `SideWalk.base_b_count_of_gammatrap`, verbatim, from the tile identity alone. -/
theorem base_b_count_vacuous (e0 f0 b0 : ℤ) (he0 : 0 ≤ e0) (hb0 : b0 + e0 ^ 2 = f0 ^ 2) :
    ∃ Pc Qc Rc : ℕ, (Qc : ℤ) = e0 ∧
      (Pc : ℤ) * (e0 * f0) + (Qc : ℤ) * b0 + (Rc : ℤ) * f0 ^ 2 = e0 * (3 * f0 ^ 2 - e0 ^ 2) := by
  refine ⟨0, e0.toNat, 2 * e0.toNat, by simp [Int.toNat_of_nonneg he0], ?_⟩
  push_cast [Int.toNat_of_nonneg he0]
  nlinarith [hb0]

end Erdos634.VacuityProbe
