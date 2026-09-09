import Erdos634.BaseDecomposition
import Erdos634.SideWalk
import Erdos634.BaseChain

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

/-! ### Batch 9 (2026-09-10): the vertex-figure existentials

Same bug class, found in `VertexFigureReal`. Both theorems take a real `Dissection N`, a real point
`v`, and the hypothesis that every tile's local angle at `v` lies in `{α,β,γ,π,0}` — and then
conclude only that *some* naturals `p q r s` satisfy an angle identity. The identity is satisfied by
the constant tuple that ignores the dissection entirely, so the conclusion carries no information
about `D`, `v`, or the angles at `v`. The docstrings' claim that `s` "counts the tiles meeting the
point in the interior of one of their edges" is nowhere in the statement. -/

/-- Conclusion of `VertexFigureReal.vertex_multiplicities_real`, verbatim, with **no dissection,
no point, and no hypotheses**: take `(p,q,r,s) = (0,0,0,1)`. -/
theorem vertex_multiplicities_real_vacuous (α β γ : ℝ) :
    ∃ p q r s : ℕ, (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = Real.pi :=
  ⟨0, 0, 0, 1, by push_cast; ring⟩

/-- Conclusion of `VertexFigureReal.interior_multiplicities_real`, verbatim, with **no dissection,
no point, and no hypotheses**: take `(p,q,r,s,u) = (0,0,0,0,1)`. -/
theorem interior_multiplicities_real_vacuous (α β γ : ℝ) :
    ∃ p q r s u : ℕ,
      (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi + (u : ℝ) * (2 * Real.pi)
        = 2 * Real.pi :=
  ⟨0, 0, 0, 0, 1, by push_cast; ring⟩

/-! ### Batch 10 (2026-09-10): the base-chain enumeration existential

`BaseChain.base_chain_consecutive_meet` packs the enumeration `E` into the conclusion while
dropping the three properties (`hmono`, `hmem`, `hsurj`) that tie `E` to `wallList D g c`.  What is
left is satisfied by the *constant* enumeration, since `edgePos e = min … ≤ max … = edgeEnd e` for
one and the same edge `e`.  The dissection, the wall functional `g`, the base `a b` and all five
geometric hypotheses are unused. -/

/-- Conclusion of `BaseChain.base_chain_consecutive_meet`, verbatim, with **no wall hypotheses, no
base segment, and no relation between `E` and `wallList`**: take `E` constant. -/
theorem base_chain_consecutive_meet_vacuous {N : ℕ} (hN : 0 < N) (D : Erdos634.Geometry.Dissection N)
    (g : Erdos634.Geometry.Plane →ᵃ[ℝ] ℝ) (c : ℝ) (dir : Erdos634.Geometry.Plane →ₗ[ℝ] ℝ) :
    ∃ E : ℕ → Fin N × Fin 3, ∀ k, k + 1 < (Erdos634.BaseChain.wallList D g c).length →
      ∃ j ≤ k, Erdos634.OrientBridge.edgePos D dir (E (k + 1))
        ≤ Erdos634.ChainInstance.edgeEnd D dir (E j) :=
  ⟨fun _ => (⟨0, hN⟩, 0), fun k _ => ⟨0, Nat.zero_le k,
    min_le_max⟩⟩

end Erdos634.VacuityProbe
