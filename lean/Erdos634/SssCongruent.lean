import Erdos634.Congruence
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# SSS: equal side lengths give an ambient congruence

Erdős #634. `Tri.Congruent T U` asks for a genuine isometry **of the plane** carrying `T`'s
vertices to `U`'s. Mathlib's `EuclideanGeometry.side_side_side` proves the *metric* statement —
that equal corresponding sides make the two vertex families congruent in the sense of equal
pairwise distances — but that is strictly weaker: it produces no map. Every certificate in this
project checks side lengths (squared, in exact arithmetic), so the passage from "equal sides" to
"congruent" was the one lemma standing between a checked certificate and a `CongruentDissection`.

The proof is the classical one, done concretely because the plane is two-dimensional. The edge
vectors at vertex `0` are linearly independent (`ev_indep`, from affine independence) hence a
basis; equal side lengths give equal norms and, by polarisation, equal inner products
(`inner_ev_eq`); so the linear map matching one basis to the other preserves the inner product
(`LinearMap.isometryOfInner`), is a linear isometry equivalence, and conjugating it by the two
translations that move the base vertices to the origin gives the isometry of the plane.

`congruent_of_dist` is the result, and `congruent_of_dist_three` is the three-sided form a
certificate actually supplies.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SssCongruent

open Erdos634.Geometry RealInnerProductSpace

/-- The two edge vectors of `T` at vertex `0`. -/
noncomputable def ev (T : Tri) : Fin 2 → Plane := ![T.pts 1 - T.pts 0, T.pts 2 - T.pts 0]

/-- **The edge vectors at a vertex are linearly independent.** -/
theorem ev_indep (T : Tri) : LinearIndependent ℝ (ev T) := by
  rw [ev, LinearIndependent.pair_iff]
  intro s t hst
  have haff := affineIndependent_iff.mp T.indep Finset.univ ![-s - t, s, t]
  have hw : ∑ i, (![-s - t, s, t] : Fin 3 → ℝ) i = 0 := by
    simp [Fin.sum_univ_three]; ring
  have hp : ∑ i, (![-s - t, s, t] : Fin 3 → ℝ) i • T.pts i = 0 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    have h : s • (T.pts 1 - T.pts 0) + t • (T.pts 2 - T.pts 0) = 0 := hst
    rw [smul_sub, smul_sub] at h
    rw [sub_smul, neg_smul]
    linear_combination (norm := module) h
  have hz := haff hw hp
  have h1 := hz 1 (Finset.mem_univ _)
  have h2 := hz 2 (Finset.mem_univ _)
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at h1 h2
  exact ⟨h1, h2⟩

/-- The edge vectors, as a basis of the plane. -/
noncomputable def evBasis (T : Tri) : Module.Basis (Fin 2) ℝ Plane :=
  basisOfLinearIndependentOfCardEqFinrank (ev_indep T) (by simp)

@[simp] theorem evBasis_apply (T : Tri) (i : Fin 2) : evBasis T i = ev T i := by
  simp [evBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- **Equal side lengths give equal inner products of the edge vectors** — polarisation. -/
theorem inner_ev_eq {T U : Tri} (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j))
    (i j : Fin 2) : ⟪ev T i, ev T j⟫ = ⟪ev U i, ev U j⟫ := by
  have hnorm : ∀ (V : Tri) (a b : Fin 3), ‖V.pts a - V.pts b‖ = dist (V.pts a) (V.pts b) :=
    fun V a b => (dist_eq_norm _ _).symm
  have key : ∀ (V : Tri) (a b : Fin 2),
      ⟪ev V a, ev V b⟫
        = (dist (V.pts a.succ) (V.pts 0) ^ 2 + dist (V.pts b.succ) (V.pts 0) ^ 2
            - dist (V.pts a.succ) (V.pts b.succ) ^ 2) / 2 := by
    intro V a b
    have hsub : ev V a - ev V b = V.pts a.succ - V.pts b.succ := by
      fin_cases a <;> fin_cases b <;> simp [ev] <;> abel
    have hpol : ⟪ev V a, ev V b⟫ = (‖ev V a‖ ^ 2 + ‖ev V b‖ ^ 2 - ‖ev V a - ev V b‖ ^ 2) / 2 := by
      rw [@norm_sub_sq_real]; ring
    rw [hpol, hsub]
    have hea : ev V a = V.pts a.succ - V.pts 0 := by fin_cases a <;> simp [ev]
    have heb : ev V b = V.pts b.succ - V.pts 0 := by fin_cases b <;> simp [ev]
    rw [hea, heb, hnorm, hnorm, hnorm]
  rw [key T, key U, hd, hd, hd]

/-- The linear map matching `T`'s edge basis to `U`'s. -/
noncomputable def evMap (T U : Tri) : Plane →ₗ[ℝ] Plane := (evBasis T).constr ℝ (ev U)

theorem evMap_basis (T U : Tri) (i : Fin 2) : evMap T U (ev T i) = ev U i := by
  rw [evMap, ← evBasis_apply T i, Module.Basis.constr_basis]

theorem expand (T : Tri) (x : Plane) :
    x = (evBasis T).repr x 0 • ev T 0 + (evBasis T).repr x 1 • ev T 1 := by
  conv_lhs => rw [← (evBasis T).sum_repr x]
  rw [Fin.sum_univ_two, evBasis_apply, evBasis_apply]

theorem evMap_expand (T U : Tri) (x : Plane) :
    evMap T U x = (evBasis T).repr x 0 • ev U 0 + (evBasis T).repr x 1 • ev U 1 := by
  conv_lhs => rw [expand T x]
  rw [map_add, map_smul, map_smul, evMap_basis, evMap_basis]

/-- **`evMap` preserves the inner product**, given equal side lengths. -/
theorem evMap_inner {T U : Tri} (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j))
    (x y : Plane) : ⟪evMap T U x, evMap T U y⟫ = ⟪x, y⟫ := by
  conv_lhs => rw [evMap_expand, evMap_expand]
  conv_rhs => rw [expand T x, expand T y]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ← inner_ev_eq hd]

/-- `T`'s edge basis matched to `U`'s, as a linear equivalence. -/
noncomputable def evEquiv (T U : Tri) : Plane ≃ₗ[ℝ] Plane :=
  (evBasis T).equiv (evBasis U) (Equiv.refl (Fin 2))

theorem evEquiv_eq (T U : Tri) (x : Plane) : evEquiv T U x = evMap T U x := by
  have hb : ∀ i, (evEquiv T U).toLinearMap (evBasis T i) = evMap T U (evBasis T i) := by
    intro i
    show evEquiv T U (evBasis T i) = evMap T U (evBasis T i)
    rw [evEquiv, Module.Basis.equiv_apply]
    simp only [Equiv.refl_apply, evBasis_apply, evMap_basis]
  exact congrFun (congrArg DFunLike.coe ((evBasis T).ext hb)) x

/-- **The linear isometry equivalence matching `T`'s edge basis to `U`'s.** -/
noncomputable def evIso {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) : Plane ≃ₗᵢ[ℝ] Plane :=
  (evEquiv T U).isometryOfInner (by
    intro x y
    rw [evEquiv_eq, evEquiv_eq]
    exact evMap_inner hd x y)

@[simp] theorem evIso_apply {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) (x : Plane) :
    evIso hd x = evMap T U x := by
  rw [evIso, LinearEquiv.coe_isometryOfInner, evEquiv_eq]

/-- **The isometry of the plane realising the congruence.** -/
noncomputable def sssIso {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) : Plane ≃ᵢ Plane :=
  ((IsometryEquiv.addRight (-T.pts 0)).trans (evIso hd).toIsometryEquiv).trans
    (IsometryEquiv.addRight (U.pts 0))

theorem sssIso_apply {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) (x : Plane) :
    sssIso hd x = evMap T U (x + -T.pts 0) + U.pts 0 := by
  simp [sssIso, IsometryEquiv.addRight, LinearIsometryEquiv.toIsometryEquiv]

/-- **SSS congruence, with an ambient isometry.** Two triangles whose corresponding vertices are
pairwise equidistant are congruent in the sense of `Tri.Congruent`: there is an isometry of the
whole plane carrying one onto the other, vertex for vertex. -/
theorem congruent_of_dist {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) : T.Congruent U := by
  refine ⟨sssIso hd, Equiv.refl _, ?_⟩
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  intro k
  show sssIso hd (T.pts k) = U.pts k
  rcases htri k with rfl | rfl | rfl
  · rw [sssIso_apply]
    have h0 : T.pts 0 + -T.pts 0 = (0 : Plane) := by abel
    rw [h0, map_zero, zero_add]
  · rw [sssIso_apply]
    have h1 : T.pts 1 + -T.pts 0 = ev T 0 := by simp [ev]; abel
    rw [h1, evMap_basis]
    show U.pts 1 - U.pts 0 + U.pts 0 = U.pts 1
    abel
  · rw [sssIso_apply]
    have h2 : T.pts 2 + -T.pts 0 = ev T 1 := by simp [ev]; abel
    rw [h2, evMap_basis]
    show U.pts 2 - U.pts 0 + U.pts 0 = U.pts 2
    abel

/-- **SSS in the three-sided form a certificate supplies.** -/
theorem congruent_of_dist_three {T U : Tri}
    (h01 : dist (T.pts 0) (T.pts 1) = dist (U.pts 0) (U.pts 1))
    (h12 : dist (T.pts 1) (T.pts 2) = dist (U.pts 1) (U.pts 2))
    (h20 : dist (T.pts 2) (T.pts 0) = dist (U.pts 2) (U.pts 0)) : T.Congruent U := by
  refine congruent_of_dist ?_
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  intro i j
  rcases htri i with rfl | rfl | rfl <;> rcases htri j with rfl | rfl | rfl <;>
    simp_all [dist_comm]

/-! ## SSS up to relabelling, and from *squared* lengths

A certificate checks a squared side **multiset**, so it certifies equal sides only after some
relabelling of the vertices, and it certifies the *squares*. Both gaps are closed here. -/

/-- `U` with its vertices relabelled by `σ`. -/
def permTri (U : Tri) (σ : Equiv.Perm (Fin 3)) : Tri where
  pts := U.pts ∘ σ
  indep := U.indep.comp_embedding σ.toEmbedding

/-- A relabelling is a congruence — that is exactly what the permutation in `Tri.Congruent` is
for. -/
theorem congruent_permTri (U : Tri) (σ : Equiv.Perm (Fin 3)) : (permTri U σ).Congruent U :=
  ⟨IsometryEquiv.refl Plane, σ, fun k => rfl⟩

/-- **SSS up to relabelling.** -/
theorem congruent_of_dist_perm {T U : Tri} (σ : Equiv.Perm (Fin 3))
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts (σ i)) (U.pts (σ j))) : T.Congruent U :=
  (congruent_of_dist (U := permTri U σ) hd).trans (congruent_permTri U σ)

/-- Equal squared distances give equal distances. -/
theorem dist_of_sq {a b c d : Plane} (h : dist a b ^ 2 = dist c d ^ 2) : dist a b = dist c d := by
  have h1 : (0:ℝ) ≤ dist a b := dist_nonneg
  have h2 : (0:ℝ) ≤ dist c d := dist_nonneg
  nlinarith [h, h1, h2]

/-- **SSS from squared side lengths, up to relabelling** — the form a certificate supplies. -/
theorem congruent_of_sq_dist_perm {T U : Tri} (σ : Equiv.Perm (Fin 3))
    (hd : ∀ i j, dist (T.pts i) (T.pts j) ^ 2 = dist (U.pts (σ i)) (U.pts (σ j)) ^ 2) :
    T.Congruent U :=
  congruent_of_dist_perm σ (fun i j => dist_of_sq (hd i j))

end Erdos634.SssCongruent
