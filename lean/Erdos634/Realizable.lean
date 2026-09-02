import Erdos634.Ladder

/-!
# `cor:ladder`: the realizable set of a base-β family is closed under multiples

Erdős #634, `cor:ladder`. With `thm:ladder` a theorem (`Ladder.ladder`), the corollary is the
statement *about the set*: writing

  `S = { m ≥ 1 : the scale-m target is cut into m²N₀ copies of the tile }`,

it says `m ∈ S ⇒ km ∈ S` for every `k ≥ 1`, so `S` is a union of multiples of its minimal
elements — and in particular `S ≠ ∅` does **not** give `1 ∈ S`.

Two things are needed beyond `thm:ladder`, and this file supplies them.

* A **scale operation on triangles**: `scaleTri r T` is the homothety of `T` about its own first
  vertex with ratio `r`. Because a homothety fixes its centre, the centre of `scaleTri r T` is
  again `T.pts 0`, and so scaling composes *on the nose*: `scaleTri r (scaleTri s T) =
  scaleTri (r*s) T` (`scaleTri_scaleTri`). This is what turns "apply the ladder at `k` to the
  scale-`m` target" into a statement about the scale-`km` target.
* A **realizability predicate** `Cut T t N` — "`T` is cut into `N` copies of `t`" — as a `Prop`,
  so that `S` is a set of naturals and the closure statement can be quantified.

`cut_scale` is the ladder in these terms, and `mem_realizableSet_mul` is `cor:ladder` as written.
Note what is *not* claimed: nothing here says `S` is nonempty, and nothing gives `1 ∈ S` — that
is exactly the corollary's point.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Realizable

open Erdos634.Geometry Erdos634.Subdivision Erdos634.Ladder

/-- Two triangles with the same vertex map are equal (the independence field is a `Prop`). -/
theorem Tri.ext' {T U : Tri} (h : T.pts = U.pts) : T = U := by
  cases T; cases U; simp_all

/-- A triangle is the triple of its own vertices. -/
theorem Tri.eta (T : Tri) :
    (⟨![T.pts 0, T.pts 1, T.pts 2], by
        have h : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
          funext x; fin_cases x <;> rfl
        rw [h]; exact T.indep⟩ : Tri) = T := by
  refine Tri.ext' ?_
  funext x; fin_cases x <;> rfl

/-- **The scale-`r` copy of `T`**: the homothety of `T` about its own first vertex. -/
noncomputable def scaleTri (r : ℝ) (hr : r ≠ 0) (T : Tri) : Tri where
  pts := (bigMap (T.pts 0) r) ∘ T.pts
  indep := T.indep.map' _ (bigMap_injective (T.pts 0) hr)

@[simp] theorem scaleTri_pts (r : ℝ) (hr : r ≠ 0) (T : Tri) (i : Fin 3) :
    (scaleTri r hr T).pts i = AffineMap.homothety (T.pts 0) r (T.pts i) := rfl

/-- A homothety fixes its centre, so scaling does not move the first vertex. -/
@[simp] theorem scaleTri_pts0 (r : ℝ) (hr : r ≠ 0) (T : Tri) :
    (scaleTri r hr T).pts 0 = T.pts 0 := by
  simp [scaleTri, bigMap, AffineMap.homothety_apply]

/-- **Scaling composes.** Both sides are the homothety about the same centre `T.pts 0`. -/
theorem scaleTri_scaleTri (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r * s ≠ 0) (T : Tri) :
    scaleTri r hr (scaleTri s hs T) = scaleTri (r * s) hrs T := by
  refine Tri.ext' ?_
  funext i
  simp only [scaleTri_pts, scaleTri_pts0, bigMap, AffineMap.homothety_apply, vsub_eq_sub,
    vadd_eq_add, scaleTri]
  simp only [Function.comp_apply, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  module

/-- The scale-`k` copy at a natural ratio `k ≥ 1`. -/
noncomputable def scaleN (k : ℕ) (hk : 0 < k) (T : Tri) : Tri :=
  scaleTri (k : ℝ) (by exact_mod_cast hk.ne') T

theorem scaleN_scaleN (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (T : Tri) :
    scaleN k hk (scaleN m hm T) = scaleN (k * m) (Nat.mul_pos hk hm) T := by
  refine (scaleTri_scaleTri _ _ _ _ (by positivity) T).trans ?_
  simp only [scaleN, scaleTri]
  congr 1
  push_cast
  ring

/-- `scaleN k` of `ABC` is exactly the scale-`k` triangle the subdivision is built in. -/
theorem scaleN_eq_bigTri (A B C : Plane) (hindep : AffineIndependent ℝ ![A, B, C])
    (k : ℕ) (hk : 0 < k) :
    scaleN k hk (⟨![A, B, C], hindep⟩ : Tri) = bigTri A B C hindep k hk := by
  refine Tri.ext' ?_
  funext x
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  rcases htri x with rfl | rfl | rfl <;>
    simp [scaleN, scaleTri, bigMap, bigTri, P, AffineMap.homothety_apply] <;>
    module

/-- **`T` is cut into `N` copies of `t`.** -/
def Cut (T t : Tri) (N : ℕ) : Prop :=
  ∃ D : CongruentDissection N, D.target = T ∧ D.model = t

/-- **The ladder, on the scale operation.** -/
theorem cut_scale {T t : Tri} {N : ℕ} (h : Cut T t N) (k : ℕ) (hk : 0 < k) :
    Cut (scaleN k hk T) t (k * k * N) := by
  obtain ⟨D, hTgt, hMod⟩ := h
  -- present `T` as a labelled triple, which is the form `Ladder.ladder` takes
  have hindep : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by
    have h : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
      funext x; fin_cases x <;> rfl
    rw [h]; exact T.indep
  have hT : D.target = (⟨![T.pts 0, T.pts 1, T.pts 2], hindep⟩ : Tri) := by
    rw [hTgt]; exact (Tri.eta T).symm
  obtain ⟨E, hEt, hEm⟩ := ladder _ _ _ hindep D hT k hk
  refine ⟨E, ?_, by rw [hEm, hMod]⟩
  rw [hEt, ← scaleN_eq_bigTri]
  congr 1
  exact Tri.eta T

/-- **`cor:ladder`.** `S(T,t,N₀) = {m ≥ 1 : the scale-`m` copy of `T` is cut into `m²N₀` copies of
`t`}` is closed under multiplication: `m ∈ S ⇒ km ∈ S` for every `k ≥ 1`. Hence `S` is the union
of the multiples of its minimal elements. -/
theorem cut_scale_mul (T t : Tri) (N₀ m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (h : Cut (scaleN m hm T) t (m * m * N₀)) :
    Cut (scaleN (k * m) (Nat.mul_pos hk hm) T) t ((k * m) * (k * m) * N₀) := by
  have hstep := cut_scale h k hk
  rw [scaleN_scaleN] at hstep
  have harith : k * k * (m * m * N₀) = k * m * (k * m) * N₀ := by ring
  rwa [harith] at hstep

/-- The realizable set itself, as a set of naturals. -/
def realizableSet (T t : Tri) (N₀ : ℕ) : Set ℕ :=
  {m | ∃ hm : 0 < m, Cut (scaleN m hm T) t (m * m * N₀)}

theorem mem_realizableSet_mul (T t : Tri) (N₀ : ℕ) {m : ℕ} (hmem : m ∈ realizableSet T t N₀)
    (k : ℕ) (hk : 0 < k) : k * m ∈ realizableSet T t N₀ := by
  obtain ⟨hm, h⟩ := hmem
  exact ⟨Nat.mul_pos hk hm, cut_scale_mul T t N₀ m k hm hk h⟩

/-- `d` is a minimal element of the realizable set: it is realizable, and no proper divisor of it
is. -/
def IsMinimal (T t : Tri) (N₀ d : ℕ) : Prop :=
  d ∈ realizableSet T t N₀ ∧ ∀ e ∈ realizableSet T t N₀, e ∣ d → e = d

theorem pos_of_mem {T t : Tri} {N₀ m : ℕ} (h : m ∈ realizableSet T t N₀) : 0 < m := h.1

/-- **A prime realizable scale is automatically minimal, given `1` is not realizable.** A prime
`p`'s only divisors are `1` and `p`; if `1 ∉ S` then no divisor other than `p` itself can witness
`p`'s non-minimality. This is exactly `cor:elevenm`'s primitivity claim in general form: "neither
the `44`- nor `99`-tiling arises from `thm:ladder` applied to a smaller member" reduces to this,
since the scales `2` and `3` are both prime. -/
theorem isMinimal_of_prime_of_one_not_mem (T t : Tri) (N₀ p : ℕ) (hp : Nat.Prime p)
    (h1 : (1:ℕ) ∉ realizableSet T t N₀) (hpmem : p ∈ realizableSet T t N₀) :
    IsMinimal T t N₀ p := by
  refine ⟨hpmem, ?_⟩
  intro e he hdvd
  rcases hp.eq_one_or_self_of_dvd e hdvd with h1' | h2'
  · exact absurd (h1' ▸ he) h1
  · exact h2'

/-- **Every realizable scale is a multiple of a minimal one.** -/
theorem exists_minimal_divisor (T t : Tri) (N₀ : ℕ) :
    ∀ m ∈ realizableSet T t N₀, ∃ d, IsMinimal T t N₀ d ∧ d ∣ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hmin : ∀ e ∈ realizableSet T t N₀, e ∣ m → e = m
    · exact ⟨m, ⟨hm, hmin⟩, dvd_refl m⟩
    · push_neg at hmin
      obtain ⟨e, he, hdvd, hne⟩ := hmin
      have hlt : e < m := lt_of_le_of_ne (Nat.le_of_dvd (pos_of_mem hm) hdvd) hne
      obtain ⟨d, hd, hdve⟩ := ih e hlt he
      exact ⟨d, hd, hdve.trans hdvd⟩

/-- **`cor:ladder`, second clause.** The realizable set is exactly the union of the multiples of
its minimal elements. -/
theorem realizableSet_eq_multiples (T t : Tri) (N₀ : ℕ) :
    realizableSet T t N₀ = {m | ∃ d, IsMinimal T t N₀ d ∧ ∃ k, 0 < k ∧ m = k * d} := by
  ext m
  constructor
  · intro hm
    obtain ⟨d, hd, k, hk⟩ := exists_minimal_divisor T t N₀ m hm
    refine ⟨d, hd, k, ?_, by rw [hk, Nat.mul_comm]⟩
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hk; exact absurd hk.symm (pos_of_mem hm).ne
    · exact h
  · rintro ⟨d, hd, k, hk, rfl⟩
    exact mem_realizableSet_mul T t N₀ hd.1 k hk

/-! ## Toward a real-ratio scale map on a whole dissection

`scaleTri` scales a single `Tri` by any real `r ≠ 0`. `DissectionMap.mapDissection` transports a
whole `Dissection` along any `Plane ≃ᵃ[ℝ] Plane`. Composing these — scaling a whole
`CongruentDissection` down (or up) by an arbitrary real ratio, not just a natural blow-up like
`Ladder.ladder` — is the missing piece for a specific, concrete instance of structural blocker 1:
`Tiling44Bridge.dissection`'s target and model tile have real side lengths exactly `8×` the
base-β member `(e,f)=(1,2)`'s abstract `Δ₂`/`(2,3,4)` values (`176,128,128` vs `22,16,16`;
`16,24,32` vs `2,3,4` — checked directly against `targetTri_sides`/`model_sides`, matching the
paper's own `Y₁=11,X₁=8,N₁=11` data for this member exactly). Scaling `Tiling44Bridge.dissection`
down by `1/8` would give a genuine `CongruentDissection` whose model/target sides are the *exact*,
unscaled values `SideWalk.lean`'s `_of_gammatrap` family (`equal_side_no_b_of_gammatrap` etc.)
needs for its `hA`,`hB`,`hC`,`hLen` hypotheses — closing a concrete case of structural blocker 1,
not the general case, but a real one.

`homothetyEquiv` below is the first piece: the homothety about a point, as a genuine
`Plane ≃ᵃ[ℝ] Plane` (not just the one-directional `AffineMap.homothety` `scaleTri` already uses),
so `mapDissection` can transport a whole dissection through it. **Not yet done**: proving
`Tri.Congruent` is preserved under the image of a similarity (a homothety conjugates an isometry to
an isometry, since the scale factors cancel: `e ∘ f ∘ e⁻¹` scales distances by `|r| · 1 · 1/|r| =
1`) — needed to show the tiles of a scaled `CongruentDissection` are still all congruent to the
scaled model. That conjugation lemma, plus assembling the whole `scaleDissection` operation, is the
next concrete step. -/

/-- The homothety about `p` with ratio `r ≠ 0`, as a genuine affine equivalence (not just the
one-directional `AffineMap.homothety`). -/
noncomputable def homothetyEquiv (p : Plane) (r : ℝ) (hr : r ≠ 0) : Plane ≃ᵃ[ℝ] Plane :=
  AffineEquiv.homothetyUnitsMulHom p (Units.mk0 r hr)

theorem homothetyEquiv_apply (p : Plane) (r : ℝ) (hr : r ≠ 0) (x : Plane) :
    homothetyEquiv p r hr x = AffineMap.homothety p r x := by
  show (AffineEquiv.homothetyUnitsMulHom p (Units.mk0 r hr) : Plane → Plane) x = _
  rw [AffineEquiv.coe_homothetyUnitsMulHom_apply]
  norm_num

end Erdos634.Realizable
