import Erdos634.CornerAnglePerm

/-!
# The summation engine for the census partition

Split out of `CornerAnglePerm.lean` (Lean rule 2.3's file-length guideline). The census identities
all have the shape "sum a per-point weight over all tile vertices, and it equals a linear
combination of the class counts" — with the classes being the fibres of the multiplicity vector,
that is a general fact about summing a fibre-constant function, plus its instantiation for
`lem:census`'s eight `censusLabels` and the target vertex counts.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Geometry

/-! ## The summation engine for the census partition

The census identities all have the shape "sum a per-point weight over all tile vertices, and it
equals a linear combination of the class counts".  With the classes being the fibres of the
multiplicity vector, that is a general fact about summing a fibre-constant function. -/

/-- **Summing a fibre-constant weight.**  If `g` depends on `x` only through `f x`, the sum of `g`
over `s` is the class-count combination `∑ y, c y * |fibre y|`. -/
theorem sum_over_fibers_const {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (f : ι → κ) (hmaps : ∀ x ∈ s, f x ∈ t) (g : ι → ℕ) (c : κ → ℕ)
    (hconst : ∀ x ∈ s, g x = c (f x)) :
    ∑ x ∈ s, g x = ∑ y ∈ t, c y * (s.filter (fun x => f x = y)).card := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmaps g]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have : ∀ x ∈ s.filter (fun x => f x = y), g x = c y := by
    intro x hx
    obtain ⟨hxs, hxy⟩ := Finset.mem_filter.mp hx
    rw [hconst x hxs, hxy]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- The `(α, β, γ)`-multiplicity vector at a point: the census's class label. -/
noncomputable def figureVec {N : ℕ} (D : Dissection N) (α β γ : ℝ) (v : Plane) : ℕ × ℕ × ℕ := by
  classical
  exact (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
    ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card)

/-- The eight class labels of `lem:census`: apex `{3α}`, base corner `{β}`, the two straight figures
`{α,β,γ}` and `{3α,2β}`, and the four interior figures `{β,3γ}`, `{2α,2β,2γ}`, `{4α,3β,γ}`,
`{6α,4β}`.  All eight vectors are distinct, so the classes are automatically disjoint. -/
def censusLabels : Finset (ℕ × ℕ × ℕ) :=
  {(3, 0, 0), (0, 1, 0), (1, 1, 1), (3, 2, 0), (0, 1, 3), (2, 2, 2), (4, 3, 1), (6, 4, 0)}

theorem censusLabels_card : censusLabels.card = 8 := by decide

/-- **Every tile vertex carries one of the eight census labels.**  The maps-to obligation of the
partition: `cornerPts_trichotomy` splits the point three ways, and the three classification
theorems — `TileAt.congruentDissection_apex_counts` / `.congruentDissection_base_corner_counts` at
the target's corners, `congruentDissection_boundary_figure_at_corner` on the rest of the frontier,
`congruentDissection_interior_figure_at_corner` inside — land each case on one of the eight labels.

`htarget` is the base-`β` target's own shape: each of its corners is the apex `3α` or a base `β`. -/
theorem figureVec_mem_censusLabels {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β)
    {v : Plane} (hv : v ∈ cornerPts D.toDissection) :
    ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
      ∈ censusLabels := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
  rcases cornerPts_trichotomy D.toDissection hv with hc | ⟨hfr, hnv⟩ | hint
  · obtain ⟨k, hk⟩ := hc
    subst hk
    rcases htarget k with h3 | hb
    · obtain ⟨ha, hb', hc', -⟩ := Erdos634.Geometry.Dissection.congruentDissection_apex_counts D
        α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k h3
      simp [censusLabels, ha, hb', hc']
    · obtain ⟨ha, hb', hc', -⟩ :=
        Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D
        α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k hb
      simp [censusLabels, ha, hb', hc']
  · rcases congruentDissection_boundary_figure_at_corner D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ hfr hnv j m hm with
      ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
    · simp [censusLabels, ha, hb, hc]
    · simp [censusLabels, ha, hb, hc]
  · rcases congruentDissection_interior_figure_at_corner D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ
      hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr hint j m hm with
      ⟨-, hcase⟩ | ⟨-, hcase⟩
    · rcases hcase with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;> simp [censusLabels, ha, hb, hc]
    · rcases hcase with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;>
        simp [censusLabels, ha, hb, hc]

/-- The model's three corner angles are pairwise distinct, indexed. -/
theorem model_corner_dist {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    ∀ k l : Fin 3,
      cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
        = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2)) → k = l := by
  have e0 : (0 : Fin 3) + 1 = 1 := rfl
  have e0' : (0 : Fin 3) + 2 = 2 := rfl
  have e1 : (1 : Fin 3) + 1 = 2 := rfl
  have e1' : (1 : Fin 3) + 2 = 0 := rfl
  have e2 : (2 : Fin 3) + 1 = 0 := rfl
  have e2' : (2 : Fin 3) + 2 = 1 := rfl
  have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  intro k l h
  rcases hall k with rfl | rfl | rfl <;> rcases hall l with rfl | rfl | rfl <;>
    simp only [e0, e0', e1, e1', e2, e2', hmα, hmβ, hmγ] at h <;>
    first
      | rfl
      | exact absurd h hαβ
      | exact absurd h hαγ
      | exact absurd h hβγ
      | exact absurd h.symm hαβ
      | exact absurd h.symm hαγ
      | exact absurd h.symm hβγ

/-- **The `α`-identity of the census, as a sum over the eight classes.**  Instantiating
`sum_over_fibers_const` with the `α`-multiplicity as weight and the label's own first coordinate as
the class constant, against `congruentDissection_corner_balance`'s total of `N`.

This is `lem:census`'s `α`-identity in the form the partition produces it; matching it to
`OrderForcing.vertex_census`'s `ha` needs only the target's corner counts (one apex, two base
corners). -/
theorem census_alpha_sum {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ∑ y ∈ censusLabels, y.1 *
        ((cornerPts D.toDissection).filter (fun v =>
          ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
            ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
            ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ) = y)).card
      = N := by
  classical
  rw [← sum_over_fibers_const (cornerPts D.toDissection) censusLabels _
    (fun v hv => figureVec_mem_censusLabels D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
      hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget hv)
    (fun v => ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card)
    (fun y => y.1) (fun _ _ => rfl)]
  have hbal := congruentDissection_corner_balance D
    (model_corner_dist D hmα hmβ hmγ hαβ hαγ hβγ) 0
    (by rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hα0)
    (by rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hαπ)
    (by rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα]; exact hα2π)
  rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hmα] at hbal
  exact hbal

/-- **The base-`β` target has exactly one apex corner.**  Given that each of the target's corners is
`3α` or `β`, the angle sum `3α + 2β = π` and the irrationality of `α/π` force the split to be one
apex and two base corners — the counts `lem:census` writes as the constants `3` and `0` in its
identities.  Not an extra assumption: two apexes, three apexes, or none each force `α = π/9`. -/
theorem target_corner_counts {N : ℕ} (D : CongruentDissection N) {α β : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α}
      : Finset (Fin 3)).card = 1 := by
  classical
  have hne : β ≠ 3 * α := by
    intro h
    exact hirr ⟨1/9, by rw [h] at hrel; push_cast; linarith⟩
  have hnine : α ≠ (1/9 : ℝ) * Real.pi := by
    intro h; exact hirr ⟨1/9, by push_cast; exact h⟩
  have hsum := Erdos634.Geometry.cornerAngle_sum D.target
  have e0 : (0 : Fin 3) + 1 = 1 := rfl
  have e0' : (0 : Fin 3) + 2 = 2 := rfl
  have e1 : (1 : Fin 3) + 1 = 2 := rfl
  have e1' : (1 : Fin 3) + 2 = 0 := rfl
  have e2 : (2 : Fin 3) + 1 = 0 := rfl
  have e2' : (2 : Fin 3) + 2 = 1 := rfl
  have h0 := htarget 0
  have h1 := htarget 1
  have h2 := htarget 2
  simp only [e0, e0', e1, e1', e2, e2'] at h0 h1 h2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rw [h0, h1, h2] at hsum
  all_goals (
    first
      | (exfalso; apply hnine; linarith)
      | (rw [Finset.card_eq_one]
         refine ⟨0, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
         · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           rw [e0, e0']; exact h0
         · intro k hk
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
           have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
           rcases hall k with rfl | rfl | rfl
           · rfl
           · rw [e1, e1'] at hk; rw [h1] at hk; exact absurd hk hne
           · rw [e2, e2'] at hk; rw [h2] at hk; exact absurd hk hne)
      | (rw [Finset.card_eq_one]
         refine ⟨1, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
         · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           rw [e1, e1']; exact h1
         · intro k hk
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
           have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
           rcases hall k with rfl | rfl | rfl
           · rw [e0, e0'] at hk; rw [h0] at hk; exact absurd hk hne
           · rfl
           · rw [e2, e2'] at hk; rw [h2] at hk; exact absurd hk hne)
      | (rw [Finset.card_eq_one]
         refine ⟨2, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
         · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
           rw [e2, e2']; exact h2
         · intro k hk
           simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
           have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
           rcases hall k with rfl | rfl | rfl
           · rw [e0, e0'] at hk; rw [h0] at hk; exact absurd hk hne
           · rw [e1, e1'] at hk; rw [h1] at hk; exact absurd hk hne
           · rfl))

/-- **Only the apex label has `β`-count zero.**  Among the eight census labels, `(3,0,0)` is the
only one whose middle coordinate is `0`; so a tile vertex with no tile presenting `β` must be one of
the target's own corners, and its corner angle is `3α`. -/
theorem beta_free_is_apex {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ cornerPts D.toDissection)
    (hβcount : ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 0) :
    ∃ k : Fin 3, D.target.pts k = v ∧
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) ≠ β := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
  rcases cornerPts_trichotomy D.toDissection hv with hc | ⟨hfr, hnv⟩ | hint
  · obtain ⟨k, hk⟩ := hc
    refine ⟨k, hk, ?_⟩
    intro hβcorner
    obtain ⟨-, hb, -, -⟩ := Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D
      α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k hβcorner
    rw [hk] at hb
    omega
  · exfalso
    rcases congruentDissection_boundary_figure_at_corner D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ hfr hnv j m hm with
      ⟨-, hb, -⟩ | ⟨-, hb, -⟩ <;> omega
  · exfalso
    rcases congruentDissection_interior_figure_at_corner D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ
      hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr hint j m hm with
      ⟨-, hcase⟩ | ⟨-, hcase⟩
    · rcases hcase with ⟨-, hb, -⟩ | ⟨-, hb, -⟩ <;> omega
    · rcases hcase with ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ <;> omega

/-- **The apex class has exactly one point.**  Combining `target_corner_counts` (one target corner
carries `3α`) with `beta_free_is_apex` (only the apex label has `β`-count `0`) and
`TileAt.congruentDissection_apex_counts` (the apex carries `(3,0,0)`): the fibre of the label
`(3,0,0)` in `cornerPts` is the single apex point.  This is the constant `3` in `lem:census`'s
`α`-identity. -/
theorem apex_fibre_card {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (3, 0, 0))).card = 1 := by
  classical
  obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp (target_corner_counts D hrel hirr htarget)
  have hmem₀ : cornerAngle (D.target.pts (k₀ + 1)) (D.target.pts k₀) (D.target.pts (k₀ + 2))
      = 3 * α := by
    have : k₀ ∈ ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
        = 3 * α} : Finset (Fin 3)) := by rw [hk₀]; exact Finset.mem_singleton_self k₀
    simpa using this
  obtain ⟨ha, hb, hc, -⟩ := Erdos634.Geometry.Dissection.congruentDissection_apex_counts D
    α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k₀ hmem₀
  -- the apex is a tile vertex, since some tile presents `α` there
  have hapexmem : D.target.pts k₀ ∈ cornerPts D.toDissection := by
    have hpos : 0 < ({i | (D.tile i).localAngle (D.target.pts k₀) = α} : Finset (Fin N)).card := by
      rw [ha]; norm_num
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) hi hα0 hαπ hα2π
    rw [← hm]; exact mem_cornerPts D.toDissection i m
  refine Finset.card_eq_one.mpr ⟨D.target.pts k₀, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · simp only [Finset.mem_filter]
    exact ⟨hapexmem, by rw [ha, hb, hc]⟩
  · intro v hv
    obtain ⟨hvmem, hvlab⟩ := Finset.mem_filter.mp hv
    have hβ0' : ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 0 := by
      have := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) hvlab
      simpa using this
    obtain ⟨k, hk, hkne⟩ := beta_free_is_apex D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
      hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr hvmem hβ0'
    have hk3 : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α :=
      (htarget k).resolve_right hkne
    have : k ∈ ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
        = 3 * α} : Finset (Fin 3)) := by simpa using hk3
    rw [hk₀, Finset.mem_singleton] at this
    rw [← hk, this]

/-- **The base-corner class has exactly two points.**  The discriminator is `α`-count `0` together
with `γ`-count `0`: among the eight labels those two conditions hold only for `(0,1,0)`.  With
`target_corner_counts` giving one apex, the other two target corners carry `β`, and the target's
vertices are distinct — so the fibre has two points.  This is the constant `2` in `lem:census`'s
`β`-identity. -/
theorem base_fibre_card {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (0, 1, 0))).card = 2 := by
  classical
  have hne : β ≠ 3 * α := fun h => hirr ⟨1/9, by rw [h] at hrel; push_cast; linarith⟩
  -- the two base corners, as a `Finset (Fin 3)` of size two
  have hsplit : ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β} : Finset (Fin 3)).card = 2 := by
    have hfil : ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
        (D.target.pts (k + 2)) = β} : Finset (Fin 3))
        = Finset.univ.filter (fun k => ¬ (cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
          (D.target.pts (k + 2)) = 3 * α)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h h3; exact hne (h ▸ h3)
      · intro h; exact (htarget k).resolve_left h
    have hcard := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin 3)))
      (p := fun k => cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
        (D.target.pts (k + 2)) = 3 * α)
    rw [hfil]
    have h1 := target_corner_counts D hrel hirr htarget
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  -- the fibre is the image of those two corners
  have himg : ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ) = (0, 1, 0)))
      = ({k | cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
          (D.target.pts (k + 2)) = β} : Finset (Fin 3)).image D.target.pts := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hvmem, hvlab⟩
      have hαc : ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 0 := by
        have := congrArg (fun p : ℕ × ℕ × ℕ => p.1) hvlab; simpa using this
      have hγc : ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0 := by
        have := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hvlab; simpa using this
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hvmem
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
      rcases cornerPts_trichotomy D.toDissection hvmem with hc | ⟨hfr, hnv⟩ | hint
      · obtain ⟨k, hk⟩ := hc
        refine ⟨k, ?_, hk⟩
        rcases htarget k with h3 | hb
        · exfalso
          obtain ⟨ha, -, -, -⟩ := Erdos634.Geometry.Dissection.congruentDissection_apex_counts D
            α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k h3
          rw [hk] at ha; omega
        · exact hb
      · exfalso
        rcases congruentDissection_boundary_figure_at_corner D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
          hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ hfr hnv j m hm with
          ⟨ha, -, -⟩ | ⟨ha, -, -⟩ <;> omega
      · exfalso
        rcases congruentDissection_interior_figure_at_corner D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ
          hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr hint j m hm with
          ⟨-, hcase⟩ | ⟨-, hcase⟩
        · rcases hcase with ⟨ha, -, -⟩ | ⟨ha, -, -⟩ <;> omega
        · rcases hcase with ⟨ha, -, hc⟩ | ⟨ha, -, hc⟩ | ⟨ha, -, hc⟩ | ⟨ha, -, hc⟩ <;> omega
    · rintro ⟨k, hkβ, rfl⟩
      obtain ⟨ha, hb, hc, -⟩ :=
        Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D
        α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ k
        (by simpa using hkβ)
      refine ⟨?_, by rw [ha, hb, hc]⟩
      have hpos : 0 < ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card := by
        rw [hb]; norm_num
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨m', hm'⟩ := vertex_of_localAngle_corner (D.tile i) hi hβ0 hβπ hβ2π
      rw [← hm']; exact mem_cornerPts D.toDissection i m'
  rw [himg, Finset.card_image_of_injective _ D.target.indep.injective, hsplit]

/-- **The `β`-identity of the census, as a sum over the eight classes.** -/
theorem census_beta_sum {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ∑ y ∈ censusLabels, y.2.1 *
        ((cornerPts D.toDissection).filter (fun v =>
          ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
            ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
            ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ) = y)).card
      = N := by
  classical
  rw [← sum_over_fibers_const (cornerPts D.toDissection) censusLabels _
    (fun v hv => figureVec_mem_censusLabels D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
      hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget hv)
    (fun v => ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card)
    (fun y => y.2.1) (fun _ _ => rfl)]
  have hbal := congruentDissection_corner_balance D
    (model_corner_dist D hmα hmβ hmγ hαβ hαγ hβγ) 1
    (by rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, hmβ]
        exact hβ0)
    (by rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, hmβ]
        exact hβπ)
    (by rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, hmβ]
        exact hβ2π)
  rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, hmβ] at hbal
  exact hbal

/-- **The `γ`-identity of the census, as a sum over the eight classes.** -/
theorem census_gamma_sum {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ∑ y ∈ censusLabels, y.2.2 *
        ((cornerPts D.toDissection).filter (fun v =>
          ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
            ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
            ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ) = y)).card
      = N := by
  classical
  rw [← sum_over_fibers_const (cornerPts D.toDissection) censusLabels _
    (fun v hv => figureVec_mem_censusLabels D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
      hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget hv)
    (fun v => ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card)
    (fun y => y.2.2) (fun _ _ => rfl)]
  have hbal := congruentDissection_corner_balance D
    (model_corner_dist D hmα hmβ hmγ hαβ hαγ hβγ) 2
    (by rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hmγ]
        exact hγ0)
    (by rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hmγ]
        exact hγπ)
    (by rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hmγ]
        exact hγ2π)
  rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hmγ] at hbal
  exact hbal

/-- **`lem:census`'s conclusion, for a real congruent dissection.**  The `{β,3γ}` class is mandatory
and each `γ`-poor figure demands one more:

`v₁ = 1 + n₂ + v₃ + 2·v₄`

with the classes named by their multiplicity vectors — `v₁ = (0,1,3)`, `n₂ = (3,2,0)`,
`v₃ = (4,3,1)`, `v₄ = (6,4,0)`.  The three class-sum identities feed
`OrderForcing.vertex_census` after the apex and base-corner fibres are replaced by `1` and `2`. -/
theorem congruentDissection_vertex_census {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (0, 1, 3))).card
      = 1 + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (3, 2, 0))).card
        + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (4, 3, 1))).card
        + 2 * ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (6, 4, 0))).card := by
  classical
  have ha := census_alpha_sum D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
    hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  have hb := census_beta_sum D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
    hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  have hg := census_gamma_sum D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
    hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  have hap := apex_fibre_card D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
    hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  have hba := base_fibre_card D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
    hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  simp only [censusLabels, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, Prod.mk.injEq] at ha hb hg ⊢
  simp only [Prod.mk.injEq] at hap hba
  norm_num at ha hb hg hap hba ⊢
  omega

/-- **The climber is mandatory**, for a real congruent dissection: `v₁ ≥ 1`, i.e. some point of the
tiling carries the `{β,3γ}` figure.  `lem:census`'s "in particular" clause, immediate from the
identity. -/
theorem congruentDissection_climber_mandatory {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    1 ≤ ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (0, 1, 3))).card := by
  have h := congruentDissection_vertex_census D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0
    hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  omega

end Erdos634.Geometry
