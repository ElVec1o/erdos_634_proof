import Erdos634.ThickPrefixACB

/-!
# Right-leg junction escapes at thick base-`β` members, **parametric in `f` and in the junction distance `D`**

Erdős #634, base-`β` branch, thick family `e = f − 1`, `f ≥ 6` (`N = 83` is `f = 6`).  Same model as
`ThickPrefixACB`: tile `(a,b,c) = (f² − f, 2f − 1, f²)`, target `tgt f = (0,0)–(L,0)–(L/2,H)`,
`L = (f−1)(2f² + 2f − 1)`, `H = (2f−1)√D/2`, `D = 3f² + 2f − 1` (= `baseBetaTarget (f−1) f`).

## Provenance and the reproduction verdict (2026-09-12, `private/ROOM/attack/report_rightleg.md`)

`report_residue.md` §3 names a mechanism **M2** at `(2,3)`: at the base junctions `(31,0)` and `(40,0)`
of the word `aabbcca`, the placements of the exact constructor escape through the **right** leg.
Read exactly from the saved tree:

* at `(40,0)` (distance `a` from the right corner) the free sector starts on the ray at angle `γ`,
  which is the `b`-edge of the corner tile; that ray meets the leg at distance exactly `b`, so
  `a`- and `c`-edges along it escape.  This is the **mirror of the corner configuration `{T1}`** of
  `ThickPrefixACB` (node `N1`, a different ray), a reproduction; nothing is formalised for it.
* at `(31,0)` (distance `a + c` from the right corner) the free sector starts on the ray at angle
  `α` from `+x`; the four `α/β` candidates all carry the `c`-edge either **along the `α`-ray**,
  **along the `2α`-ray**, or **along the `(α+β)`-ray**, and each such `c`-edge escapes.  These are
  not among `ThickPrefixACB`'s 23 facts (its `(a+c,0)` node uses the base ray).  They are the
  parametric object formalised here.

## The parametric lemma

A ray from the base point `(L − D, 0)` at angle `θ` meets the right leg (interior angle `β` at
`(L,0)`) at distance `ρ = D·sin β / sin(θ + β)`; an edge of length `s` along it escapes iff `D < D₀ :=
s·sin(θ+β)/sin β`.  In coordinates this is one affine inequality (`ray_escapes_right`).  For the tile's
`c`-edge (`s = f²`) at `e = f − 1` the thresholds are **exact rational functions of `f`**:

* `θ = α` and `θ = 2α` (the same threshold, because `2α + β = γ` and `α + β = π − γ`):
  `D₀ = f⁴/(2f − 1)`  (`= 1296/11 ≈ 117.8` at `f = 6`);
* `θ = α + β`: `D₀ = f(f−1)(f² + 2f − 1)/(2f − 1)`  (`= 1410/11 ≈ 128.2` at `f = 6`).

In `t = e/f` these read `D/f² < 1/(1−t²)` and `D/f² < t(2−t²)/(1−t²)`; at the junction `D = a + c`
both reduce to `1 − t − t² < 0`, i.e. `t > (√5−1)/2`, satisfied by every member from `(2,3)` on.

## What is proved (all for real `f ≥ 6`, real `D`)

* `not_mem_tgt_of_right`, `ray_escapes_right` — the right-leg escape test, general in `(D, s, θ)`.
* `cA, sA, cB, sB` (cos/sin of `α`, `β`, the corpus values `cos α = (2f²−e²)/2f²`, `cos β = eN/2f³`),
  `c2A, s2A` (double angle), `cAB, sAB` (`= (f−1)/2f`, `√D/2f`) with the addition formulae
  `cAB_eq`, `sAB_eq` proved from `rr² = D`.
* Four explicit candidate `Tri`s at the junction `(L − D, 0)` with the ray at angle `α`
  (`cJ_alpha_cb`, `cJ_alpha_bc`, `cJ_beta_ca`, `cJ_beta_ac`, frames recorded), and their escape facts
  `esc_*` under the exact threshold hypotheses `hD : D < D0a f` / `hD : D < D0ab f`; `blocking_J`
  collects them.
* **Non-vacuity**: `witness_83` — at `f = 6`, `D = 66 = a + c` (the `c|c` junction `x = 349` of the
  `N = 83` residue word `accaabbbbbbbbbbbacca`), both thresholds hold, the junction lies in the target,
  and all four escapes are instances.

## What is **not** proved

Nothing about a dissection.  The escape of a candidate kills a search node only together with the
placement-rule completeness (H7) and, at `(31,0)`, with the *overlap* rejection of the two `γ`
placements, which is state-dependent and not stated here.  The word-level consequence found in the
report — 14 of the 19 596 `N = 83` residue words die — uses these escapes only to pin the orientation
of the end blocks; the propagation along the base is the corpus fact `Inflation.orient_monotone`
(`RunOrientation.corner_anchored_run_all_BG`), not re-proved here.

No `sorry`; axioms are the standard three.
-/

namespace Erdos634.ThickJunctionEscape

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.ThickPrefixACB

/-! ## 1. The right leg -/

/-- **Beyond the right leg is outside the target.**  The right leg carries the functional
`H·(L − x) − (L/2)·y`, nonnegative on the target. -/
theorem not_mem_tgt_of_right {f : ℝ} (hf : 6 ≤ f) {x y : ℝ}
    (h : 0 < Lq f / 2 * y - Hq f * (Lq f - x)) : mkPt x y ∉ (tgt f hf).carrier := by
  intro hm
  have hL := Lq_pos hf; have hH := Hq_pos hf
  have hb : ∀ z ∈ (tgt f hf).carrier, 0 ≤ lineFun (Lq f) 0 (Lq f / 2) (Hq f) z := by
    refine ge_of_forall_pts_ge _ ?_
    intro k
    fin_cases k <;>
      simp [tgt, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
      nlinarith [mul_pos hL hH]
  have := hb _ hm
  simp only [lineFun_apply, mkPt_zero, mkPt_one] at this
  nlinarith

/-- **The parametric escape.**  The point at distance `s` along the ray from `(L − D, 0)` in the
direction `(cθ, sθ)` lies beyond the right leg whenever `H·D < s·((L/2)·sθ + H·cθ)`, i.e.
`D < s·sin(θ+β)/sin β`. -/
theorem ray_escapes_right {f : ℝ} (hf : 6 ≤ f) {D s cθ sθ : ℝ}
    (h : Hq f * D < s * (Lq f / 2 * sθ + Hq f * cθ)) :
    mkPt (Lq f - D + s * cθ) (s * sθ) ∉ (tgt f hf).carrier := by
  apply not_mem_tgt_of_right hf
  have e : Lq f / 2 * (s * sθ) - Hq f * (Lq f - (Lq f - D + s * cθ)) =
      s * (Lq f / 2 * sθ + Hq f * cθ) - Hq f * D := by ring
  rw [e]; linarith

/-- A base point at distance `0 ≤ D ≤ L` from the right corner lies in the target. -/
theorem junction_mem {f : ℝ} (hf : 6 ≤ f) {D : ℝ} (h0 : 0 ≤ D) (hL : D ≤ Lq f) :
    mkPt (Lq f - D) 0 ∈ (tgt f hf).carrier := by
  have hH := Hq_pos hf
  refine mem_tgt hf le_rfl ?_ ?_ <;> nlinarith [mul_nonneg hH.le h0, mul_nonneg hH.le (sub_nonneg.mpr hL)]

/-! ## 2. The angles at `e = f − 1` -/

/-- `cos α = (2f² − e²)/(2f²)` at `e = f − 1`. -/
noncomputable def cA (f : ℝ) : ℝ := (f^2 + 2*f - 1) / (2*f^2)
/-- `sin α = e√D/(2f²)`. -/
noncomputable def sA (f : ℝ) : ℝ := (f - 1) / (2*f^2) * rr f
/-- `cos β = eN/(2f³)`. -/
noncomputable def cB (f : ℝ) : ℝ := (f - 1) * (2*f^2 + 2*f - 1) / (2*f^3)
/-- `sin β = b√D/(2f³)`. -/
noncomputable def sB (f : ℝ) : ℝ := (2*f - 1) / (2*f^3) * rr f
/-- `cos 2α`, `sin 2α`. -/
noncomputable def c2A (f : ℝ) : ℝ := 2 * cA f ^ 2 - 1
noncomputable def s2A (f : ℝ) : ℝ := 2 * sA f * cA f
/-- `cos(α+β) = (f−1)/(2f)` (`= −cos γ`), `sin(α+β) = √D/(2f)`. -/
noncomputable def cAB (f : ℝ) : ℝ := (f - 1) / (2*f)
noncomputable def sAB (f : ℝ) : ℝ := rr f / (2*f)

theorem cA_sq_add_sA_sq {f : ℝ} (hf : 6 ≤ f) : cA f ^ 2 + sA f ^ 2 = 1 := by
  have hf0 : f ≠ 0 := by intro h; linarith
  unfold cA sA
  have h2 := rr_sq hf
  field_simp
  rw [h2]; unfold Dq; ring

theorem cB_sq_add_sB_sq {f : ℝ} (hf : 6 ≤ f) : cB f ^ 2 + sB f ^ 2 = 1 := by
  have hf0 : f ≠ 0 := by intro h; linarith
  unfold cB sB
  have h2 := rr_sq hf
  field_simp
  rw [h2]; unfold Dq; ring

/-- The addition formula: `cAB` really is `cos(α+β)`. -/
theorem cAB_eq {f : ℝ} (hf : 6 ≤ f) : cAB f = cA f * cB f - sA f * sB f := by
  have hf0 : f ≠ 0 := by intro h; linarith
  have h2 := rr_sq hf
  unfold cAB cA cB sA sB
  field_simp
  ring_nf
  rw [h2]; unfold Dq; ring

/-- The addition formula: `sAB` really is `sin(α+β)`. -/
theorem sAB_eq {f : ℝ} (hf : 6 ≤ f) : sAB f = sA f * cB f + cA f * sB f := by
  have hf0 : f ≠ 0 := by intro h; linarith
  unfold sAB cA cB sA sB
  field_simp
  ring

/-! ## 3. The thresholds -/

/-- `D₀` for a `c`-edge along the `α`-ray or the `2α`-ray. -/
noncomputable def D0a (f : ℝ) : ℝ := f^4 / (2*f - 1)
/-- `D₀` for a `c`-edge along the `(α+β)`-ray. -/
noncomputable def D0ab (f : ℝ) : ℝ := f * (f - 1) * (f^2 + 2*f - 1) / (2*f - 1)

theorem key_alpha {f : ℝ} (hf : 6 ≤ f) :
    f^2 * (Lq f / 2 * sA f + Hq f * cA f) = rr f * (f^4 / 2) := by
  have hf0 : f ≠ 0 := by intro h; linarith
  unfold Lq Hq sA cA; field_simp; ring

theorem key_2alpha {f : ℝ} (hf : 6 ≤ f) :
    f^2 * (Lq f / 2 * s2A f + Hq f * c2A f) = rr f * (f^4 / 2) := by
  have hf0 : f ≠ 0 := by intro h; linarith
  unfold Lq Hq s2A c2A sA cA; field_simp; ring_nf

theorem key_alphabeta {f : ℝ} (hf : 6 ≤ f) :
    f^2 * (Lq f / 2 * sAB f + Hq f * cAB f) = rr f * (f * (f - 1) * (f^2 + 2*f - 1) / 2) := by
  have hf0 : f ≠ 0 := by intro h; linarith
  unfold Lq Hq sAB cAB; field_simp; ring

/-- **`c` along the `α`-ray escapes below `D0a`.** -/
theorem esc_c_alpha {f : ℝ} (hf : 6 ≤ f) {D : ℝ} (hD : D < D0a f) :
    mkPt (Lq f - D + f^2 * cA f) (f^2 * sA f) ∉ (tgt f hf).carrier := by
  apply ray_escapes_right hf
  rw [key_alpha hf]; unfold Hq
  have hD' : D * (2*f - 1) < f^4 := (lt_div_iff₀ (by linarith)).mp hD
  nlinarith [mul_pos (rr_pos hf) (sub_pos.mpr hD')]

/-- **`c` along the `2α`-ray escapes below `D0a`.** -/
theorem esc_c_2alpha {f : ℝ} (hf : 6 ≤ f) {D : ℝ} (hD : D < D0a f) :
    mkPt (Lq f - D + f^2 * c2A f) (f^2 * s2A f) ∉ (tgt f hf).carrier := by
  apply ray_escapes_right hf
  rw [key_2alpha hf]; unfold Hq
  have hD' : D * (2*f - 1) < f^4 := (lt_div_iff₀ (by linarith)).mp hD
  nlinarith [mul_pos (rr_pos hf) (sub_pos.mpr hD')]

/-- **`c` along the `(α+β)`-ray escapes below `D0ab`.** -/
theorem esc_c_alphabeta {f : ℝ} (hf : 6 ≤ f) {D : ℝ} (hD : D < D0ab f) :
    mkPt (Lq f - D + f^2 * cAB f) (f^2 * sAB f) ∉ (tgt f hf).carrier := by
  apply ray_escapes_right hf
  rw [key_alphabeta hf]; unfold Hq
  have hD' : D * (2*f - 1) < f * (f - 1) * (f^2 + 2*f - 1) := (lt_div_iff₀ (by linarith)).mp hD
  nlinarith [mul_pos (rr_pos hf) (sub_pos.mpr hD')]

/-! ## 4. The four candidates at a junction with the ray at angle `α` -/

theorem sA_pos {f : ℝ} (hf : 6 ≤ f) : 0 < sA f := by
  unfold sA; exact mul_pos (div_pos (by linarith) (by positivity)) (rr_pos hf)
theorem sB_pos {f : ℝ} (hf : 6 ≤ f) : 0 < sB f := by
  unfold sB; exact mul_pos (div_pos (by linarith) (by positivity)) (rr_pos hf)

/-- `α(c on ray, b off)`: vertices `J`, `J + c·(cos α, sin α)`, `J + b·(cos 2α, sin 2α)`. -/
theorem det_alpha_cb {f : ℝ} (hf : 6 ≤ f) (D : ℝ) :
    det3 (Lq f - D) 0 (Lq f - D + f^2 * cA f) (f^2 * sA f)
      (Lq f - D + (2*f - 1) * c2A f) ((2*f - 1) * s2A f) ≠ 0 := by
  have h : det3 (Lq f - D) 0 (Lq f - D + f^2 * cA f) (f^2 * sA f)
      (Lq f - D + (2*f - 1) * c2A f) ((2*f - 1) * s2A f) = f^2 * (2*f - 1) * sA f := by
    unfold det3 c2A s2A; ring
  rw [h]; exact ne_of_gt (mul_pos (mul_pos (by positivity) (by linarith)) (sA_pos hf))

noncomputable def cJ_alpha_cb (f : ℝ) (hf : 6 ≤ f) (D : ℝ) : Tri :=
  mkTri (Lq f - D) 0 (Lq f - D + f^2 * cA f) (f^2 * sA f)
    (Lq f - D + (2*f - 1) * c2A f) ((2*f - 1) * s2A f) (det_alpha_cb hf D)

/-- `α(b on ray, c off)`: vertices `J`, `J + b·(cos α, sin α)`, `J + c·(cos 2α, sin 2α)`. -/
theorem det_alpha_bc {f : ℝ} (hf : 6 ≤ f) (D : ℝ) :
    det3 (Lq f - D) 0 (Lq f - D + (2*f - 1) * cA f) ((2*f - 1) * sA f)
      (Lq f - D + f^2 * c2A f) (f^2 * s2A f) ≠ 0 := by
  have h : det3 (Lq f - D) 0 (Lq f - D + (2*f - 1) * cA f) ((2*f - 1) * sA f)
      (Lq f - D + f^2 * c2A f) (f^2 * s2A f) = f^2 * (2*f - 1) * sA f := by
    unfold det3 c2A s2A; ring
  rw [h]; exact ne_of_gt (mul_pos (mul_pos (by positivity) (by linarith)) (sA_pos hf))

noncomputable def cJ_alpha_bc (f : ℝ) (hf : 6 ≤ f) (D : ℝ) : Tri :=
  mkTri (Lq f - D) 0 (Lq f - D + (2*f - 1) * cA f) ((2*f - 1) * sA f)
    (Lq f - D + f^2 * c2A f) (f^2 * s2A f) (det_alpha_bc hf D)

/-- The cross product of the `α`-ray and the `(α+β)`-ray is `sin β`. -/
theorem cross_alpha_alphabeta {f : ℝ} (hf : 6 ≤ f) : cA f * sAB f - sA f * cAB f = sB f := by
  have hf0 : f ≠ 0 := by intro h; linarith
  unfold cA sA cAB sAB sB; field_simp; ring

/-- `β(c on ray, a off)`: vertices `J`, `J + c·(cos α, sin α)`, `J + a·(cos(α+β), sin(α+β))`. -/
theorem det_beta_ca {f : ℝ} (hf : 6 ≤ f) (D : ℝ) :
    det3 (Lq f - D) 0 (Lq f - D + f^2 * cA f) (f^2 * sA f)
      (Lq f - D + (f^2 - f) * cAB f) ((f^2 - f) * sAB f) ≠ 0 := by
  have h : det3 (Lq f - D) 0 (Lq f - D + f^2 * cA f) (f^2 * sA f)
      (Lq f - D + (f^2 - f) * cAB f) ((f^2 - f) * sAB f) =
      f^2 * (f^2 - f) * (cA f * sAB f - sA f * cAB f) := by
    unfold det3; ring
  rw [h, cross_alpha_alphabeta hf]
  exact ne_of_gt (mul_pos (mul_pos (by positivity) (by nlinarith)) (sB_pos hf))

noncomputable def cJ_beta_ca (f : ℝ) (hf : 6 ≤ f) (D : ℝ) : Tri :=
  mkTri (Lq f - D) 0 (Lq f - D + f^2 * cA f) (f^2 * sA f)
    (Lq f - D + (f^2 - f) * cAB f) ((f^2 - f) * sAB f) (det_beta_ca hf D)

/-- `β(a on ray, c off)`: vertices `J`, `J + a·(cos α, sin α)`, `J + c·(cos(α+β), sin(α+β))`. -/
theorem det_beta_ac {f : ℝ} (hf : 6 ≤ f) (D : ℝ) :
    det3 (Lq f - D) 0 (Lq f - D + (f^2 - f) * cA f) ((f^2 - f) * sA f)
      (Lq f - D + f^2 * cAB f) (f^2 * sAB f) ≠ 0 := by
  have h : det3 (Lq f - D) 0 (Lq f - D + (f^2 - f) * cA f) ((f^2 - f) * sA f)
      (Lq f - D + f^2 * cAB f) (f^2 * sAB f) =
      f^2 * (f^2 - f) * (cA f * sAB f - sA f * cAB f) := by
    unfold det3; ring
  rw [h, cross_alpha_alphabeta hf]
  exact ne_of_gt (mul_pos (mul_pos (by positivity) (by nlinarith)) (sB_pos hf))

noncomputable def cJ_beta_ac (f : ℝ) (hf : 6 ≤ f) (D : ℝ) : Tri :=
  mkTri (Lq f - D) 0 (Lq f - D + (f^2 - f) * cA f) ((f^2 - f) * sA f)
    (Lq f - D + f^2 * cAB f) (f^2 * sAB f) (det_beta_ac hf D)

/-- Frames: vertex `0` is the junction `(L − D, 0)`, vertex `1` lies on the `α`-ray. -/
theorem frame_J {f : ℝ} (hf : 6 ≤ f) (D : ℝ) :
    (cJ_alpha_cb f hf D).pts 0 = mkPt (Lq f - D) 0 ∧ (cJ_alpha_bc f hf D).pts 0 = mkPt (Lq f - D) 0 ∧
    (cJ_beta_ca f hf D).pts 0 = mkPt (Lq f - D) 0 ∧ (cJ_beta_ac f hf D).pts 0 = mkPt (Lq f - D) 0 ∧
    (cJ_alpha_cb f hf D).pts 1 = mkPt (Lq f - D + f^2 * cA f) (f^2 * sA f) ∧
    (cJ_beta_ac f hf D).pts 2 = mkPt (Lq f - D + f^2 * cAB f) (f^2 * sAB f) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 5. The escapes -/

theorem esc_cJ_alpha_cb {f : ℝ} (hf : 6 ≤ f) {D : ℝ} (hD : D < D0a f) :
    ¬ ((cJ_alpha_cb f hf D).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hv : (cJ_alpha_cb f hf D).pts 1 ∈ (tgt f hf).carrier :=
    h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  exact esc_c_alpha hf hD hv

theorem esc_cJ_alpha_bc {f : ℝ} (hf : 6 ≤ f) {D : ℝ} (hD : D < D0a f) :
    ¬ ((cJ_alpha_bc f hf D).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hv : (cJ_alpha_bc f hf D).pts 2 ∈ (tgt f hf).carrier :=
    h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  exact esc_c_2alpha hf hD hv

theorem esc_cJ_beta_ca {f : ℝ} (hf : 6 ≤ f) {D : ℝ} (hD : D < D0a f) :
    ¬ ((cJ_beta_ca f hf D).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hv : (cJ_beta_ca f hf D).pts 1 ∈ (tgt f hf).carrier :=
    h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  exact esc_c_alpha hf hD hv

theorem esc_cJ_beta_ac {f : ℝ} (hf : 6 ≤ f) {D : ℝ} (hD : D < D0ab f) :
    ¬ ((cJ_beta_ac f hf D).carrier ⊆ (tgt f hf).carrier) := by
  intro h
  have hv : (cJ_beta_ac f hf D).pts 2 ∈ (tgt f hf).carrier :=
    h (subset_convexHull ℝ _ (Set.mem_range_self 2))
  exact esc_c_alphabeta hf hD hv

/-- **The junction blocking fact.**  At a base junction at distance `D` from the right corner whose
free sector starts on the `α`-ray, every `α`- and `β`-placement escapes through the right leg as soon
as `D < D0a f` and `D < D0ab f` (`D0a < D0ab` for `f ≥ 6`, so the first threshold is the binding one). -/
theorem blocking_J {f : ℝ} (hf : 6 ≤ f) {D : ℝ} (hDa : D < D0a f) (hDab : D < D0ab f) :
    ¬ ((cJ_alpha_cb f hf D).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cJ_alpha_bc f hf D).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cJ_beta_ca f hf D).carrier ⊆ (tgt f hf).carrier) ∧
    ¬ ((cJ_beta_ac f hf D).carrier ⊆ (tgt f hf).carrier) :=
  ⟨esc_cJ_alpha_cb hf hDa, esc_cJ_alpha_bc hf hDa, esc_cJ_beta_ca hf hDa, esc_cJ_beta_ac hf hDab⟩

theorem D0a_lt_D0ab {f : ℝ} (hf : 6 ≤ f) : D0a f < D0ab f := by
  unfold D0a D0ab
  rw [div_lt_div_iff_of_pos_right (by linarith)]
  nlinarith [sq_nonneg (f - 1), sq_nonneg f]

/-! ## 6. Non-vacuity at `N = 83` -/

/-- `f = 6`, `D = 66 = a + c`: the `c|c` junction `x = 349` of the residue word `accaabbbbbbbbbbbacca`
(`L = 415`).  Both thresholds hold (`66 < 1296/11 < 1410/11`), the junction is in the target, and
all four candidate placements escape. -/
theorem witness_83 :
    (66 : ℝ) < D0a 6 ∧ (66 : ℝ) < D0ab 6 ∧
    mkPt (Lq 6 - 66) 0 ∈ (tgt 6 (le_refl 6)).carrier ∧
    ¬ ((cJ_alpha_cb 6 (le_refl 6) 66).carrier ⊆ (tgt 6 (le_refl 6)).carrier) ∧
    ¬ ((cJ_alpha_bc 6 (le_refl 6) 66).carrier ⊆ (tgt 6 (le_refl 6)).carrier) ∧
    ¬ ((cJ_beta_ca 6 (le_refl 6) 66).carrier ⊆ (tgt 6 (le_refl 6)).carrier) ∧
    ¬ ((cJ_beta_ac 6 (le_refl 6) 66).carrier ⊆ (tgt 6 (le_refl 6)).carrier) := by
  have ha : (66 : ℝ) < D0a 6 := by unfold D0a; norm_num
  have hab : (66 : ℝ) < D0ab 6 := by unfold D0ab; norm_num
  refine ⟨ha, hab, junction_mem (le_refl 6) (by norm_num) (by unfold Lq; norm_num), ?_⟩
  exact blocking_J (le_refl 6) ha hab

/-- The junction `x = 349` is `L − 66` at `f = 6`. -/
theorem junction_coord : Lq 6 - 66 = 349 := by unfold Lq; norm_num

end Erdos634.ThickJunctionEscape

#print axioms Erdos634.ThickJunctionEscape.blocking_J
#print axioms Erdos634.ThickJunctionEscape.witness_83
#print axioms Erdos634.ThickJunctionEscape.cAB_eq
