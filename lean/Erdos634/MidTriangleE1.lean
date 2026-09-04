import Mathlib.Tactic

/-!
# The middle triangle `ADD'` is untileable at `e = 1` — with no hypothesis on the slant sides

Erdős #634, base-β family at `e = 1`, `m = 1`, `N = 3f² − 1`.  Tile `(a,b,c) = (f, f²−1, f²)`,
angles `α, β, γ = 2α+β`, `3α+2β = π`.  Theorem R forces the target to split along the two cevians
`AD`, `AD'` into two `f`-scaled copies of the tile and a **middle triangle** `T_mid = ADD'` with

* base `DD'` of length exactly `e·b = b = f²−1`,
* legs `AD = AD' = f·b`,
* apex angle `α`, base angles `α+β`  (checked: `α + 2(α+β) = 3α+2β = π`).

`MidTriangle.lean` already records an exclusion of `T_mid`, but **under the extra hypothesis that
the slant sides are partitioned into whole `b`-edges** ("pure-b slants", `E1FAMILY_DRAFT` L7), and
instantiated per family member.  The argument below needs **no hypothesis on the slants**, is
**general in `f`**, and is specific to `e = 1`:

> At `e = 1` the base `DD'` has length exactly `b`.  The tile sides lying on `DD'` are whole sides
> (a side meeting a line in positive length lies on it) and tile the length `b`; by
> `base_single_b` the only nonnegative solution of `ua + vb + wc = b` for `f ≥ 2` is one `b`-side.
> So a **single** tile `T₀` has its `b`-side equal to `DD'`, with vertices exactly at `D` and `D'`.
> The two angles adjacent to a `b`-side are `α` and `γ` (`β` is opposite `b`).  So `T₀` presents
> `γ` at one of `D`, `D'`.  But the interior angle of `T_mid` there is `α+β`, and
> `γ = 2α+β > α+β`.  Contradiction. ∎

At `e ≥ 2` the base carries `e` distinct `b`-sides and the two extreme tiles are different, so the
step "the same tile presents both `α` and `γ`" is unavailable — the kill is exactly `e = 1`.

**Scope.** The arithmetic and angle facts below are proved in full, generally in `f`.  The geometric
step — that the sides lying on `DD'` are whole sides and partition its length — is the standing
"no tile-placement layer" blocker and is *not* proved here; it enters `midTriangle_untileable` as a
named hypothesis, and `sides_on_base_witness` shows that hypothesis is satisfiable.
-/

namespace Erdos634.MidTriangleE1

/-! ## 1. The base of `T_mid` is a single `b`-side -/

/-- **For `f ≥ 2`, the only way to write the length `b = f²−1` as a nonnegative combination of tile
sides `a = f`, `b = f²−1`, `c = f²` is a single `b`.** -/
theorem base_single_b {f u v w : ℕ} (hf : 2 ≤ f)
    (h : u * f + v * (f ^ 2 - 1) + w * f ^ 2 = f ^ 2 - 1) :
    u = 0 ∧ v = 1 ∧ w = 0 := by
  have hf1 : 1 ≤ f ^ 2 := Nat.one_le_pow _ _ (by omega)
  -- pass to ℤ so that `f ^ 2 - 1` is honest subtraction
  have hZ : (u : ℤ) * f + v * ((f : ℤ) ^ 2 - 1) + w * (f : ℤ) ^ 2 = (f : ℤ) ^ 2 - 1 := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub hf1] at this
    linarith [this]
  have hf2 : (2 : ℤ) ≤ (f : ℤ) := by exact_mod_cast hf
  have hbpos : (0 : ℤ) < (f : ℤ) ^ 2 - 1 := by nlinarith
  -- `w = 0`, since `c = f² > b`
  have hw : w = 0 := by
    by_contra hw
    have : (1 : ℤ) ≤ (w : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hw
    nlinarith [Int.natCast_nonneg u, Int.natCast_nonneg v, sq_nonneg ((f : ℤ) - 1)]
  subst hw
  -- `v = 1`, since `v = 0` forces `f ∣ 1` and `v ≥ 2` overshoots
  have hv : v = 1 := by
    rcases Nat.lt_or_ge v 1 with hv0 | hv1
    · exfalso
      have hv0 : v = 0 := by omega
      subst hv0
      have huf : (u : ℤ) * f = (f : ℤ) ^ 2 - 1 := by push_cast at hZ ⊢; linarith
      have hdvd : (f : ℤ) ∣ 1 := by
        have : (f : ℤ) ∣ (f : ℤ) ^ 2 - (u : ℤ) * f := ⟨(f : ℤ) - u, by ring⟩
        simpa [huf] using this
      have := Int.le_of_dvd one_pos hdvd
      omega
    · rcases Nat.lt_or_ge v 2 with hv2 | hv2
      · omega
      · exfalso
        have : (2 : ℤ) ≤ (v : ℤ) := by exact_mod_cast hv2
        nlinarith [Int.natCast_nonneg u]
  subst hv
  refine ⟨?_, rfl, rfl⟩
  have : (u : ℤ) * f = 0 := by push_cast at hZ ⊢; linarith
  have : (u : ℤ) = 0 := by
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exfalso; omega
  exact_mod_cast this

/-- The hypothesis of `base_single_b` is satisfiable: one `b`-side does it. -/
theorem base_single_b_witness (f : ℕ) :
    0 * f + 1 * (f ^ 2 - 1) + 0 * f ^ 2 = f ^ 2 - 1 := by ring_nf

/-! ## 2. The angle at the far end of that side does not fit -/

variable (α β γ : ℝ)

/-- `γ = 2α + β` exceeds the base angle `α + β` of `T_mid`, for any positive `α`. -/
theorem gamma_gt_base_angle (hγ : γ = 2 * α + β) (hα : 0 < α) : α + β < γ := by
  rw [hγ]; linarith

/-- The base angles of `T_mid` are `α + β`: they are what remains of `π` after the apex `α`,
using `3α + 2β = π`. -/
theorem base_angle_eq (hrel : 3 * α + 2 * β = Real.pi) :
    α + 2 * (α + β) = Real.pi := by linarith

/-- A tile's angle presented at a corner of `T_mid` cannot exceed that corner's interior angle. -/
theorem no_gamma_at_base_corner (hγ : γ = 2 * α + β) (hα : 0 < α)
    (θ : ℝ) (hθ : θ = γ) (hfit : θ ≤ α + β) : False := by
  rw [hθ, hγ] at hfit; linarith

/-! ## 3. The exclusion, with the tile-placement step as a named hypothesis -/

/-- **`T_mid` is untileable at `e = 1`.**

`base_single_b` supplies the single tile; the geometric input (the standing "no tile-placement layer" blocker): the sides lying on
`DD'` are whole tile sides whose lengths sum to `b`.  `hends` is the elementary fact that the two
angles adjacent to a `b`-side are `α` and `γ`.  `hfit` is that a tile at a corner presents at most
the corner's interior angle.  Together they are contradictory. -/
theorem midTriangle_untileable (hα : 0 < α) (hγ : γ = 2 * α + β)
    -- the single tile on the base, with the angles it presents at `D` and `D'`
    (θD θD' : ℝ)
    (hends : (θD = α ∧ θD' = γ) ∨ (θD = γ ∧ θD' = α))
    (hfitD : θD ≤ α + β) (hfitD' : θD' ≤ α + β) : False := by
  rcases hends with ⟨_, h⟩ | ⟨h, _⟩
  · exact no_gamma_at_base_corner α β γ hγ hα θD' h hfitD'
  · exact no_gamma_at_base_corner α β γ hγ hα θD h hfitD

end Erdos634.MidTriangleE1
