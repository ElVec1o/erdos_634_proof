import Mathlib.Tactic

/-!
# Soundness of the fan-collapse prune

Erdős #634.  The search engine gained a prune (`CENGINE_FAN`) that cuts, at its root, any subtree
below a convex corner of the uncovered region whose angle is smaller than the second-smallest tile
angle and is not an exact integer multiple of the smallest.  Every exclusion certified with the
prune enabled — including `N = 191` — rests on its soundness, so the argument is recorded here.

**The argument.**  Let a convex corner of the uncovered region have angle `W`, and let `α < β ≤ γ`
be the tile's angles.

* Every tile covering a neighbourhood of the corner has a *vertex* there: it cannot contain the
  corner in its interior (it would leave the region), and it cannot have the corner interior to one
  of its edges (that contributes `π > W`).
* Hence the tiles at the corner contribute a multiset of angles from `{α, β, γ}` summing to `W`.
* If `W < β` then no `β` and no `γ` can occur (`corner_all_alpha`), so every angle is `α` and
  `W = k·α` with `k` the number of tiles there (`corner_is_multiple`).
* Therefore a corner with `W < β` and `W ∉ {kα}` admits no completion, and its subtree is empty.

`fan_prune_sound` states exactly that. The engine's test is the same statement with `k` ranged over
`cos(kα)` by the Chebyshev recurrence, in exact rational arithmetic.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FanPruneSound

/-- **Only the minimal angle fits.**  A corner of angle `W < β` carries no `β` and no `γ`, the
other angles being nonnegative. -/
theorem corner_all_alpha {α β γ W : ℝ} (hα : 0 ≤ α) (hβγ : β ≤ γ)
    (angles : Multiset ℝ) (hmem : ∀ x ∈ angles, x = α ∨ x = β ∨ x = γ)
    (hnn : ∀ x ∈ angles, 0 ≤ x)
    (hsum : angles.sum = W) (hW : W < β) : ∀ x ∈ angles, x = α := by
  intro x hx
  rcases hmem x hx with h | h | h
  · exact h
  · exfalso
    have hle : x ≤ angles.sum := Multiset.single_le_sum hnn x hx
    rw [hsum, h] at hle; linarith
  · exfalso
    have hle : x ≤ angles.sum := Multiset.single_le_sum hnn x hx
    rw [hsum, h] at hle; linarith

/-- **The corner is an exact multiple.**  If every angle at the corner equals `α`, the corner is
`k·α` for `k` the number of tiles there. -/
theorem corner_is_multiple {α W : ℝ} (angles : Multiset ℝ)
    (hall : ∀ x ∈ angles, x = α) (hsum : angles.sum = W) :
    W = (Multiset.card angles : ℝ) * α := by
  have : angles = Multiset.replicate (Multiset.card angles) α := by
    refine Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  rw [← hsum]
  conv_lhs => rw [this]
  rw [Multiset.sum_replicate, nsmul_eq_mul]

/-- **The prune is sound.**  A convex corner with `W < β` that is not an integer multiple of `α`
admits no completion: no multiset of tile angles at it sums to `W`. -/
theorem fan_prune_sound {α β γ W : ℝ} (hα : 0 ≤ α) (hβγ : β ≤ γ) (hW : W < β)
    (hnotmul : ∀ k : ℕ, W ≠ (k : ℝ) * α)
    (angles : Multiset ℝ) (hmem : ∀ x ∈ angles, x = α ∨ x = β ∨ x = γ)
    (hnn : ∀ x ∈ angles, 0 ≤ x) (hsum : angles.sum = W) : False := by
  have hall := corner_all_alpha hα hβγ angles hmem hnn hsum hW
  exact hnotmul (Multiset.card angles) (corner_is_multiple angles hall hsum)

/-- The engine's residue form: with `k = ⌊W/α⌋` the remainder is trapped in `(0, α)` when `W` is
not a multiple, so no further tile fits — the same conclusion, phrased as the leaf test the
unpruned search would eventually reach. -/
theorem residue_trapped {α W : ℝ} (hα : 0 < α) (hW : 0 < W)
    (hnotmul : W - (⌊W / α⌋₊ : ℝ) * α ≠ 0) :
    0 < W - (⌊W / α⌋₊ : ℝ) * α ∧ W - (⌊W / α⌋₊ : ℝ) * α < α := by
  have hdiv : (0 : ℝ) ≤ W / α := le_of_lt (div_pos hW hα)
  have hle : (⌊W / α⌋₊ : ℝ) ≤ W / α := Nat.floor_le hdiv
  have hlt : W / α < (⌊W / α⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h1 : (⌊W / α⌋₊ : ℝ) * α ≤ W := by
    have := mul_le_mul_of_nonneg_right hle (le_of_lt hα)
    rwa [div_mul_cancel₀ W (ne_of_gt hα)] at this
  have h2 : W < ((⌊W / α⌋₊ : ℝ) + 1) * α := by
    have := mul_lt_mul_of_pos_right hlt hα
    rwa [div_mul_cancel₀ W (ne_of_gt hα)] at this
  constructor
  · rcases lt_or_eq_of_le h1 with h | h
    · linarith
    · exact absurd (by linarith : W - (⌊W / α⌋₊ : ℝ) * α = 0) hnotmul
  · nlinarith [h2]

end Erdos634.FanPruneSound
