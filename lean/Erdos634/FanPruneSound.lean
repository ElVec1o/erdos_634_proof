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

/-! ## The extended criterion: every corner, not only the acute convex ones

The engine's corner test was applied only at **acute convex** corners: the corner routine skipped
every non-convex vertex, and the fillability test sat behind an acute-only guard.  The same
equation binds everywhere, and extending it to obtuse and reflex corners is what settles
`N = 431` and `N = 587`.

The criterion.  A corner of the uncovered region with interior angle `W` is filled by tiles that
either have a vertex there — contributing `α`, `β` or `γ = 2α + β` — or carry the corner interior
to an edge, contributing `π = 3α + 2β`, which is possible only when `W > π`, i.e. at a reflex
corner.  **Every one of those four contributions is of the form `Xα + Yβ` with `X, Y ≥ 0`**, so
`W` must be too (`corner_fill_form`); a corner whose angle admits no such representation admits no
fill (`corner_unfillable`).

The reflex case needs one extra remark, which is why the engine matches it against a separate
table: there the interior angle is `2π − θ` for the angle `θ` between the two boundary rays, and
`cos(2π − θ) = cos θ`, so the cosine alone does not distinguish the two — the sign of the cross
product does.

Axiom-clean; no `sorry`.
-/

/-- **Every admissible contribution has the form `Xα + Yβ` with `X, Y ≥ 0`.**  The four cases are
a vertex showing `α`, `β` or `γ = 2α+β`, and an edge through the corner contributing
`π = 3α+2β`. -/
theorem contribution_form (α β x : ℝ)
    (h : x = α ∨ x = β ∨ x = 2*α + β ∨ x = 3*α + 2*β) :
    ∃ X Y : ℕ, x = (X : ℝ) * α + (Y : ℝ) * β := by
  rcases h with h | h | h | h
  · exact ⟨1, 0, by rw [h]; push_cast; ring⟩
  · exact ⟨0, 1, by rw [h]; push_cast; ring⟩
  · exact ⟨2, 1, by rw [h]; push_cast; ring⟩
  · exact ⟨3, 2, by rw [h]; push_cast; ring⟩

/-- **A filled corner's angle has the form `Xα + Yβ`.**  Induction over the multiset of
contributions at the corner. -/
theorem corner_fill_form (α β : ℝ) :
    ∀ (angles : Multiset ℝ),
      (∀ x ∈ angles, x = α ∨ x = β ∨ x = 2*α + β ∨ x = 3*α + 2*β) →
      ∃ X Y : ℕ, angles.sum = (X : ℝ) * α + (Y : ℝ) * β := by
  intro angles
  induction angles using Multiset.induction_on with
  | empty => exact fun _ => ⟨0, 0, by simp⟩
  | cons a s ih =>
    intro hmem
    obtain ⟨X, Y, hs⟩ := ih (fun x hx => hmem x (Multiset.mem_cons_of_mem hx))
    obtain ⟨P, Q, ha⟩ := contribution_form α β a (hmem a (Multiset.mem_cons_self a s))
    exact ⟨P + X, Q + Y, by rw [Multiset.sum_cons, ha, hs]; push_cast; ring⟩

/-- **The extended prune is sound.**  A corner whose angle is not `Xα + Yβ` for any `X, Y ≥ 0`
admits no fill — whether it is acute, obtuse or reflex. -/
theorem corner_unfillable (α β W : ℝ)
    (hno : ∀ X Y : ℕ, W ≠ (X : ℝ) * α + (Y : ℝ) * β)
    (angles : Multiset ℝ)
    (hmem : ∀ x ∈ angles, x = α ∨ x = β ∨ x = 2*α + β ∨ x = 3*α + 2*β)
    (hsum : angles.sum = W) : False := by
  obtain ⟨X, Y, h⟩ := corner_fill_form α β angles hmem
  exact hno X Y (hsum ▸ h)

end Erdos634.FanPruneSound
