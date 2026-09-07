import Mathlib.GroupTheory.Nilpotent

/-!
# `rem:nilptower` — no higher nilpotent layer (outcome-1/nogo debt)

Erdős #634, `paper/erdos-634-obstructions.tex:1756`. The remark's content is pure group theory,
with no geometric quantifier at all: for the tiling group `G`, the class-2 layer of the lower
central series collapses (`γ₂ = γ₃`, a fact proved elsewhere, `Remark OM-tilinggroup`), and the
remark's own claim is that this forces `γ_k = γ_2` for **every** `k ≥ 2` — the tower has no further
layers, so every nilpotent quotient of `G` equals its abelianization. This file formalizes exactly
that implication, generally, for any group.

## Scope, stated exactly

**Formalized here: the general algebraic fact.** If a group's lower central series satisfies
`lcs(n+1) = lcs(n)` at some `n`, it stays constant from `n` on. This is completely general — it has
nothing to do with the tiling group specifically, and needs no hypothesis about `n = 2`.

**NOT formalized here: that the tiling group's `γ₂ = γ₃` actually holds** — that is
`Remark OM-tilinggroup`'s content, a separate fact about a specific group, not this one.
`rem:nilptower` stays PROVED: this file supplies the algebraic half unconditionally, but the row's
overall content is the composition of the group-theoretic step here with the tiling-group-specific
collapse, and only the former is now Lean.

Numerically sanity-checked first (no computation needed — this is a direct structural induction,
verified by hand before writing: `lcs(n+1) = ⁅lcs(n), ⊤⁆` is monotone-in-a-fixed-point sense, so
`lcs(n) = lcs(n+1)` is exactly the statement that `lcs(n)` is a fixed point of `X ↦ ⁅X,⊤⁆`, and a
fixed point stays fixed under further application of the same map).
-/

namespace Erdos634.NilpotentTower

/-- **The lower central series is eventually constant once it stabilizes for one step.**
If `Subgroup.lowerCentralSeries G (n+1) = Subgroup.lowerCentralSeries G n`, then `Subgroup.lowerCentralSeries G m =
Subgroup.lowerCentralSeries G n` for every `m ≥ n`. Pure group theory; no hypothesis on `n` beyond the
one-step collapse. -/
theorem lcs_eventually_const {G : Type*} [Group G] {n : ℕ}
    (h : Subgroup.lowerCentralSeries G (n + 1) = Subgroup.lowerCentralSeries G n) :
    ∀ m ≥ n, Subgroup.lowerCentralSeries G m = Subgroup.lowerCentralSeries G n := by
  intro m hm
  induction m with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have hkn : k ≥ n := by omega
      have hk : Subgroup.lowerCentralSeries G k = Subgroup.lowerCentralSeries G n := ih hkn
      rw [Subgroup.lowerCentralSeries_succ, hk, ← Subgroup.lowerCentralSeries_succ, h]
    · have : n = k + 1 := by omega
      rw [this]

/-- **`rem:nilptower`'s exact statement, from the class-2 collapse.** If `γ₂ = γ₃`
(`Subgroup.lowerCentralSeries G 2 = Subgroup.lowerCentralSeries G 3`), then `γ_k = γ₂` for every `k ≥ 2` — the tower
has no layer past class 2. -/
theorem no_layer_past_class_two {G : Type*} [Group G]
    (h : Subgroup.lowerCentralSeries G 3 = Subgroup.lowerCentralSeries G 2) :
    ∀ k ≥ 2, Subgroup.lowerCentralSeries G k = Subgroup.lowerCentralSeries G 2 :=
  lcs_eventually_const h

/-- Non-vacuity: in an abelian group, `Subgroup.lowerCentralSeries G 1 = ⊥` already (the commutator subgroup
is trivial), so certainly `γ₂ = γ₃ = ⊥`, and the theorem applies with a genuine (trivial) witness. -/
example {G : Type*} [CommGroup G] : Subgroup.lowerCentralSeries G 3 = Subgroup.lowerCentralSeries G 2 := by
  have h1 : Subgroup.lowerCentralSeries G 1 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
    simp only [Subgroup.mem_top, true_and, Subgroup.closure_eq_bot_iff]
    rintro y ⟨x, x1, rfl⟩
    rw [commutatorElement_def, mul_comm x x1]
    show x1 * x * x⁻¹ * x1⁻¹ = 1
    group
  have h2 : Subgroup.lowerCentralSeries G 2 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, h1]
    simp
  have h3 : Subgroup.lowerCentralSeries G 3 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, h2]
    simp
  rw [h2, h3]

end Erdos634.NilpotentTower

#print axioms Erdos634.NilpotentTower.lcs_eventually_const
#print axioms Erdos634.NilpotentTower.no_layer_past_class_two
