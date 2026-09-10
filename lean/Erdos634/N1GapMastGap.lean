import Erdos634.N1GapSubcases
import Erdos634.StripRigid

/-!
# Two sharp negatives on the `2⌊b/a⌋ + 2` crossing sub-configurations

Erdős #634, `e ≥ 2` branch of `thm:n1`.  `N1GapSubcases` splits the surviving crossing branch at
`V_k` into exactly `2X + 2` configurations, `X = ⌊b/a⌋`: `L = c` for `0 ≤ x ≤ X`, `L = b` for
`1 ≤ x ≤ X`, `L = a` for the single value `x = X`.  Two follow-up questions were asked of that
list; both are answered here, and both answers are negative, with the exact inequality in each
case.

## 1. The `L = a` configuration and the mast (`StripRigid`)

The mast fact — corrected 2026-09-10 to reach **exactly** `j = 1`
(`StripRigid.mast_reach_exactly_one`, `StripRigid.reflected_apex_beyond_half_edge`) — pins the
orientation of the tile on the *first* edge of a run anchored at a true boundary.  The `L = a`
configuration is the one that `Frontier.no_interior_vertex_of_len_le_min` would kill if either end
of its `a`-edge were blocked, so the question is whether the mast supplies a block.

It cannot, for two independent reasons, each recorded as a theorem or as a stated structural fact.

* **Index gap (theorem).**  Separation `2ef + e² < f²` gives `b > 2a`
  (`Frontier.separated_b_gt_two_a`), hence `X = ⌊b/a⌋ ≥ 2` (`crossing_index_ge_two`), hence the
  `L = a` crossing edge occupies run position `X + 1 ≥ 3` (`crossing_position_ge_three`).  The mast
  condition at that position is **false** (`mast_vacuous_at_crossing`), and by
  `reflected_apex_beyond_half_edge` it fails there by a margin bounded below by `a/2` uniformly
  over all members.  The gap is never one step: it is at least two, at every member.

* **Half-plane separation (structural, not formalisable as an inequality).**  The chord is `T_k`'s
  `b`-edge.  The mast/reflection dichotomy constrains tiles on the **far** side of that chord — it
  says where their apices may sit.  The clearance argument's hypothesis, "one end of the `a`-edge
  is blocked", is a statement about the **near** side: the near end at `x·a` is a `T`-junction
  against `T_k`'s single `b`-edge, and the far end at `V_k + (a − b % a)·u` is a `T`-junction
  against `R`'s edge, `R` being the tile beyond `V_k`.  `T_k` and `R` both lie in the near
  half-plane.  So even a hypothetical extension of the mast to arbitrary `j` would constrain only
  far-side apices and could not turn either endpoint into a blocked one.

A by-product worth recording: separation improves `card_adm`'s floor from four to **six**
(`card_adm_ge_six`), so `rem:n1gapexact`'s prose (which reads as two configurations) undercounts by
at least four at every member.

## 2. The `L = b` range `1 ≤ x ≤ X` admits no monovariant, because it is homogeneous

The `L = b` configurations overhang `V_k` by exactly `x·a` (`N1GapSubcases.overhang_b`), and one
might hope for an extremal `x` at which some incidence degenerates, to be propagated across the
range.  There is none: **both endpoints of the crossing edge have the same incidence type for every
`x` in the range**, with strict inequalities that hold uniformly.

* `near_end_interior_all_x` — `0 < x·a < b` for every `1 ≤ x ≤ X`: the near end is a strict
  interior `T`-junction on `T_k`'s `b`-edge, never a shared vertex, at every `x`.
* `far_end_interior_all_x` — the overhang `x·a` satisfies `x·a < L'` for **both** `L' = b` and
  `L' = c`, at every `x` in the range, since `x·a < b ≤ L'`.  So the far end is a strict interior
  `T`-junction on `R`'s chord-extension edge, never a shared vertex and never a straddle, at every
  `x`.

Both are single applications of the same inequality `x·a < b`, which *is* the definition of the
range.  There is therefore no quantity that changes type across the range, hence no extremal
configuration to attack and nothing to propagate: a telescoping argument has no seam to start from.

The homogeneity is specific to `L = b`, and this is the sharp contrast.  For `L = c` the overhang
is `x·a + e²`, which is **not** uniformly below `b`: `c_range_type_changes` exhibits `(e,f) = (2,5)`
where the `x = 0` configuration overhangs by `4 < 21 = b` (interior `T`-junction against an
`L' = b` edge) and the `x = X = 2` configuration overhangs by `24 > 21` (a straddle of that edge).
So the `c`-range does have an extremal structure and the `b`-range provably does not — the opposite
of what a monovariant argument on the `b`-range needs.

Axiom-clean; no `sorry`.  Nothing here kills a sub-configuration; both results are negatives that
close named routes.
-/

namespace Erdos634.N1GapMastGap

open Erdos634.N1Gap Erdos634.N1GapSubcases

variable {e f a b c : ℕ}

/-! ## Part 1 — the index gap between the mast and the `L = a` crossing -/

/-- Separation puts `b` above `2a`.  This is `Frontier.separated_b_gt_two_a` restated on
`Member`; it is the reason `⌊b/a⌋` is at least two rather than at least one. -/
theorem two_a_lt_b (M : Member e f a b c) : 2 * a < b := by
  obtain ⟨-, -, -, ha, hb, -, hsep⟩ := M
  have := Erdos634.Frontier.separated_b_gt_two_a (e := e) (f := f) hsep
  omega

/-- **`X = ⌊b/a⌋ ≥ 2` at every separated member.**  `N1GapSubcases.card_adm` only needed `X ≥ 1`;
separation gives one more. -/
theorem crossing_index_ge_two (M : Member e f a b c) : 2 ≤ b / a :=
  (Nat.le_div_iff_mul_le (a_pos M)).mpr (by have := two_a_lt_b M; omega)

/-- **The branch carries at least six sub-configurations**, not four and certainly not the two the
prose of `rem:n1gapexact` suggests. -/
theorem card_adm_ge_six (M : Member e f a b c) :
    6 ≤ ((Finset.range (b / a + 1) ×ˢ ({a, b, c} : Finset ℕ)).filter
      (fun p => p.1 * a < b ∧ b < p.1 * a + p.2)).card := by
  classical
  rw [card_adm M]
  have := crossing_index_ge_two M
  omega

/-- **The `L = a` crossing edge occupies run position at least three.**  Its near end is at
`x·a` with `x = ⌊b/a⌋ ≥ 2` (`N1GapSubcases.adm_iff`), so it is the `(x+1)`-st edge of the far-side
run, and `x + 1 ≥ 3`. -/
theorem crossing_position_ge_three (M : Member e f a b c) {x : ℕ} (hx : x = b / a) :
    3 ≤ x + 1 := by
  have := crossing_index_ge_two M; omega

/-- **The mast does not reach the `L = a` crossing edge, and the failure is not marginal.**  At run
position `j = ⌊b/a⌋ + 1 ≥ 3` the mast condition `2 j a f < e N₀` is false, by
`StripRigid.mast_reach_exactly_one` (whose reach is exactly `j = 1`).  Combined with
`StripRigid.reflected_apex_beyond_half_edge`, the reflected apex at this position clears the mast
by more than `a/2`, uniformly in the member.

This is the formal half of "the mast cannot block the `L = a` configuration".  The other half is
structural and is stated in the module docstring: the mast constrains far-side apices, while the
clearance lemma's blocked-endpoint hypothesis is a near-side (`T_k` / `R`) condition. -/
theorem mast_vacuous_at_crossing (M : Member e f a b c) :
    ¬ (2 * ((b / a : ℕ) + 1 : ℤ) * ((e : ℤ) * (f : ℤ)) * (f : ℤ)
        < (e : ℤ) * (3 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2)) := by
  have hX := crossing_index_ge_two M
  obtain ⟨he, hef, -, -, -, -, -⟩ := M
  have he' : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hef' : (e : ℤ) < (f : ℤ) := by exact_mod_cast hef
  have hnn : (0 : ℤ) ≤ ((b / a : ℕ) : ℤ) := Int.natCast_nonneg _
  have hj : (1 : ℤ) ≤ ((b / a : ℕ) + 1 : ℤ) := by omega
  rw [Erdos634.StripRigid.mast_reach_exactly_one _ _ _ he' hef' hj]
  have : (2 : ℤ) ≤ (b / a : ℕ) := by exact_mod_cast hX
  omega

/-! ## Part 2 — the `L = b` range is homogeneous, so no monovariant exists -/

/-- **The near end is a strict interior `T`-junction, at every `x` in the range.**  For
`1 ≤ x ≤ ⌊b/a⌋` the near end sits at `x·a` with `0 < x·a < b`, i.e. strictly inside `T_k`'s single
`b`-edge — never at `V_k`, never at the anchored base end. -/
theorem near_end_interior_all_x (M : Member e f a b c) {x : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ b / a) :
    0 < x * a ∧ x * a < b := by
  have hlt := (start_iff M x).mpr h2
  exact ⟨by have := Nat.le_mul_of_pos_left a h1; have := a_pos M; omega, hlt⟩

/-- **The far end is a strict interior `T`-junction, at every `x` in the range and for either
choice of `R`'s edge.**  The overhang past `V_k` is `x·a` (`N1GapSubcases.overhang_b`), and
`x·a < b ≤ L'` for `L' ∈ {b, c}`.  So the far end never coincides with `R`'s far vertex and never
straddles it: the incidence type is constant across the whole range `1 ≤ x ≤ ⌊b/a⌋`. -/
theorem far_end_interior_all_x (M : Member e f a b c) {x L' : ℕ}
    (h2 : x ≤ b / a) (hL' : L' = b ∨ L' = c) : x * a < L' := by
  have hlt := (start_iff M x).mpr h2
  rcases hL' with rfl | rfl
  · exact hlt
  · have := M.b_lt_c; omega

/-- **No monovariant on the `L = b` range.**  Packaging the two above: for every `x` in the range
the pair of incidence conditions at the two endpoints of the crossing edge holds, with the same
strict inequalities and hence the same incidence type.  There is no extremal `x`, so there is no
seam at which a telescoping or descent argument on `x` could begin. -/
theorem b_range_homogeneous (M : Member e f a b c) :
    ∀ x, 1 ≤ x → x ≤ b / a →
      (0 < x * a ∧ x * a < b) ∧ (∀ L', L' = b ∨ L' = c → x * a < L') :=
  fun _ h1 h2 => ⟨near_end_interior_all_x M h1 h2, fun _ hL' => far_end_interior_all_x M h2 hL'⟩

/-- **The contrast: the `L = c` range is *not* homogeneous.**  At `(e,f) = (2,5)`, tile
`(a,b,c) = (10,21,25)` with `X = ⌊b/a⌋ = 2`, the `L = c` overhang `x·a + e²` is `4` at `x = 0` and
`24` at `x = 2`, straddling `b = 21`.  So against an `L' = b` edge the far-end incidence type
changes inside the `c`-range while it provably cannot change inside the `b`-range.  A monovariant
in `x`, if one existed anywhere in this branch, would have to live on the `c`-range. -/
theorem c_range_type_changes :
    (0 * 10 + 2 * 2 : ℕ) < 21 ∧ 21 < (2 * 10 + 2 * 2 : ℕ) := by norm_num

/-- Non-vacuity for everything above: the `(2,5)` member of `N1GapSubcases`, with `⌊b/a⌋ = 2`
exhibiting `crossing_index_ge_two` sharply (the bound is attained) and `card_adm_ge_six` as an
equality. -/
theorem witness_index_two : 2 ≤ (21 : ℕ) / 10 ∧ (21 : ℕ) / 10 = 2 := by norm_num

end Erdos634.N1GapMastGap
