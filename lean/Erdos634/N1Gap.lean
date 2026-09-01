import Erdos634.Frontier
import Erdos634.PentagonLemma
import Erdos634.ChordInterface

/-!
# The `thm:n1` induction step at `e ≥ 2`, reduced to one crossing (`rem:n1gapexact`)

Erdős #634, `e ≥ 2` branch. `thm:n1` (the column `(0,e,2e)` admits no tiling) is proved at
`e = 1` and open at `e ≥ 2`, the induction failing at the interior points `V_k`
(`rem:n1gap`). `rem:n1gapexact` states the failure sharply, in prose:

> Let `Q` be the tile across `T_k`'s `b`-edge `[V_k, ((k+1)c, 0)]`, base end on `∂ABC`, `V_k`
> interior. Measured from the anchored base end, `Q` lays `a`, `b` or `c`:
> `b` — exact match, `Q` is the partner (what the induction wants); `c` — overruns `V_k` by
> `c − b = e²`; `a` — falls short by `b − a`, and `b − a` is representable in `⟨a,b,c⟩` for no
> member. So both surviving branches force a tile edge past `V_k`, and the induction step is
> **equivalent** to the assertion that nothing overruns `V_k`.

This file makes that reduction a checked theorem rather than prose. The `a`-branch is discharged
by `Frontier.gap_b_sub_a` (`b − a ∉ ⟨a,b,c⟩`, general in the member) and the `b`-branch by
`PentagonLemma.partner_unique`; the `c`-branch is identified as the overrun `c − b = e²`. What
remains genuinely open — that no tile edge actually crosses `V_k` — is `prop:threecostumes`(ii)'s
crossing question at `V_k`, and `prop:ninetools` shows nine tool classes cannot answer it. The
value here is not a closure: it is that `e ≥ 2`'s obligation is now a single, stated,
location-sensitive crossing exclusion, with the two arithmetic escape routes formally closed.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.N1Gap

open Erdos634.ChordInterface

variable {e f a b c : ℕ}

/-- The three tile-side lengths of a **separated** base-β member (`thm:n1`'s hypothesis
`f² > 2ef + e²`), named. Separation is exactly what puts the sides in order `a < b < c`. -/
structure Member (e f a b c : ℕ) : Prop where
  he : 1 ≤ e
  hef : e < f
  hco : Nat.Coprime e f
  ha : a = e * f
  hb : b + e * e = f * f
  hc : c = f * f
  sep : 2 * e * f + e * e < f * f

theorem Member.a_lt_b (M : Member e f a b c) : a < b := by
  obtain ⟨he, hef, _, ha, hb, _, sep⟩ := M
  have hbridge : 2 * e * f = e * f + e * f := by ring
  omega

theorem Member.b_lt_c (M : Member e f a b c) : b < c := by
  obtain ⟨he, _, _, _, hb, hc, _⟩ := M
  have : 0 < e * e := Nat.mul_pos (by omega) (by omega)
  omega

/-- **The `c`-overrun is exactly `e²`.** The `c`-branch of `rem:n1gapexact`. -/
theorem c_overrun (M : Member e f a b c) : c - b = e * e := by
  obtain ⟨_, _, _, _, hb, hc, _⟩ := M; omega

/-- **The `a`-branch is a gap.** If `Q` lays an `a` from the anchored end it falls short of `V_k`
by `b − a`, and no run of tile sides covers that shortfall: `x·a + y·b + z·c = b − a` is
impossible. This is `Frontier.gap_b_sub_a`, restated on `Member`. -/
theorem a_short_is_gap (M : Member e f a b c) (x y z : ℕ)
    (h : x * a + y * b + z * c = b - a) : False := by
  have hab : a < b := M.a_lt_b
  obtain ⟨he, hef, hco, ha, hb, hc, _⟩ := M
  have hf : 2 ≤ f := by omega
  refine Erdos634.Frontier.gap_b_sub_a (e := e) (f := f) (a := a) (b := b) (c := c)
    (d := b - a) (x := x) (y := y) (z := z) (by omega) hf hco ha hb ?_ ?_
  · omega
  · rw [← hc]; exact h

/-- **The `b`-branch is the partner.** If the far side of the chord partitions with total exactly
`b`, it is a single `b`-edge — `Q` is the partner and `V_k` is a junction. This is
`PentagonLemma.partner_unique`, restated on `Member`. -/
theorem b_exact_is_partner (M : Member e f a b c) (x y z : ℕ)
    (h : x * a + y * b + z * c = b) : x = 0 ∧ y = 1 ∧ z = 0 := by
  obtain ⟨he, hef, hco, ha, hb, hc, _⟩ := M
  exact Erdos634.PentagonLemma.partner_unique hco he hef ha (by omega) hc h

/-- **The reduction, `rem:n1gapexact` as a checked statement.** Fix the far side of `T_k`'s
`b`-edge as a `FarSide` run anchored at the boundary end. Its first edge `ℓ ∈ {a,b,c}`. Then
exactly one of:

* `ℓ = b`: `V_k` is a junction (the far side's leading edge is the partner's whole `b`-edge, and a
  single `b` is the only partition of length `b` — `b_exact_is_partner`); the induction step holds
  at `V_k`.
* `ℓ = a`: `ℓ < b`, so the edge ends `b − a` short of `V_k`; covering `[end, V_k]` is impossible
  (`a_short_is_gap`), so no junction sits at `V_k` and an edge must cross it.
* `ℓ = c`: `ℓ > b`, so the edge overruns `V_k` by `c − b = e²`; it crosses `V_k`.

Hence: the induction step (`V_k` is a junction) holds **iff** the leading far-side edge is `b`, and
each of the two alternatives forces a tile edge strictly past `V_k`. The only content not decided
by arithmetic is which alternative the geometry permits — the crossing question at `V_k`. -/
theorem step_reduces_to_crossing (M : Member e f a b c)
    (F : FarSide a b c) (ℓ : ℕ) (hℓ : F.run.headI = ℓ) (hne : F.run ≠ [])
    (hmem : ℓ = a ∨ ℓ = b ∨ ℓ = c) :
    -- `ℓ = b` is the junction (partner) case; the other two strictly pass `V_k`
    (ℓ = b) ∨ (ℓ < b ∧ ℓ = a) ∨ (b < ℓ ∧ ℓ = c ∧ ℓ - b = e * e) := by
  rcases hmem with rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨M.a_lt_b, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨M.b_lt_c, rfl, c_overrun M⟩)

/-- **Corollary: no arithmetic escape.** The `a`- and `c`-branches are *not* alternative
partitions that could quietly satisfy the induction — each is a genuine crossing. Only the `b`-edge
partner reaches `V_k` exactly, and it is unique. So `thm:n1`'s step at `e ≥ 2` is neither more nor
less than excluding a tile edge that overruns `V_k`: one crossing exclusion, no cheaper repair. -/
theorem no_cheaper_repair (M : Member e f a b c) :
    (∀ x y z : ℕ, x * a + y * b + z * c = b → x = 0 ∧ y = 1 ∧ z = 0) ∧
    (∀ x y z : ℕ, ¬ (x * a + y * b + z * c = b - a)) ∧
    (c - b = e * e ∧ 0 < e * e) := by
  refine ⟨fun x y z h => b_exact_is_partner M x y z h,
    fun x y z h => a_short_is_gap M x y z h, c_overrun M, ?_⟩
  obtain ⟨he, _, _, _, _, _, _⟩ := M
  exact Nat.mul_pos (by omega) (by omega)

end Erdos634.N1Gap
