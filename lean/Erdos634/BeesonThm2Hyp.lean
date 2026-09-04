import Erdos634.TileAt
import Erdos634.MidTriangleE1

/-!
# Beeson's Theorem 2: its three hypotheses, discharged for our target

Erdős #634, base-β family at `e = 1`, `m = 1`.  Beeson (arXiv:1206.2229v3, §6.1, verified verbatim
against the source) requires of an `N`-tiling of `ABC` by a tile `(a,b,c)`/`(α,β,γ)`:

> (i) `ABC` is not similar to the tile, and none of its angles is greater than `γ`;
> (ii) either `3α+2β = π` or `3β+2α = π`;
> (iii) there is just one tile at vertex `B`, and the angle there is `β`.

Our target is isosceles with base angles `β` and apex `3α`.  This file turns the paper-level
"hypotheses discharged" into Lean:

* **(ii)** is the defining relation of the family — `hyp_ii`.
* **(i)** splits.  *Not similar*: the tile's angles are pairwise distinct (`tile_angles_distinct`)
  while the target repeats `β`, so the angle multisets differ (`hyp_i_not_similar`).  *No angle
  exceeds `γ`*: the target's angles are `β, 3α, β`, and `β ≤ γ` is immediate while `3α ≤ γ`
  reduces exactly to `α ≤ β` (`hyp_i_angles_le_gamma`), which at `e = 1` follows from `a < b`,
  i.e. `f < f² − 1` for `f ≥ 2` (`a_lt_b_e1`).
* **(iii)** is *already* a theorem of this development: `TileAt`'s
  `congruentDissection_base_corner_counts` gives the angle census at a base corner (exactly one
  tile presenting `β`, none presenting `α`, `γ` or a straight angle) and
  `congruentDissection_base_corner_tile_unique` gives that exactly one tile's carrier contains the
  vertex.  `hyp_iii` records the citation; it is not reproved here.

**What this does NOT do.**  It discharges the *hypotheses*.  Theorem 2's *proof* — the region `Ω`,
the Type I/II component classification (Beeson Def. 5–7), the arrow and boundary-segment notions
(Def. 12–13), and the two geometric parts 1 and 3 that `BeesonThm2Graph` names — remains unbuilt.
Theorem R is still conditional.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BeesonThm2Hyp

/-! ## Hypothesis (i), angle half -/

/-- The tile's angles are pairwise distinct, given `α < β` and `γ = 2α + β` with `α > 0`. -/
theorem tile_angles_distinct {α β γ : ℝ} (hα : 0 < α) (hαβ : α < β) (hγ : γ = 2 * α + β) :
    α < β ∧ β < γ ∧ α < γ := ⟨hαβ, by rw [hγ]; linarith, by rw [hγ]; linarith⟩

/-- **(i), "no angle exceeds `γ`".**  The target's angles are `β, 3α, β`; both bounds hold as soon
as `α ≤ β`. -/
theorem hyp_i_angles_le_gamma {α β γ : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hγ : γ = 2 * α + β) :
    β ≤ γ ∧ 3 * α ≤ γ := ⟨by rw [hγ]; linarith, by rw [hγ]; linarith⟩

/-- **(i), "not similar".**  The tile's three angles are pairwise distinct while the target repeats
`β`; so no bijection of angle multisets exists and the triangles are not similar. -/
theorem hyp_i_not_similar {α β γ : ℝ} (hα : 0 < α) (hαβ : α < β) (hγ : γ = 2 * α + β) :
    ({β, 3 * α, β} : Multiset ℝ) ≠ {α, β, γ} := by
  intro h
  -- `β` occurs at least twice on the left, but at most once on the right
  have hleft : 2 ≤ Multiset.count β ({β, 3 * α, β} : Multiset ℝ) := by
    classical
    simp [Multiset.count_cons, Multiset.count_singleton]
  have hright : Multiset.count β ({α, β, γ} : Multiset ℝ) ≤ 1 := by
    classical
    have hβα : ¬ (β = α) := by linarith
    have hβγ : ¬ (β = γ) := by rw [hγ]; linarith
    simp [Multiset.count_cons, Multiset.count_singleton, hβα, hβγ, Ne.symm]
  rw [h] at hleft
  omega

/-! ## The `e = 1` arithmetic behind `α ≤ β` -/

/-- At `e = 1` the tile has `a = f < f² − 1 = b` for `f ≥ 2`; with the side–angle order this is
`α < β`, which is what `hyp_i_angles_le_gamma` consumes. -/
theorem a_lt_b_e1 {f : ℕ} (hf : 2 ≤ f) : f < f ^ 2 - 1 := by
  have h : 2 * f ≤ f * f := Nat.mul_le_mul_right f hf
  have : f ^ 2 = f * f := sq f
  omega

/-! ## Hypothesis (iii) — a citation, not a reproof -/

open Erdos634.Geometry Erdos634.TilePlacement in
/-- **(iii), for our target.**  At a base corner of a real congruent dissection exactly one tile's
carrier contains the vertex, and by `congruentDissection_base_corner_counts` the angle it presents
is `β`.  This is Beeson's hypothesis (iii) verbatim, obtained by applying `TileAt`'s theorem — one
name for consumers to cite. -/
theorem hyp_iii {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    (∃! i : Fin N, D.target.pts k ∈ (D.tile i).carrier) ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 :=
  ⟨Erdos634.Geometry.Dissection.congruentDissection_base_corner_tile_unique D α β γ hαβ hαγ hαπ hα0 hβγ hβπ
      hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' k hcorner,
   (Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
      hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' k hcorner).2.1⟩

end Erdos634.BeesonThm2Hyp
