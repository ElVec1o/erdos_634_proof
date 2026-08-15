import Mathlib.Tactic
import Erdos634.BaseBetaCorners
import Erdos634.RogueContainment

/-!
# ForcedRow.lean — the forced first row of a scale-`k` inflation: the arithmetic skeleton

Erdős #634, base-`β` branch.  The induction `W(k−1) ⟹ W(k)` ("every scale-`k` inflation
occurring inside a tiling is standard") rests on the **forced row**: the first row of `Δ_k`
along the `B`-side is forced tile by tile, and the forcing stalls at exactly one per-slot
dichotomy — the rogue.  Until now that derivation lived only in module docstrings
(`RogueContainment`, `RogueChord`, `RogueMirror`) and session notes, cited as "the forced row
and slot structure from the `W(k)` session (paper)"; the companion's subsection
`sub:forcedrow` is now its reference write-up, and this file banks the assembly's arithmetic
skeleton — the position calculus, the junction ledger, the figure forcing, and the dichotomy —
as named theorems.  Everything here is bookkeeping; the geometry enters only through the
standing hypotheses listed at the end.

## The chart and the row

Chart `(x, ŷ)`, `y = ŷ·√D`, `D = 4f² − e²`; `Δ_k` has `A = (0,0)` (the `α`-corner),
`C = kb·w` (the `γ`-corner), `B = kc·u` (the `β`-corner), with the unit vectors

    w = (1, 0)                    (the base, word b^k),
    2·u = ((2f²−e²)/f², e/f²)     (the c-side AB),
    2·v̂ = (e/f, 1/f)              (the a-side direction, C → B).

Cleared by `2`, the three scaled vectors are integral:

    2·(b·w) = (2(f²−e²), 0),   2·(c·u) = (2f²−e², e),
    2·(a·v̂) = (e², e),          2·(c·v̂) = (ef, f).

The **forced row** is `P_0, Q_0, P_1, Q_1, …, P_{k−1}` with

    P_i = P_0 + i·b·w :  α at i·b·w,  γ at (i+1)·b·w,  β at X_i,
    Q_i = Q_0 + i·b·w :  β at (i+1)·b·w,  γ at X_i,  α at X_{i+1},

where `X_i := i·b·w + c·u` is the apex of `P_i` and the row-top advances `X_{i+1} = X_i + b·w`.
The forcing chain (companion, `sub:forcedrow`; each step cites its banked core):

1.  `P_0` — the `α`-corner fill is `{α}` (`CChord.fill_alpha`), flanks `{b, c}`; the `c`-side
    carries no `b` (`Inflation.c_side_no_b` for `k < f`, `SideNoB.side_no_b_uncond` at `k = f`),
    so the `b`-flank lies on the base: `P_0` is standard.
2.  `Q_0` — `P_0`'s `a`-edge `[b·w, c·u]` is blocked at both ends by the region boundary, so
    its far side is partitioned by whole tile edges summing to `a`
    (`Geometry.Dissection.wall_two_sided`-class), and `Inflation.a_unsplittable` leaves a single
    `a`-edge: one partner tile.  The reflected partner repeats `γ` at `b·w` against `P_0`'s `γ`
    (`BaseBetaCorners.pi_vertex_gamma_le_one`; directly `2γ = π + α > π`), so the **direct**
    partner is forced, and `P_0 ∪ Q_0` is the parallelogram `(A, b·w, b·w + c·u, c·u)`
    (`pgram_x` below).
3.  `P_1` — at `Y_0 = b·w` the figure `γ + β` leaves the residual `α` (`junction_ledger`),
    fill `{α}`, flanks `{b, c}` on the rays `w` and `u`; `c` on the base would contradict the
    base word `b^k` (`base_letter_distinct`), so `P_1 = P_0 + b·w`.
4.  **The slot dichotomy** — at `Y_i = (i+1)·b·w`, `1 ≤ i ≤ k−2`, only `P_i`'s `γ` is present;
    the junction figure is `{α, β, γ}` (`slot_figure`), the `α` is base-adjacent
    (`base_letter_distinct`: a `β`-tile's flanks `{a, c}` cannot lay the base letter `b`), so
    `P_{i+1}` is forced and the `β`-tile lays on the chord ray `v̂` either its `a`-flank — the
    standard `Q_i`, closing the parallelogram — or its `c`-flank — the **rogue**, overrunning
    `X_i` by `Δ = c − a = f(f−e)` (`overrun_x`; `RogueChord.delta_identities`).  At `i = 0`
    both chord ends are blocked, so no rogue exists there and the slot range is exactly
    `1 ≤ i ≤ k−2` (`M := i+1 ∈ [2, k−1]`).
5.  The standard row closes: `2k−1` row tiles plus the scale-`(k−1)` remainder anchored at
    `c·u` (`remainder_x/_y`) make `k²` (`row_count`), and `W(k−1)` applies to the remainder.

## The slot kills this feeds

`RogueContainment` (`M·e < f` — `slot_dies_by_containment` below is the wired instance),
`RogueChord` K1–K3, `RogueFan` (low slots), `RogueMirror` (top-2/top-3, and the wall-scale
base reading `wall_base_reading` that discharges the `b^f` input at `k = f`).

## Standing hypotheses (the geometry, named)

*  the angle sums at a point of the dissection — `2π` interior, `π` at a side-interior point,
   the corner angle at a corner (`Dissection.HasAngleSums`-class, G2); together with
   `α/π ∉ ℚ` (proved, `BaseBetaE1.tile_alpha_irrational`) they yield the integer
   multiplicities via `Geometry.vertex_multiplicities` (proved);
*  the exactly-once edge coverings — `Geometry.Dissection.side_partition` (boundary) and
   `wall_two_sided` (interior walls), both PROVED (G3); their ordered-run extraction is the
   named residual of `ChordInterface.FarSide`;
*  the base reading `b^k` — `Inflation.b_side_rigid` (`k < f`),
   `RogueMirror.wall_base_reading` (`k = f`), themselves standing on the previous two items.

Axiom-clean; no `sorry`; nothing here duplicates a banked lemma — the fills, unsplittability
and containment cores are imported and instantiated, not restated.
-/

namespace Erdos634.ForcedRow

/-! ## The position calculus (cleared chart, `×2`) -/

/-- **The jump identity** `Y_i + a·v̂ = X_i`, x-coordinate cleared by `2`:
`Y_i = (i+1)·b·w` plus `a·v̂` lands on the row apex `X_i = i·b·w + c·u`.  (The `ŷ`-coordinates
agree at `e` on both sides.)  This is the `i`-translated instance of the chart generator
`c·u − a·v̂ = b·w` (`RogueMirror.generator_x/_y`); it is why the chord ray from the slot
toward `X_i` carries exactly one `a` of room before the row apex. -/
theorem jump_x (e f i : ℤ) :
    (i + 1) * (2 * (f ^ 2 - e ^ 2)) + e ^ 2
      = i * (2 * (f ^ 2 - e ^ 2)) + (2 * f ^ 2 - e ^ 2) := by ring

/-- **The parallelogram closure** `Y_i + c·u = X_i + b·w`, x-coordinate cleared by `2`
(`ŷ`: both sides are `e`).  Read at `i`: the fourth vertex of `P_i ∪ Q_i` is reached both as
`Y_i + c·u` (up the `c`-flank of the slot's `β`-tile) and as `X_i + b·w` (along the row top),
so the direct partner closes a parallelogram and the row top advances by exactly one base
letter: `X_{i+1} = X_i + b·w`. -/
theorem pgram_x (e f i : ℤ) :
    (i + 1) * (2 * (f ^ 2 - e ^ 2)) + (2 * f ^ 2 - e ^ 2)
      = (i * (2 * (f ^ 2 - e ^ 2)) + (2 * f ^ 2 - e ^ 2)) + 2 * (f ^ 2 - e ^ 2) := by ring

/-- **The remainder anchor**, x-coordinate cleared by `2`: `B − c·u = (k−1)·c·u`, decomposed
as the remainder's own base-plus-jump structure `(k−1)·b·w + (k−1)·a·v̂`.  The region above
the forced row is the scale-`(k−1)` triangle anchored at `c·u` — the object `W(k−1)`
consumes. -/
theorem remainder_x (e f k : ℤ) :
    k * (2 * f ^ 2 - e ^ 2) - (2 * f ^ 2 - e ^ 2)
      = (k - 1) * (2 * (f ^ 2 - e ^ 2)) + (k - 1) * e ^ 2 := by ring

/-- The remainder anchor, `ŷ`-coordinate cleared by `2`. -/
theorem remainder_y (e k : ℤ) : k * e - e = (k - 1) * e := by ring

/-- **The rogue overrun**, x-coordinate cleared by `2`: the rogue's far endpoint
`Z_i = Y_i + c·v̂` overruns the row apex `X_i` by exactly `Δ·v̂` with `Δ = c − a`:
`Z_i − X_i` has cleared x-coordinate `e(f−e) = 2·(Δ·v̂)_x`.  (`ŷ`: `f − e = 2·(Δ·v̂)_ŷ`,
immediate.)  `Δ = f(f−e) < b < a, c`: the overrun is shorter than every tile edge
(`RogueChord.delta_identities`), which is what makes `X_i` a T-vertex of the rogue branch
rather than a flush endpoint. -/
theorem overrun_x (e f i : ℤ) :
    ((i + 1) * (2 * (f ^ 2 - e ^ 2)) + e * f)
      - (i * (2 * (f ^ 2 - e ^ 2)) + (2 * f ^ 2 - e ^ 2)) = e * (f - e) := by ring

/-- **The row count**: `k` up-tiles and `k−1` down-tiles, plus the `(k−1)²` tiles of the
remainder, exhaust the inflation: `(2k−1) + (k−1)² = k²`. -/
theorem row_count (k : ℤ) : (2 * k - 1) + (k - 1) ^ 2 = k ^ 2 := by ring

/-! ## The junction ledger (over `ℝ`, on the single relation `3α + 2β = π`) -/

/-- **The junction ledger**: `γ + α + β = π` — the standard slot figure closes a straight
angle exactly.  (`γ = 2α + β` throughout the branch.) -/
theorem junction_ledger (α β : ℝ) (h : 3 * α + 2 * β = Real.pi) :
    (2 * α + β) + α + β = Real.pi := by linarith

/-- **The slot residual**: after the row tile's `γ` and the next row tile's `α`, the residual
at a base junction is exactly `β` — the slot's `β`-tile is angle-forced, and only its flank
assignment (the `a`-vs-`c` dichotomy) is free. -/
theorem slot_residual_beta (α β : ℝ) (h : 3 * α + 2 * β = Real.pi) :
    Real.pi - (2 * α + β) - α = β := by linarith

/-! ## The figure forcing -/

/-- **The slot figure is `{α, β, γ}`.**  A junction interior to a side is `(3,2,0)` or
`(1,1,1)` (`BaseBetaCorners.pi_vertex_figures`); the row tile `P_i` contributes a `γ`, which
kills `(3,2,0)`.  So besides the `γ` the junction carries exactly one `α` and one `β` — the
next row tile and the slot's `β`-tile, nothing else. -/
theorem slot_figure (p q r : ℕ) (h1 : 2 * (p : ℤ) - 3 * q + r = 0) (h2 : q + r = 2)
    (hr : 1 ≤ r) : p = 1 ∧ q = 1 ∧ r = 1 := by
  rcases Erdos634.BaseBetaCorners.pi_vertex_figures p q r h1 h2 with ⟨_, _, hr0⟩ | h
  · omega
  · exact h

/-- **The base letter is neither flank of a `β`-tile.**  `a = b` would give `e² = f(f−e)`,
so `f ∣ e²`, forcing `f = 1` by coprimality; `b = c` fails on `e ≥ 1`.  Consequence: at a
base junction the `β`-tile of the slot figure cannot be base-adjacent (its flanks are
`{a, c}`), so the base-adjacent tile is the `α` — the next row tile, laying `b`. -/
theorem base_letter_distinct (e f b : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) :
    e * f ≠ b ∧ b ≠ f ^ 2 := by
  constructor
  · intro h
    have hd : (f : ℤ) ∣ (e : ℤ) ^ 2 := by
      refine ⟨(f : ℤ) - e, ?_⟩
      have hbz : (b : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hb
      have hz : (e : ℤ) * f = (b : ℤ) := by exact_mod_cast h
      linear_combination hbz + hz
    have hdn : f ∣ e ^ 2 := by exact_mod_cast hd
    have hf1 : f = 1 := (Nat.Coprime.pow_right 2 hcop.symm).eq_one_of_dvd hdn
    omega
  · intro h
    have h1 : 1 ≤ e ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega

/-! ## The dichotomy, named -/

/-- The two flank assignments of the slot's `β`-tile: `std` lays `a` on the chord ray `v̂`
(and `c` on the `u`-ray) — the direct partner `Q_i`; `rogue` lays `c` on `v̂` (and `a` on
`u`) — the overrunning branch. -/
inductive SlotChoice
  | std
  | rogue
deriving DecidableEq

/-- The length laid along the chord ray `v̂` toward `X_i`. -/
def SlotChoice.chordLen (e f : ℕ) : SlotChoice → ℕ
  | .std => e * f
  | .rogue => f ^ 2

/-- The length laid along the `u`-ray at the slot. -/
def SlotChoice.uLen (e f : ℕ) : SlotChoice → ℕ
  | .std => f ^ 2
  | .rogue => e * f

/-- **The flank multiset is `{a, c}` under either choice**: the product invariant
`chordLen · uLen = e·f³` holds for both assignments — the dichotomy permutes the pair and
never introduces a `b`. -/
theorem flank_product (e f : ℕ) (ch : SlotChoice) :
    ch.chordLen e f * ch.uLen e f = e * f ^ 3 := by
  cases ch
  · show e * f * f ^ 2 = e * f ^ 3
    ring
  · show f ^ 2 * (e * f) = e * f ^ 3
    ring

/-- The flank sum invariant `chordLen + uLen = a + c`, the additive companion. -/
theorem flank_sum (e f : ℕ) (ch : SlotChoice) :
    ch.chordLen e f + ch.uLen e f = e * f + f ^ 2 := by
  cases ch
  · show e * f + f ^ 2 = e * f + f ^ 2
    rfl
  · show f ^ 2 + e * f = e * f + f ^ 2
    ring

/-- **The choice is read off the chord letter**: since `a < c`, laying `a` on the chord ray
is exactly the standard choice. -/
theorem std_iff_chord_a (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (ch : SlotChoice) :
    ch = SlotChoice.std ↔ ch.chordLen e f = e * f := by
  have hac : e * f < f ^ 2 := by nlinarith
  cases ch
  · simp [SlotChoice.chordLen]
  · simp only [SlotChoice.chordLen]
    constructor
    · intro h
      exact absurd h (by simp)
    · intro h
      omega

/-- **The rogue strictly overruns**: `a < c`, so the `c`-choice extends past `X_i` — the
overrun is `Δ = c − a = f(f−e)` (`overrun_x`, `RogueChord.delta_identities`). -/
theorem rogue_overrun_pos (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    SlotChoice.chordLen e f SlotChoice.std < SlotChoice.chordLen e f SlotChoice.rogue := by
  simp [SlotChoice.chordLen]
  nlinarith

/-- **Containment, wired**: at a slot `Y_i` with `(i+1)·e < f` the rogue's far endpoint has
negative `w`-coordinate — it exits `Δ_k`, so the choice is forced to `std`.  This is the
instance of `RogueContainment.outside_iff` the row forcing consumes; with
`RogueContainment.step_rogue_free` it closes every step `W(k−1) ⟹ W(k)` with
`(k−1)e < f`. -/
theorem slot_dies_by_containment (i e f : ℤ) (hef : e < f) (he : 0 < e)
    (h : (i + 1) * e < f) : (f ^ 2 - e ^ 2) * ((i + 1) * e - f) < 0 :=
  (Erdos634.RogueContainment.outside_iff i e f hef he).mpr h

end Erdos634.ForcedRow

#print axioms Erdos634.ForcedRow.jump_x
#print axioms Erdos634.ForcedRow.pgram_x
#print axioms Erdos634.ForcedRow.remainder_x
#print axioms Erdos634.ForcedRow.overrun_x
#print axioms Erdos634.ForcedRow.row_count
#print axioms Erdos634.ForcedRow.junction_ledger
#print axioms Erdos634.ForcedRow.slot_residual_beta
#print axioms Erdos634.ForcedRow.slot_figure
#print axioms Erdos634.ForcedRow.base_letter_distinct
#print axioms Erdos634.ForcedRow.flank_product
#print axioms Erdos634.ForcedRow.std_iff_chord_a
#print axioms Erdos634.ForcedRow.rogue_overrun_pos
#print axioms Erdos634.ForcedRow.slot_dies_by_containment
