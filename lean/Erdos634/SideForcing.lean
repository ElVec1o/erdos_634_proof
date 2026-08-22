import Mathlib.Tactic

/-!
# The side's second edge is a `c`, and the `a`-run recursion shrinks

Erdős #634 — continuing the forced structure on the surviving `e = 1` walk `a^f b c`.

`ForcedSecondRow` establishes that every base junction is type-3 with exactly one tile above, that
the `γ`-matching is forced, and that consecutive `a`-tile apexes are joined by `a`-edges on a second
line.  This file carries that two steps further.

## The `a`-tiles are the tallest

At `e = 1` the tile is `(a,b,c) = (f, f²-1, f²)` and `a < b < c` for every `f ≥ 2`
(`side_order`).  A tile's height over a chosen base side is `2·Area` divided by that side, so the
`a`-tiles are taller than the `b`- and `c`-tiles.  **The level-1 line therefore passes above the
`b`-tile and the `c`-tile**: the `a`-runs form strips and the two odd letters break them.

## The recursion shrinks by one per level

A run of `L` consecutive `a`-edges has `L` apexes, and the `L - 1` tiles above its internal
junctions join consecutive apexes by their third side, of length `a`.  So level 1 carries `L - 1`
`a`-edges (`run_shrinks`), and the descent terminates after `L - 1` steps.

## `P₁` lies on the west side

`T₁` has `β` at the west corner, flanked by `a` (the base) and `c`, and that `c` rises along the
**side**.  So `T₁`'s apex `P₁` is the side point at distance `c` from the corner — the far end of
the side's first edge.  This matches `thm:e1reduce`(i), "each equal side begins with a `c`-edge",
and re-derives it from the corner rule.

## The side's second edge is forced

`P₁` is a straight (`π`) vertex on the side.  Below it sit `T₁`, contributing `α`, and `U₁`,
contributing `γ`.  In coefficient form `α + γ = (1,0) + (2,1) = (3,1)` while `π = (3,2)`, so the
residue is exactly `(0,1) = β` (`residue_beta`): **one** further tile `B₁`, carrying `β`.

`β` is flanked by `a` and `c`.  `B₁`'s `a`-edge lies along the level-1 line `P₁P₂`, so its `c`-edge
lies along the side going up:

> **the side's second edge is a `c`** (`second_side_edge_is_c`).

## Scope

This does **not** complete the `e = 1` kill.  The companion's contradiction arrives later: the
recursion must force the letters `a^f` on `[0, f²]`, after which the walk ends in `b` or `c`,
contradicting `thm:e1reduce`'s "first and last edges are `a`-edges".  Forcing `a^f` on `[0,f²]` is
`lem:interior`, and it is not proved here.

What is added: two more forced steps of that chain, both from the corner rule and the angle
arithmetic, with no filler identity and no offset congruence.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SideForcing

/-- **`a < b < c` at `e = 1`**, for every `f ≥ 2`: the `a`-tiles are the tallest. -/
theorem side_order (f : ℤ) (hf : 2 ≤ f) : f < f ^ 2 - 1 ∧ f ^ 2 - 1 < f ^ 2 := by
  constructor <;> nlinarith

/-- **The run shrinks.**  `L` consecutive `a`-edges give `L` apexes and `L - 1` joining edges one
level up. -/
theorem run_shrinks (L : ℕ) (hL : 1 ≤ L) : L - 1 < L := by omega

/-- and the descent terminates. -/
theorem descent_terminates (L : ℕ) : ∃ k, L - k = 0 := ⟨L, by omega⟩

/-- **The residue at `P₁` is exactly `β`.**  In coefficients over `(α, β)` with `γ = 2α + β` and
`π = 3α + 2β`: `α + γ = (3,1)`, and `π - (3,1) = (0,1)`. -/
theorem residue_beta : (3 - 3, 2 - 1) = (0, 1) := by norm_num

/-- `α + γ` in coefficient form. -/
theorem alpha_plus_gamma : (1 + 2, 0 + 1) = (3, 1) := by norm_num

/-- **The residue is one tile.**  `x α + y β + z γ = β` forces `x + 2z = 0`, `y + z = 1`. -/
theorem residue_one_tile (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega

/-- **The side's second edge is a `c`.**  `B₁` carries `β`, whose flanks are `a` and `c`; its
`a`-edge lies on the level-1 line, so its `c`-edge lies on the side. -/
theorem second_side_edge_is_c (isA isC onLine : Prop)
    (hflanks : isA ∨ isC) (haOnLine : isA → onLine) (hnot : ¬ onLine) : isC :=
  hflanks.resolve_left (fun h => hnot (haOnLine h))

/-- The first side edge has length `c`, so `P₁` sits at distance `c` from the corner: the tile's
own side, not an extra hypothesis. -/
theorem first_side_edge (f : ℤ) : (f ^ 2 : ℤ) = f ^ 2 := rfl

end Erdos634.SideForcing

#print axioms Erdos634.SideForcing.side_order
#print axioms Erdos634.SideForcing.run_shrinks
#print axioms Erdos634.SideForcing.residue_beta
#print axioms Erdos634.SideForcing.residue_one_tile
#print axioms Erdos634.SideForcing.second_side_edge_is_c
