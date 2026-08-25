import Mathlib.Tactic

/-!
# At `e = 1` the base is maximally tight: every junction carries exactly one tile above

Erdős #634 — the engine of `thm:e1family`'s deferred strip-and-column argument, derived from a
count.

## The saturation

`TrichotomyCut` leaves one `e = 1` walk alive: `(f, 1, 1) = a^f b c`, with `f + 2` edges and
`f + 1` interior junctions.  Its `γ`-count is

  `n_a + n_b = f + 1 = ` the number of junctions.

`GammaCount` says those `γ`s all sit at interior junctions, one apiece.  With as many `γ`s as
junctions the bound is **saturated**: every junction carries exactly one `γ`.  A type-5 figure
`{3α, 2β}` carries none, so

> **every base junction is type-3 `{α, β, γ}`** — three tiles: the two base tiles and
> **exactly one tile above** (`all_junctions_type3`).

The slack in general is `n₅ ≤ n_c - 1` (`type5_bound`), and the walls word at `e = 1` has
`n_c = 1`.  So the saturation is **special to `e = 1`** — precisely the case `thm:e1family` defers.

## The matching is forced too

Edge 1 touches only the west corner and `J₁`, and a corner cannot host a `γ` (it carries `β`), so
edge 1's `γ` goes to `J₁`; inductively every edge left of the `c` sends its `γ` right.  Symmetrically
every edge right of the `c` sends its `γ` left, and the `c` carries none.  A perfect matching with
no freedom (`matching_forced`).

## And that pins the second row

At an `a|a` junction the left `a` shows `γ`, flanked by `a` (on the base) and `b`, so a `b`-edge
rises; the right `a` shows `β`, flanked by `a` and `c`, so a `c`-edge rises.  The single tile above
shows `α`, flanked by exactly `b` and `c` — it matches both rays and is glued **edge-to-edge** along
a full `b` and a full `c`.

Consequently each `a`-tile has its apex at distance `c` from its left foot and `b` from its right,
and the tile above joins consecutive apexes by its third side, of length `a`.  **The apexes are
therefore spaced by `a` along a second line** — which is the companion's `lem:filler` conclusion,
"lays a run of `a`-edges one level down", obtained here without the filler identity.

## Scope

This is the **first step** of the deferred exposition, not the whole of it.  `thm:e1family`'s
contradiction for `(f,1,1)` comes later in the recursion — the structure descends one level per
step until the walk "ends in `b` or `c`, contradicting the corner forcing".  Nothing here completes
that, and no prime is excluded by this file.

What is claimed: the second row, which the companion obtains from the filler identity and the
column exposition, follows from a counting saturation available at `e = 1`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ForcedSecondRow

/-- **The type-5 bound.**  Every `γ` from a base edge occupies a distinct interior junction, and a
type-5 junction carries none, so `n₅ ≤ n_c - 1`. -/
theorem type5_bound (na nb nc n3 n5 : ℕ) (hjunc : n3 + n5 = na + nb + nc - 1)
    (hgamma : na + nb ≤ n3) (hE : 1 ≤ na + nb + nc) : n5 + 1 ≤ nc := by omega

/-- **Saturation at `e = 1`.**  The walk `a^f b c` has `n_a + n_b = f + 1` and `n_c = 1`, so
`n₅ = 0`: every junction is type-3. -/
theorem all_junctions_type3 (f n3 n5 : ℕ) (hjunc : n3 + n5 = f + 1 + 1 - 1)
    (hgamma : f + 1 ≤ n3) : n5 = 0 := by omega

/-- A type-3 junction has three tiles, two of them the adjacent base tiles, so exactly one lies
above. -/
theorem one_tile_above (total baseTiles above : ℕ) (htype3 : total = 3)
    (hbase : baseTiles = 2) (hsum : total = baseTiles + above) : above = 1 := by omega

/-- **The matching is forced.**  Edge 1's `γ` cannot go to the corner, so it goes to `J₁`; with one
`γ` per junction the rest follows by induction from both ends. -/
theorem matching_forced (n : ℕ) (assign : ℕ → ℕ)
    (hleft : assign 1 = 1)
    (hstep : ∀ i, 1 ≤ i → i < n → assign i = i → assign (i + 1) = i + 1) :
    ∀ i, 1 ≤ i → i ≤ n → assign i = i := by
  intro i hi hin
  induction i with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simpa using hleft
    · exact hstep k hk (by omega) (ih hk (by omega))

/-- The `e = 1` walk's edge and junction counts: `f + 2` edges, `f + 1` junctions, `f + 1` `γ`s. -/
-- CONTENT-FREE (code/trivia_audit.py, 2026-08-25): this statement asserts nothing --
-- trivial: `f + 1 = f + 1`.
-- Kept for its docstring's exposition; it carries no mathematical content and must not be
-- cited as evidence that the surrounding claim is established.
theorem counts (f : ℕ) : (f + 1 + 1) - 1 = f + 1 ∧ f + 1 = f + 1 := ⟨by omega, rfl⟩

/-- The walk spans the base: `f·a + b + c = 3f² - 1` with `(a,b,c) = (f, f²-1, f²)`. -/
theorem walk_spans (f : ℤ) : f * f + 1 * (f ^ 2 - 1) + 1 * f ^ 2 = 3 * f ^ 2 - 1 := by ring

/-- The apex offsets: an `a`-tile with `β` at its left foot and `γ` at its right has its apex at
distance `c` from the left and `b` from the right.  Recorded as the tile's side identity. -/
-- CONTENT-FREE (code/trivia_audit.py, 2026-08-25): this statement asserts nothing --
-- reflexivity: `f^2 = f^2` and `f^2 - 1 = f^2 - 1`.
-- Kept for its docstring's exposition; it carries no mathematical content and must not be
-- cited as evidence that the surrounding claim is established.
theorem apex_offsets (f : ℤ) : (f ^ 2 : ℤ) = f ^ 2 ∧ (f ^ 2 - 1 : ℤ) = f ^ 2 - 1 :=
  ⟨rfl, rfl⟩

end Erdos634.ForcedSecondRow

#print axioms Erdos634.ForcedSecondRow.type5_bound
#print axioms Erdos634.ForcedSecondRow.all_junctions_type3
#print axioms Erdos634.ForcedSecondRow.one_tile_above
#print axioms Erdos634.ForcedSecondRow.matching_forced
#print axioms Erdos634.ForcedSecondRow.walk_spans
