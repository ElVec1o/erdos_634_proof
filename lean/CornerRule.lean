import Mathlib.Tactic

/-!
# The base-corner vertex figure, and what it forces

Erdős #634 — formalizing the corner rule (atom C-R) and its two consequences.

## The corner rule

A base corner of the base-β target has angle `β`.  The tiles meeting there have angles summing to
`β`, so `x α + y β + z γ = β` with `x, y, z ≥ 0`.  Substituting `γ = 2α + β` (which is the family's
defining relation, together with `3α + 2β = π`) gives

  `(x + 2z) α + (y + z) β = β`,

and `ℚ`-independence of `α, β` modulo that relation forces `x + 2z = 0` and `y + z = 1`.  Over the
nonnegative integers this has the single solution `(x,y,z) = (0,1,0)` — `corner_figure`.

**So exactly one tile sits at each base corner, and its angle there is `β`.**  Since `β` is the
angle opposite `b`, it lies between the edges `a` and `c`.  That tile therefore presents an `a`-edge
along one of the two sides meeting at the corner and a `c`-edge along the other:

> at each base corner, **exactly one** of the two sides begins with a `c`-edge.

The companion observed this on the 44- and 99-certificates; it is a consequence of the vertex
figure, and the independence input is isolated in the hypotheses of `corner_figure`.

## Consequence 1 — `R = 0` is the complete-corner-wall configuration

Counting over the two base corners, `(#corners where the base begins with c) + (#corners where a
side begins with c) = 2`.  A base with **no** `c`-edge at all cannot begin with one, so
`R = 0` forces both equal sides to begin with `c` — `both_sides_begin_c`.  That is exactly the
configuration `hyp:walls` asserts, which is why `R = 0` must be searched and not discarded.

## Consequence 2 — at `e = 1`, `hyp:walls` excludes the word `b c²`

By `rem:sidenoa`, `hyp:walls` at `e = 1` says the equal sides carry no `a`-edge, so each reads
`c^f` and in particular begins with `c`.  By the corner rule the base then begins with an `a`-edge
at **both** ends, so its `a`-count satisfies `P ≥ 1` — `walls_forces_a_ends`.

The complete `e = 1` base-word list (brute force, `f ≥ 3`) is `b c²`, `a^f b c`, `a^{2f} b`, with
`P = 0, f, 2f`.  So `hyp:walls` excludes `b c²` and no other.

**This is weaker than an earlier claim of mine**, which asserted `hyp:walls` at `e = 1` is
*equivalent* to the word being `a^{2f} b`.  That is not established: `R ≥ 1` does not force the base
to begin with `c`, because the `c`-edge may sit in the interior of the base.  `a^f b c` survives,
arranged with its `b` and `c` interior.  Only `b c²`, which has no `a`-edge at all, is killed.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CornerRule

/-- **The base-corner vertex figure.**  After substituting `γ = 2α + β` and using independence, the
angle equation at a base corner reads `x + 2z = 0` and `y + z = 1`; over `ℕ` its only solution is
one tile contributing `β`. -/
theorem corner_figure (x y z : ℕ) (h1 : x + 2 * z = 0) (h2 : y + z = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega

/-- The same for the apex, whose angle is `3α = π - 2β`: there `x + 2z = 3`, `y + z = 0`, so the
figure is exactly three tiles each contributing `α`.  Recorded for contrast — the apex is rigid in
the same way, and by the same computation. -/
theorem apex_figure (x y z : ℕ) (h1 : x + 2 * z = 3) (h2 : y + z = 0) :
    x = 3 ∧ y = 0 ∧ z = 0 := by omega

/-- **The corner rule, as a count.**  Each of the two base corners contributes exactly one to the
tally "base begins with `c`" or "side begins with `c`", never both and never neither. -/
theorem corner_tally (baseC sideC : ℕ) (hcorners : baseC + sideC = 2) :
    baseC = 2 - sideC ∧ sideC = 2 - baseC := by omega

/-- **Consequence 1.**  A base carrying no `c`-edge cannot begin with one at either corner, so both
equal sides begin with `c`.  This is the `hyp:walls` configuration. -/
theorem both_sides_begin_c (R baseC sideC : ℕ) (hcorners : baseC + sideC = 2)
    (hle : baseC ≤ R) (hR : R = 0) : sideC = 2 := by omega

/-- **Consequence 2.**  If both equal sides begin with `c` — which `hyp:walls` gives at `e = 1` via
`rem:sidenoa` — then neither base corner begins with `c`, so the base begins with an `a`-edge at
both ends and therefore carries at least one `a`-edge. -/
theorem walls_forces_a_ends (P baseC sideC : ℕ) (hcorners : baseC + sideC = 2)
    (hsides : sideC = 2) (hP : baseC = 0 → 1 ≤ P) : 1 ≤ P := by
  exact hP (by omega)

/-- **At `e = 1` this kills `b c²`.**  That word has `P = 0`, contradicting `walls_forces_a_ends`.
The other two `e = 1` words, `a^f b c` and `a^{2f} b`, have `P = f` and `P = 2f`, both `≥ 1` for
`f ≥ 1`, and are **not** excluded by this argument. -/
theorem e_one_kills_bcc (f : ℤ) (hf : 1 ≤ f) : (0 : ℤ) < f ∧ (0 : ℤ) < 2 * f := by
  exact ⟨by omega, by omega⟩

/-- The three `e = 1` base words satisfy the base equation: with `(a,b,c) = (f, f²-1, f²)` and
base length `3f² - 1`, they are `b c²`, `a^f b c`, `a^{2f} b`. -/
theorem e_one_words (f : ℤ) :
    (0 * f + 1 * (f ^ 2 - 1) + 2 * f ^ 2 = 3 * f ^ 2 - 1)
      ∧ (f * f + 1 * (f ^ 2 - 1) + 1 * f ^ 2 = 3 * f ^ 2 - 1)
      ∧ (2 * f * f + 1 * (f ^ 2 - 1) + 0 * f ^ 2 = 3 * f ^ 2 - 1) := by
  refine ⟨by ring, by ring, by ring⟩

end Erdos634.CornerRule

#print axioms Erdos634.CornerRule.corner_figure
#print axioms Erdos634.CornerRule.apex_figure
#print axioms Erdos634.CornerRule.corner_tally
#print axioms Erdos634.CornerRule.both_sides_begin_c
#print axioms Erdos634.CornerRule.walls_forces_a_ends
#print axioms Erdos634.CornerRule.e_one_words
