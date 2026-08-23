import Mathlib.Tactic

/-!
# The `e = 1` case analysis, assembled from the companion's own results

Erdős #634 — auditing whether `hyp:walls` at `e = 1` follows from statements already in the
companion.  This file asserts nothing new: it records the case split and checks it is exhaustive,
so that if any input is narrower than its printed statement, the failure is localised to one row.

## The two escape routes

`conj:advance` fixes the scope: "The two ways a branch escapes the collision in the general argument
are exactly: a deviating `a`-run whose new `c`-chord ends beyond the forced region (Route 1), and an
initial side `c`-block of length at least `2` (Route 2).  Any proof of the general case must close
these two gaps and no others."

## The three inputs, as printed

* **D** — `prop:doublec` with `rem:doublecscope`: a side carrying an `a`-edge whose initial
  `c`-block has length `j ≥ 2` is impossible; "escape route 2 is closed at every initial block
  length, for every `f ≥ 3`".  Its bound `j ≤ f-1` is satisfied whenever `p ≥ 1`, since then the
  side has at most `f-1` `c`-edges.
* **C** — `thm:e1cascade`: a side carrying an `a`-edge whose first run sits behind exactly one
  `c`-edge is impossible, **provided** the opposite side has no `a`-edge or also has initial block
  `1`.  Its part (L3) disposes of Route 1 by the mirror: a word whose `c` precedes its `b` reverses
  to one whose `b` precedes its `c`, and the mirrored cascade from the opposite corner kills it.
* **Z** — `rem:sidenoa`: `p = 0` closes the subfamily outright, since complete blocks force the base
  to read `a^f b c` and end in a `c`, while `thm:e1reduce` forces `a`-edges at both ends.

## The case split

Write `(p, ℓ)` for each equal side: `p` its `a`-parameter, `ℓ` its initial `c`-block length.
`ℓ = f` exactly when `p = 0`.

| case | side L | side R | closed by |
|---|---|---|---|
| 1 | `p = 0` | `p = 0` | **Z** |
| 2 | `p ≥ 1`, `ℓ ≥ 2` | any | **D** |
| 3 | any | `p ≥ 1`, `ℓ ≥ 2` | **D** |
| 4 | `p ≥ 1`, `ℓ = 1` | `p = 0` | **C** |
| 5 | `p ≥ 1`, `ℓ = 1` | `p ≥ 1`, `ℓ = 1` | **C** |

Cases 2 and 3 absorb every configuration in which some side has `p ≥ 1` and `ℓ ≥ 2`, which is
exactly what makes **C**'s opposite-side hypothesis available in cases 4 and 5.  `exhaustive` below
checks there is no sixth case.

## Status

**This is an audit, not a claim.**  The companion does not assert `hyp:walls` at `e = 1` in general:
`cor:walls15` and `cor:walls16` establish `f = 5` and `f = 6` using `thm:elltwo` and a window
argument, which would be redundant if the split above were complete as printed.  So either the
`f ≤ 6` status text predates the general forms of **D** and **C**, or one of them is narrower than
its statement reads.  The Lean below settles only the combinatorics of the split; it cannot settle
which.  Nothing downstream is claimed until that is resolved.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ThinCaseAnalysis

/-- A side, recorded by its `a`-parameter and initial `c`-block length. -/
structure Side where
  p : ℕ
  l : ℕ

/-- `p = 0` means the side is `c^f`, i.e. the block is the whole side. -/
def pureC (f : ℕ) (s : Side) : Prop := s.p = 0 ∧ s.l = f

/-- **The split is exhaustive.**  For any pair of sides, at least one of the five cases applies:
either both are pure `c`, or some side has `p ≥ 1` with block `≥ 2`, or every side with `p ≥ 1` has
block exactly `1`. -/
theorem exhaustive (L R : Side) (hL : 1 ≤ L.l) (hR : 1 ≤ R.l) :
    (L.p = 0 ∧ R.p = 0)
      ∨ (1 ≤ L.p ∧ 2 ≤ L.l) ∨ (1 ≤ R.p ∧ 2 ≤ R.l)
      ∨ (1 ≤ L.p ∧ L.l = 1 ∧ R.p = 0)
      ∨ (1 ≤ R.p ∧ R.l = 1 ∧ L.p = 0)
      ∨ (1 ≤ L.p ∧ L.l = 1 ∧ 1 ≤ R.p ∧ R.l = 1) := by
  rcases Nat.eq_zero_or_pos L.p with hLp | hLp
  · rcases Nat.eq_zero_or_pos R.p with hRp | hRp
    · exact Or.inl ⟨hLp, hRp⟩
    · rcases Nat.lt_or_ge R.l 2 with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hRp, by omega, hLp⟩))))
      · exact Or.inr (Or.inr (Or.inl ⟨hRp, h⟩))
  · rcases Nat.lt_or_ge L.l 2 with h | h
    · rcases Nat.eq_zero_or_pos R.p with hRp | hRp
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hLp, by omega, hRp⟩)))
      · rcases Nat.lt_or_ge R.l 2 with h2 | h2
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hLp, by omega, hRp, by omega⟩))))
        · exact Or.inr (Or.inr (Or.inl ⟨hRp, h2⟩))
    · exact Or.inr (Or.inl ⟨hLp, h⟩)

/-- **`D`'s bound is available.**  `prop:doublec` needs `j ≤ f-1`; a side with `p ≥ 1` has at most
`f-1` `c`-edges, so its block satisfies that bound. -/
theorem doublec_bound_ok (f p l : ℕ) (hp : 1 ≤ p) (hl : l ≤ f - p) : l ≤ f - 1 := by omega

/-- **The assembly.**  Given the three inputs on their stated domains, no configuration survives. -/
theorem no_configuration_survives
    (f : ℕ) (L R : Side) (hL : 1 ≤ L.l) (hR : 1 ≤ R.l)
    (Z : L.p = 0 → R.p = 0 → False)
    (D : ∀ s : Side, 1 ≤ s.p → 2 ≤ s.l → False)
    (C : ∀ s t : Side, 1 ≤ s.p → s.l = 1 → (t.p = 0 ∨ t.l = 1) → False) :
    False := by
  rcases exhaustive L R hL hR with h | h | h | h | h | h
  · exact Z h.1 h.2
  · exact D L h.1 h.2
  · exact D R h.1 h.2
  · exact C L R h.1 h.2.1 (Or.inl h.2.2)
  · exact C R L h.1 h.2.1 (Or.inl h.2.2)
  · exact C L R h.1 h.2.1 (Or.inr h.2.2.2)

end Erdos634.ThinCaseAnalysis

#print axioms Erdos634.ThinCaseAnalysis.exhaustive
#print axioms Erdos634.ThinCaseAnalysis.doublec_bound_ok
#print axioms Erdos634.ThinCaseAnalysis.no_configuration_survives
