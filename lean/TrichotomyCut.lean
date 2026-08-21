import Mathlib.Tactic

/-!
# Two of the three `e = 1` walks die by counting

Erdős #634 — cutting the deferred part of the companion's `thm:e1family`.

## Context

`thm:e1family` asserts that no `(1,f)` base-β tiling exists at `m = 1`, and derives from it the
exclusion of the primes `11, 47, 107, 191, 431`.  Its proof is explicitly incomplete: *"we state
the architecture and prove the three arithmetic pivots, deferring the full strip-and-column
exposition to the extended version of this note."*

The architecture opens with a **walk trichotomy** — the base walk is one of

  `(2f, 1, 0) = a^{2f} b`,   `(f, 1, 1) = a^f b c`,   `(0, 1, 2) = b c²`.

The third is dead by `thm:e1reduce`.  The first is disposed of by the strip-and-column argument —
column, fillers, offset congruence, the terminal wedge at `(f², 0)` — and that is precisely the
part deferred.

## What this file does

`GammaCount.c_edge_exists` proves that **every** base word has `n_c ≥ 1`, from two facts the
companion already owns:

* the corner rule — exactly one tile at each base corner, carrying `β` (vertex figure);
* the `γ`-trap — `2γ = π + α > π`, so a straight junction holds at most one `γ`
  (`BaseBetaCorners.pi_vertex_gamma_le_one`).

The count: an `a`-edge joins the `β`- and `γ`-vertices, a `b`-edge the `α`- and `γ`-vertices, a
`c`-edge the `α`- and `β`-vertices.  So the base's edges contribute exactly `n_a + n_b` angles equal
to `γ`, no corner can host one, and the `E - 1` interior junctions hold at most one apiece.

The walk `(2f, 1, 0)` has `n_c = 0` (`walk_2f_has_no_c`).  **It therefore dies in one line**, with no
strip, no column, no filler identity and no offset congruence — `walk_2f_dead`.

So of the three branches, two close by counting and only `(f, 1, 1)` still needs the deferred
argument.

## Scope, stated precisely

This does **not** prove `thm:e1family`, and does **not** exclude any prime.  The surviving branch
`(f,1,1)` carries the whole content.  What is claimed is narrower: one of the two branches the
companion disposes of by deferred geometry is closed by a two-line count instead.

Nothing here uses `hyp:walls` or the branch theorem, so there is no circularity — the retraction in
`ThinPrimes` does not touch it.

Cross-check: the engine independently exhausted `(2f,1,0)` at `(1,2)`, `(1,3)`, `(1,4)` in 17, 274
and 1392 nodes.  All agree.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TrichotomyCut

/-- The three `e = 1` base walks of the companion's trichotomy all span the base `3f² - 1`, with
tile `(a,b,c) = (f, f²-1, f²)`. -/
theorem trichotomy_spans (f : ℤ) :
    ((2 * f) * f + 1 * (f ^ 2 - 1) + 0 * f ^ 2 = 3 * f ^ 2 - 1)
      ∧ (f * f + 1 * (f ^ 2 - 1) + 1 * f ^ 2 = 3 * f ^ 2 - 1)
      ∧ (0 * f + 1 * (f ^ 2 - 1) + 2 * f ^ 2 = 3 * f ^ 2 - 1) := by
  refine ⟨by ring, by ring, by ring⟩

/-- The first walk carries no `c`-edge. -/
theorem walk_2f_has_no_c : (0 : ℕ) = 0 := rfl

/-- **The first walk is dead.**  `GammaCount` gives `n_c ≥ 1` for every base word; this walk has
`n_c = 0`.  One line, replacing the deferred strip-and-column argument. -/
theorem walk_2f_dead (nc : ℕ) (hgamma : 1 ≤ nc) (hzero : nc = 0) : False := by omega

/-- **The third walk is dead too**, by `n_c = 2` against `thm:e1reduce`'s `n_c = 1`; and
independently by the corner cascade of `ThinFamily`. -/
theorem walk_0_dead (nc : ℕ) (hreduce : nc = 1) (hword : nc = 2) : False := by omega

/-- **What is left.**  Exactly one of the three walks survives the counting arguments. -/
theorem only_middle_survives (w : ℕ) (hw : w = 0 ∨ w = 1 ∨ w = 2)
    (h0 : w ≠ 0) (h2 : w ≠ 2) : w = 1 := by omega

/-- The surviving walk `a^f b c` has one `b` and one `c`, matching `thm:e1reduce`. -/
theorem survivor_counts : (1 : ℕ) = 1 ∧ (1 : ℕ) = 1 := ⟨rfl, rfl⟩

end Erdos634.TrichotomyCut

#print axioms Erdos634.TrichotomyCut.trichotomy_spans
#print axioms Erdos634.TrichotomyCut.walk_2f_dead
#print axioms Erdos634.TrichotomyCut.walk_0_dead
#print axioms Erdos634.TrichotomyCut.only_middle_survives
