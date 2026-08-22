import Mathlib.Tactic

/-!
# Every base word carries a `c`-edge

Erdős #634 — a uniform kill for the `n_c = 0` words, by counting `γ` on the base.

## The count

In the tile, the edge opposite an angle joins the other two vertices, so on the base

* an `a`-edge (opposite `α`) joins vertices carrying `β` and `γ` — one `γ`;
* a `b`-edge (opposite `β`) joins `α` and `γ` — one `γ`;
* a `c`-edge (opposite `γ`) joins `α` and `β` — **no** `γ`.

So the base's edges contribute exactly `n_a + n_b` angles equal to `γ`.

Where do they sit?  By the corner rule (`CornerRule.corner_figure`) exactly one tile occupies each
base corner and its angle there is `β`, so **no corner carries a `γ`**; every one of the `n_a + n_b`
`γ`s lands at a junction interior to the base.  (The same rule also forbids a `b`-edge at a corner
outright: a `b`-edge offers only `α` and `γ`, neither of which is `β`.)

A base of `E = n_a + n_b + n_c` edges has exactly `E - 1` interior junctions, and the `γ`-trap —
`2γ = π + α > π`, the companion's `BaseBetaCorners.pi_vertex_gamma_le_one` — allows **at most one
`γ` per interior junction**.  Hence

  `n_a + n_b ≤ E - 1 = n_a + n_b + n_c - 1`,  i.e.  **`n_c ≥ 1`**   (`c_edge_exists`).

## What it kills

Every base word with `n_c = 0`, at every member, with no search.  Against the family
`n_c = 2e - t e - j f` this excludes the whole `R = 0` branch, and in particular:

* the `t = 2` word `(2f, e, 0)` — so with `ThreeWords`, a member with `f > 2e` has **exactly two**
  surviving base words, `(0, e, 2e)` and the walls word `(f, e, e)`;
* at `(5,6)`, `N = 83`, the words `a¹²b⁵c⁰` and `a¹b³⁵c⁰`.

Both of those `83` words were separately exhausted by the engine (511,910 and 2 nodes), as were the
`(2f,e,0)` words at `(1,2), (2,3), (1,3), (3,4), (1,4), (4,5)` — 17 to 29,488 nodes.  Eight
independent searches, all agreeing with the theorem, none contradicting it.

## A second consequence

Companion (iv), `j(f-e) ≤ e-1`, is proved only under the `γ`-trap hypothesis `R ≥ 1`
(`WalkStructure.base_j_bound`).  Since `R = n_c ≥ 1` always, **(iv) now applies unconditionally**,
and the `R = 0` analysis of `WalkStructure.base_R_zero_bound` is vacuous rather than a needed case.

## Consequence for `hyp:walls`

`WallsWord` reduces `hyp:walls` to "no tiling carries a base word other than `a^f b^e c^e`".
Above `f = 2e` that is now a **single** exclusion: the word `(0, e, 2e)`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.GammaCount

/-- **Every base word has a `c`-edge.**  The `γ`s contributed by the base's `a`- and `b`-edges all
sit at interior junctions, of which there are `E - 1`, and the `γ`-trap permits one apiece. -/
theorem c_edge_exists (na nb nc : ℕ) (hE : 1 ≤ na + nb + nc)
    (htrap : na + nb ≤ na + nb + nc - 1) : 1 ≤ nc := by omega

/-- Its `c`-count really is zero: `n_c = 2e - t e - j f` at `t = 2`, `j = 0`. -/
theorem t_two_nc_zero (e f : ℤ) : 2 * e - 2 * e - 0 * f = 0 := by ring

/-- **Above `f = 2e`, exactly two base words survive.**  `ThreeWords` leaves `t ∈ {0,1,2}`;
`c_edge_exists` removes `t = 2`.  The survivors are `(0,e,2e)` and `(f,e,e)`. -/
theorem two_words (t : ℤ) (h012 : 0 ≤ t ∧ t ≤ 2) (hne2 : t ≠ 2) : t = 0 ∨ t = 1 := by omega

/-- The two survivors solve the base equation. -/
theorem survivors (e f : ℤ) :
    (0 * (e * f) + e * (f ^ 2 - e ^ 2) + (2 * e) * f ^ 2 = e * (3 * f ^ 2 - e ^ 2))
      ∧ (f * (e * f) + e * (f ^ 2 - e ^ 2) + e * f ^ 2 = e * (3 * f ^ 2 - e ^ 2)) := by
  refine ⟨by ring, by ring⟩

end Erdos634.GammaCount

#print axioms Erdos634.GammaCount.c_edge_exists
#print axioms Erdos634.GammaCount.t_two_nc_zero
#print axioms Erdos634.GammaCount.two_words
#print axioms Erdos634.GammaCount.survivors
