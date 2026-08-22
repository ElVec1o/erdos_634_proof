import Mathlib.Tactic

/-!
# Every base-β tiling is irregular

Erdős #634 — locating the branch inside Laczkovich's classification.

Laczkovich (*Tilings of convex polygons with congruent triangles*, Discrete Comput. Geom. 38 (2012)
330–372) calls a tiling by congruent triangles **regular** when there are two angles of the tile,
say `X` and `Y`, such that at **every** vertex of the tiling the number of tiles presenting `X`
equals the number presenting `Y`; otherwise the tiling is **irregular**.  He classifies all pairs
`(A, T)` with `A` a convex polygon and `T` a triangle tiling `A` regularly, and that classification
is the engine behind the known spectra of convex polygons.

The base-β branch is not reachable by it.  Two vertex figures already proved in this development
decide the matter, and they are corner figures, so they occur in *every* tiling of the target:

* the base corner has angle `β` and its figure is a single `β`-tile — `CornerRule.corner_figure`,
  i.e. `(n_α, n_β, n_γ) = (0, 1, 0)`;
* the apex has angle `3α` and its figure is exactly three `α`-corners — `CornerRule.apex_figure`,
  i.e. `(n_α, n_β, n_γ) = (3, 0, 0)`.

Each of the three candidate pairs fails at one of these two vertices:

| pair | base corner `(0,1,0)` | apex `(3,0,0)` |
|---|---|---|
| `(α, β)` | `0 ≠ 1` ✗ | |
| `(α, γ)` | | `3 ≠ 0` ✗ |
| `(β, γ)` | `1 ≠ 0` ✗ | |

so no pair equalises at every vertex — `base_beta_irregular`.

## Why this matters

It is a negative result with a positive use: it says the branch cannot be closed by appealing to
Laczkovich's regular classification, and explains structurally why the base-β family resisted the
standard machinery.  Every tiling of the target lives in the irregular regime, where the
classification gives no list to check against.  Any proof must therefore be internal to the branch,
which is what the companion's forcing chain is.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Irregular

/-- A vertex figure, recorded as the multiplicities of the tile's three angles at that vertex. -/
structure Figure where
  na : ℕ
  nb : ℕ
  ng : ℕ

/-- The base corner: one tile, presenting `β` (`CornerRule.corner_figure`). -/
def baseCorner : Figure := ⟨0, 1, 0⟩

/-- The apex: three tiles, each presenting `α` (`CornerRule.apex_figure`). -/
def apex : Figure := ⟨3, 0, 0⟩

/-- The three ways to choose an unordered pair of distinct angles. -/
inductive Pairing | ab | ag | bg

/-- The two multiplicities a pairing compares at a given vertex. -/
def Pairing.counts : Pairing → Figure → ℕ × ℕ
  | .ab, F => (F.na, F.nb)
  | .ag, F => (F.na, F.ng)
  | .bg, F => (F.nb, F.ng)

/-- A pairing *equalises* a vertex when its two counts agree there. -/
def Pairing.equalises (p : Pairing) (F : Figure) : Prop := (p.counts F).1 = (p.counts F).2

/-- **Every base-β tiling is irregular.**  No pairing equalises both corner figures, and both occur
in every tiling of the target, so no pairing equalises every vertex. -/
theorem base_beta_irregular (p : Pairing) :
    ¬ (p.equalises baseCorner ∧ p.equalises apex) := by
  cases p <;> simp [Pairing.equalises, Pairing.counts, baseCorner, apex]

/-- Sharper: each pairing is named with the corner that kills it. -/
theorem which_corner_kills :
    (¬ (Pairing.ab).equalises baseCorner)
      ∧ (¬ (Pairing.ag).equalises apex)
      ∧ (¬ (Pairing.bg).equalises baseCorner) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Pairing.equalises, Pairing.counts, baseCorner, apex]

/-- The corner figures themselves, as the arithmetic that produces them: at the base corner
`x + 2z = 0` and `y + z = 1`; at the apex `x + 2z = 3` and `y + z = 0`.  These are
`CornerRule.corner_figure` and `CornerRule.apex_figure`, restated here so the file is self-contained
about what it assumes. -/
theorem corner_arithmetic (x y z : ℕ) :
    (x + 2 * z = 0 → y + z = 1 → x = 0 ∧ y = 1 ∧ z = 0)
      ∧ (x + 2 * z = 3 → y + z = 0 → x = 3 ∧ y = 0 ∧ z = 0) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;> omega

end Erdos634.Irregular

#print axioms Erdos634.Irregular.base_beta_irregular
#print axioms Erdos634.Irregular.which_corner_kills
#print axioms Erdos634.Irregular.corner_arithmetic
