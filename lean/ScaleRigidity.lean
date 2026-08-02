/-
ScaleRigidity.lean — the A9 scale-rigidity no-go for the base-`β` branch (Erdős #634).
No imports, no axioms: kernel-checked with the core toolchain only (`omega`, `decide`, `rfl`).

Erdős #634. The last open branch is base-`β`: the tile `(ef, f²−e², f²)` cutting the isosceles
target with equal side `f³m` and base `e(3f²−e²)m` into `N = m²(3f²−e²)` pieces. A prime `N` forces
`m = 1`, so the whole remaining problem is the single case `m = 1`.

THE INSTANCE. At `(e,f) = (1,2)` the tile is `(2,3,4)` and the family is target `(8m, 8m, 11m)`
with `N = 11m²`:

  m = 1 : target (8,8,11)   N = 11  no tiling (exhaustive search; NOT formalized, and NOT used below)
  m = 2 : target (16,16,22) N = 44  tiling exists — Tiling44.lean, kernel-checked, zero axioms
  m = 3 : target (24,24,33) N = 99  tiling exists — Tiling99.lean, kernel-checked, zero axioms

The three targets are similar and the tile is identical: only the ratio of target size to tile size
differs. `target_similar` is that arithmetic.

THE NO-GO. `no_similarity_invariant_proof` is proved abstractly: a criterion that depends only on
data ignoring the target's size (any invariant of the two similarity classes separately — angles,
the direction group, vertex angle arithmetic, Dehn-type invariants), and that is sound for
non-tileability, cannot fire on an instance whose target has a tileable enlargement. Applied to the
table with `k = 2`: no such criterion can settle `m = 1`, since it would equally exclude `m = 2` and
contradict `Tiling44`. Only the EXISTENCE at `m = 2` is used; the `m = 1` non-existence is an
exhaustive-search result and is deliberately not a hypothesis anywhere in this file.

WHAT SURVIVES. Only scale-sensitive tools can separate the cases. `side_no_b_m1` proves that at
`m = 1` every admissible equal-side walk is free of `b`-edges; `side_b_exists_m2` exhibits an
admissible walk carrying `b`-edges at `m = 2`. So that statement, unlike every angle-based one,
genuinely distinguishes the impossible case from the possible one.
-/

namespace Erdos634.ScaleRigidity

/-! ## 1. The general no-go -/

/--
No criterion that ignores the target's size can certify non-tileability of an instance whose
target has a tileable enlargement.

* `Tileable T S` — `S` can be cut into finitely many congruent copies of `T`.
* `scale k S`    — `S` enlarged by `k`, hence similar to `S`.
* `data T S`     — everything the criterion is allowed to look at.
* `hdata`        — the criterion's data does not see the enlargement. This is exactly what
                   "similarity-invariant", "angle-only", "direction group" and "Dehn-type"
                   have in common.
* `hsound`       — the criterion is sound: when it fires, there is no tiling.

Conclusion: it does not fire on `(T, S)`. Contrapositively, a criterion that *does* fire on some
`(T, S)` must be sensitive to the size ratio, i.e. it must distinguish `S` from its enlargements.
-/
theorem no_similarity_invariant_proof
    {Tile Target Data Scale : Type}
    (Tileable : Tile → Target → Prop)
    (scale : Scale → Target → Target)
    (data : Tile → Target → Data)
    (hdata : ∀ (k : Scale) (T : Tile) (S : Target), data T (scale k S) = data T S)
    (P : Data → Prop)
    (hsound : ∀ (T : Tile) (S : Target), P (data T S) → ¬ Tileable T S)
    (T : Tile) (S : Target) (k : Scale)
    (hbig : Tileable T (scale k S)) :
    ¬ P (data T S) := by
  intro hP
  refine hsound T (scale k S) ?_ hbig
  rw [hdata k T S]
  exact hP

/-! ## 2. The instance: similar targets, identical tile -/

/-- Equal side of the `m`-th target of the `(e,f) = (1,2)` family: `f³m = 8m`. -/
def side (m : Nat) : Nat := 8 * m

/-- Base of the `m`-th target: `e(3f²−e²)m = 11m`. -/
def base (m : Nat) : Nat := 11 * m

/-- Tile count of the `m`-th member: `m²(3f²−e²) = 11m²`. -/
def count (m : Nat) : Nat := 11 * (m * m)

/-- The targets of the family are pairwise similar: the `m`-th is the `m`-fold enlargement of the
first. Similarity of the targets, with the tile held fixed, is the hypothesis `hdata` of the no-go. -/
theorem target_similar (m : Nat) : side m = m * side 1 ∧ base m = m * base 1 := by
  unfold side base
  omega

/-- The three members named in the table: targets `(8,8,11)`, `(16,16,22)`, `(24,24,33)`. -/
theorem targets_concrete :
    side 1 = 8 ∧ base 1 = 11 ∧ side 2 = 16 ∧ base 2 = 22 ∧ side 3 = 24 ∧ base 3 = 33 := by
  unfold side base
  decide

/-- The counts: `11` (no tiling), `44` and `99` (tilings exist, kernel-checked elsewhere). -/
theorem counts_concrete : count 1 = 11 ∧ count 2 = 44 ∧ count 3 = 99 := by
  unfold count
  decide

/-! ## 3. The scale-sensitive arithmetic that survives

A side of the target is partitioned into whole tile edges, so its edge multiset `(P,Q,R)` of `a`-,
`b`- and `c`-edges solves `P·a + Q·b + R·c = |side|`. For the tile `(2,3,4)` an *admissible* walk
also satisfies the two sound prunes carried by the engine:

* the `γ`-injection bound `R ≥ 1` (`BaseBetaWalks.lean`),
* the corner-parallelogram rule `Q + 2 ≤ P + Q + R` on an equal side.
-/

/-- **`side_no_b` at `m = 1`.** The equal side has length `8`, and every admissible walk on it is
free of `b`-edges. This is the scale-sensitive input: exactly what fails at `m ≥ 2`. -/
theorem side_no_b_m1 (P Q R : Nat)
    (hlen : 2 * P + 3 * Q + 4 * R = 8) (hR : 1 ≤ R) (hcorner : Q + 2 ≤ P + Q + R) :
    Q = 0 := by
  omega

/-- **`side_no_b` fails at `m = 2`.** The side has length `16` and `(P,Q,R) = (3,2,1)` is admissible
while carrying two `b`-edges. Hence `side_no_b` is not a consequence of any scale-invariant fact,
and it genuinely separates `m = 1` from `m = 2`. -/
theorem side_b_exists_m2 :
    2 * 3 + 3 * 2 + 4 * 1 = 16 ∧ 1 ≤ 1 ∧ 2 + 2 ≤ 3 + 2 + 1 ∧ 2 ≠ 0 := by
  decide

/-- The same failure at `m = 3` (side length `24`), for the record. -/
theorem side_b_exists_m3 :
    2 * 7 + 3 * 2 + 4 * 1 = 24 ∧ 1 ≤ 1 ∧ 2 + 2 ≤ 7 + 2 + 1 ∧ 2 ≠ 0 := by
  decide

end Erdos634.ScaleRigidity
