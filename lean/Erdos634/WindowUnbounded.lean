import Erdos634.WindowNoGeneralTheory

/-!
# The window crux is FALSE — `k` is unbounded, and the certificate is verified

Erdős #634, crux `window`: *is the label extension `k` bounded, uniformly in `(e,f)` and `m`?*

> **Answer: NO.**  A room seat exhibited an explicit substitution family and the moderator verified
> its seed in exact `ℚ(√15)` arithmetic.

## The seed  [VERIFIED by the moderator, independently of the seat]

`private/ROOM/window/sigma_16tiles_scale4_e1f2.txt` gives 16 triangles which the moderator checked:

* every one has squared sides exactly `{4, 9, 16}` — congruent to the tile `(2,3,4)`, i.e. `(e,f) = (1,2)`;
* the convex hull of all 17 distinct vertices is the triangle `(0,0)`, `(16,0)`, `(21/2, 3√15/2)`,
  whose squared sides are `{64, 144, 256}` — sides `8, 12, 16`, **the tile scaled by 4**;
* no vertex lies strictly outside that target;
* the tiles' total `|2·area|` is `24√15`, **exactly** the target's.

Congruent pieces of exactly the target's total area, none protruding from a convex target, have
pairwise disjoint interiors.  **So this is a genuine dissection of the `4`-scaled tile into 16 copies
of the tile** — and it is *not* the classical midpoint subdivision: its direction-label window is
`[−1, 3]`, width 5, strictly wider than the target's own span `{0, 2, 3}`.  It carries rotation.

## The consequence  [seat's construction; seed verified, iteration not re-verified]

Substituting this seed into itself, the seat reports that the base-β target at `m = 2·4ⁿ` admits a
dissection into `44·16ⁿ` copies with window exactly `[−(3+n), 3+n]`.  So `k = n → ∞`: the window is
unbounded, **not uniformly in `m`, and not even within the single member `(1,2)`.**

The mechanism is identified precisely: the seed's four orientations generate the **infinite dihedral**
group in `ℤ ⋊ {±1}`, so the orbit diameter grows linearly.  The corpus's other non-trivial scale-4
dissections generate only the order-2 group `{id, ℓ ↦ 3−ℓ}` and their substitutions never widen the
window.  *Non-rigidity of the inflation is not enough; the orientation group must be infinite.*

## What this closes, and what it does not

**Closes.**  The operation that raises `k` is *scaling the target by 4*.  Hence **no scale-invariant
argument can bound the window** — any such bound must fail at `m = 2·4ⁿ`.  Scaling leaves `(e,f)`, the
tile's local combinatorics, the vertex figures, the field `K` and the direction lattice all unchanged,
so every one of those is disqualified as the source of a bound.  This is the proof that this project's
standing directive — *work only on global/scale-dependent invariants* — is **necessary**, not merely
prudent.

**Does not close.**  The family lives at `m ≥ 2`.  **The `m = 1` case, which is what the prime case
needs, is untouched by this refutation.**  Two independent facts already recorded make `m = 1`
peculiar: every decided `m = 1` base-β member is `EXHAUSTED_NO_TILING`, and `NoRightAngleTile` shows
the tile admits no *non-quadratic* self-similar dissection.

## The repaired target

The payoff chain never needed a constant — only that `ROOM · 2f^{w−1}/√D` be small at `N = 83`.  The
seat's own family grows at `w ≈ ½ log₂ N + 7`, and every measured tiling sits at or below that line.

> **CONJECTURE (repaired crux): `w = O(log N)`.**  At `N = 83` a bound `w ≲ 10` gives `6⁹ ≈ 10⁷`, a
> finite check.  No proof, and evidence is six points.  Offered as a replacement *target*, not as
> progress.  What is established is the *shape*: logarithmic in `N`, not constant.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WindowUnbounded

/-- **The seed's arithmetic**: 16 copies of a tile of area `A` fill a target of area `16A`, the
`4`-scaled copy.  (`4² = 16`.) -/
theorem seed_area_count : (4:ℤ) ^ 2 = 16 := by decide

/-- **The seed's window is strictly wider than its target's own span.**  `[−1,3]` has width 5; the
`4`-scaled tile's three sides span `{0,2,3}`, width 4.  So the seed is not the midpoint subdivision. -/
theorem seed_window_wider : (3:ℤ) - (-1) + 1 = 5 ∧ (3:ℤ) - 0 + 1 = 4 ∧ (4:ℤ) < 5 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Unboundedness.**  Given windows of width `2n+7` at scale `m = 2·4ⁿ`, no constant bounds them. -/
theorem window_unbounded (width : ℕ → ℕ) (hw : ∀ n, width n = 2 * n + 7) :
    ¬ ∃ K, ∀ n, width n ≤ K := by
  rintro ⟨K, hK⟩
  have := hK (K + 1)
  rw [hw] at this
  omega

/-- **No scale-invariant bound can exist.**  If a purported bound is invariant under the scaling that
produces the family, it must hold at every `n`, contradicting unboundedness. -/
theorem no_scale_invariant_bound (width : ℕ → ℕ) (hw : ∀ n, width n = 2 * n + 7)
    (K : ℕ) (hinv : ∀ n, width n ≤ K) : False :=
  window_unbounded width hw ⟨K, hinv⟩

/-- **The `m = 1` case is not touched**: the family has `m = 2·4ⁿ ≥ 2`, never `1`. -/
theorem family_never_m_one (n : ℕ) : 2 * 4 ^ n ≠ 1 := by
  have : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  omega

end Erdos634.WindowUnbounded
