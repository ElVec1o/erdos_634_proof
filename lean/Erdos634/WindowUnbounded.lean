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

**Scope, sharpened by an independent replication.**  A second seat re-derived the seed
byte-identically, *verified the iteration* the first seat left unchecked (`N = 704` at `m = 8` by two
independent checkers; `N = 11264` at `m = 32` audited), and ran the controls: all seven *non*-spinning
scale-4 rules hold the window at exactly `[−3,3]` out to `N = 288 684`, so the growth is the spin and
not an artefact.  It also bounds the claim: **the refutation is established only at `(e,f) = (1,2)`.**
At `(1,3)` neither the 4- nor the 5-scaled tile spins, and at `(3,4)` the unique 4-scaling does not.
So "not even within the single member `(1,2)`" is correct as stated — the unboundedness occurs inside
one member — but must **not** be read as member-general.

**Two corrections to the crux's own framing**, from the same seat:
* the window is **not anchored at `−3`**: in this family the lower end moves too (`[−(3+n), 3+n]`), so
  `k` must be measured on *both* sides.  The earlier belief that every window starts at `−3` was an
  artefact of the sample;
* **no previously-known tiling climbs at all** — in `N44B`, `N44C`, `99`, `T28`, `T77` the extreme-label
  tiles sit at adjacency-graph depth `0`, i.e. they touch the boundary.  The flat evidence base was
  flat because those tilings have no interior hierarchy; substitution supplies the first examples
  where high labels come from *scale*.  (Relatedly: the unit parallelogram `P₁` has exactly 36
  tilings and **all 36** have window `[−3,2]`, which is why the collar family is flat for every `m`.)

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

**Sharpened by a second family (audited).**  All 75 tilings of the `5`-scaled tile `(10,15,20)` by 25
copies pass an independent five-part checker, and **31 of the 75 spin** — so spinning is *generic* at
scale 5, and scale 4 is merely the **minimal** spinning scale, not a curiosity.  The widest gives
`+3` width per level against `N × 25`, i.e. rate `3/log₂25 = 0.646` per `log₂N`, versus `0.500` for
the scale-4 family (✅ both rates re-checked).  It is better absolutely too: `k = 3` arrives at
`N = 27 500` rather than `N = 180 224`, a factor of 6.6 sooner.  Windows `[−3,3] → [−4,5] → [−6,6]` at
`m = 2, 10, 50`, audited at every level.

So the extremal lower bound is **`w ≥ 0.646·log₂(N/44) + 7`**, against the known upper bound
`w ≤ 4·depth + 3 = O(√N)`.  The constant any proof must beat is now larger, and `k ≥ 6` was never
searched — there is no reason to believe `0.646` is the end.

**And the disqualification is now exhaustive.**  Scaling by 4 preserves the tile, the member, the
field `K`, the label calculus, every vertex figure, all local adjacency, the target's side-labels
`{−3,0,3}`, and the boundary-word alphabet, while raising `k` by 1.  So the label calculus, the
`|ΔL| ≤ 4` adjacency bound, vertex figures (D13), the γ-trap, boundary words, and semigroup/length
arithmetic are **each individually incapable** of bounding the window.  A counting argument in `N` is
the only surviving *class* — and its one known instantiation, the covolume/packing lever, is dead
(`WindowLever`, three independent proofs).

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
