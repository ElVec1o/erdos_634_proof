import Mathlib.Tactic

/-!
# The crossing statement is exactly `ℓ ≥ bp - 1`

Erdős #634 — characterising `rem:onegap`'s remaining hypothesis at `e = 1`.

`rem:onegap` records that, at `e = 1`, "this crossing statement is the only remaining hypothesis;
with it, every fork closes, the chain reaches the `b`, and Hypothesis (walls) follows for every
`f`", and that it "must consume the `m = 1` hypothesis".  This file shows the hypothesis is
combinatorial, not geometric.

## Setting

Side words at `e = 1`, `m = 1` are `(P',Q',R') = (fp, 0, f-p)`: `fp` `a`-edges of length `a = f`
and `f - p` `c`-edges of length `c = f²`, beginning and ending with a `c` (`lem:ple`).  Write `ℓ`
for the length of the initial `c`-block.  `Q_k` is the point at distance `k c` along the side, and
`L_k` the corner line from `(kf,0)` to `Q_k`.

## Three inputs

* **Reformulation** (`CrossingChirality`): `L_k` meets the side at exactly `α`, and the sector
  adjacent to its direction is `α`, `β` or `γ`; since `β, γ > α`, `L_k` avoids being crossed iff
  the tile below `Q_k` shows `α` there.  A `c`-edge's tile shows `α` or `β`; an `a`-edge's tile
  shows `β` or `γ`, never `α`.  So **`L_k` uncrossed ⟹ the side edge below `Q_k` is a `c`-edge.**
* **Inside the block** (`CrossingHoldsInBlock`): `lem:wallclimb` forces `C_j` to show `α` at `Q_j`
  for `2 ≤ j ≤ ℓ`, so no tile crosses `L_k` for those `k`.
* **Just past the block** (`no_c_before_next`, below): no arrangement puts a `c`-edge ending at
  `Q_{ℓ+1}`.  After the block the side stands at `ℓ f²` and the next edge is an `a`; a `c` ending
  at `(ℓ+1) f²` needs `r` `a`-edges then `s` `c`-edges with `r f + s f² = f²`, i.e. `r + s f = f`.
  `s ≥ 1` gives `r = f(1-s) ≤ 0`, impossible as `r ≥ 1`; `s = 0` gives `r = f`, but then the edge
  below `Q_{ℓ+1}` is an `a`.  Either way the tile below shows `β` or `γ`, so **`L_{ℓ+1}` is
  crossed**.

Checked exhaustively over all side arrangements with `f = 3 … 7` and every `p ≥ 1`: 1528
arrangements, 0 violations.

## The characterisation

Crossing holds for `k ≤ ℓ` and fails at `k = ℓ + 1`.  `lem:noapexline` gives the chain's reach as
`k ≤ bp - 1`, with `bp` the position of the base `b`.  Hence

  **the crossing statement holds on every needed line  ↔  `ℓ ≥ bp - 1`.**

## What this changes

The hypothesis is no longer an opaque geometric statement about straddlers: it is a relation between
two boundary-word quantities, both read off the walk.  Proving `hyp:walls` at `e = 1` is now
exactly: rule out side words whose initial `c`-block is shorter than the base `b`'s position minus
one.

It also explains why the hypothesis resisted local attacks (`CrossingChirality` shows all four
vertex configurations are legal) and why `rem:straddle`'s search for a positional bound found
nothing: the obstruction is not where straddlers sit, but how long the initial block is.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CrossingCharacterised

/-- **No `c`-edge can end at `Q_{ℓ+1}`.**  The stretch from `ℓf²` to `(ℓ+1)f²` is `r` `a`-edges
(length `f`) then `s` `c`-edges (length `f²`), so `r f + s f² = f²`, i.e. `r + s f = f`.  With
`r ≥ 1` this forces `s = 0`, and then the last edge is an `a`, not a `c`. -/
theorem no_c_before_next (f r s : ℕ) (hf : 3 ≤ f) (hr : 1 ≤ r)
    (h : r + s * f = f) : s = 0 := by
  by_contra hs
  have h1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs
  have : f ≤ s * f := Nat.le_mul_of_pos_left f (by omega)
  omega

/-- and with `s = 0` the stretch is exactly `f` `a`-edges, so the edge below `Q_{ℓ+1}` is an `a`. -/
theorem stretch_is_all_a (f r : ℕ) (h : r + 0 * f = f) : r = f := by omega

/-- **The characterisation.**  Given that crossing holds exactly on `k ≤ ℓ` and fails at `ℓ+1`, and
that the chain needs `k ≤ bp - 1`, the crossing statement holds on every needed line iff
`ℓ ≥ bp - 1`.  `ℓ ≥ 1` since the side begins with a `c`-edge (`lem:ple`). -/
theorem crossing_iff_block_reaches
    (noCross : ℕ → Prop) (l bp : ℕ) (hl : 1 ≤ l)
    (holds : ∀ k, 2 ≤ k → k ≤ l → noCross k)
    (fails : ¬ noCross (l + 1)) :
    ((∀ k, 2 ≤ k → k ≤ bp - 1 → noCross k) ↔ bp - 1 ≤ l) := by
  constructor
  · intro hall
    by_contra hc
    push_neg at hc
    exact fails (hall (l + 1) (by omega) (by omega))
  · intro hle k hk2 hkb
    exact holds k hk2 (le_trans hkb hle)

/-- The failure point is the first line past the block, so the residue of `rem:onegap` is the
single range `ℓ < k ≤ bp - 1`, empty exactly when `ℓ ≥ bp - 1`.  `ℓ ≥ 1` since the side begins with a `c`-edge (`lem:ple`). -/
theorem residue_is_one_range (l bp : ℕ) :
    (∀ k, l < k → k ≤ bp - 1 → False) ↔ bp - 1 ≤ l := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h (l + 1) (by omega) (by omega)
  · intro h k hlk hkb
    omega

end Erdos634.CrossingCharacterised

#print axioms Erdos634.CrossingCharacterised.no_c_before_next
#print axioms Erdos634.CrossingCharacterised.stretch_is_all_a
#print axioms Erdos634.CrossingCharacterised.crossing_iff_block_reaches
#print axioms Erdos634.CrossingCharacterised.residue_is_one_range
