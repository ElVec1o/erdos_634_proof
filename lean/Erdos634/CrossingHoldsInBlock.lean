import Mathlib.Tactic

/-!
# The crossing statement holds inside the initial `c`-block

Erdős #634 — narrowing `rem:onegap`'s remaining hypothesis at `e = 1`.

## The two inputs

**(1) Reformulation** (`CrossingChirality`, proved here).  `L_k` meets the equal side at exactly `α`
(`ApexRay`), and the sector of the straight angle at `Q_k = k c u` adjacent to `L_k`'s direction is
`α`, `β` or `γ`.  Since `β > α` and `γ = 2α + β > α`, the line coincides with a tile boundary iff
that sector is an `α`, i.e. iff the side tile `T_k` spanning `[Q_{k-1}, Q_k]` shows `α` at `Q_k`:

  no tile crosses `L_k`  ↔  `T_k` shows `α` at its upper end.

**(2) The wall climb** (`lem:wallclimb`, companion, unconditional).  For a side whose initial
`c`-block has length `ℓ ≥ 2`, and every `2 ≤ j ≤ ℓ`, the block tile `C_j` is direct and its mate is
forced; at the side junction `j c u`, `C_j`'s `α` together with `M_j`'s `γ` force the next side
tile's corner to `β`.  In particular **`C_j` shows `α` at `Q_j`** for every `j` in that range.  The
lemma is proved by induction on `j` and uses no base-letter hypothesis and no line closure.

## The corollary

`C_j` is `T_j`, and "shows `α` at `Q_j`" is exactly the reformulation's case (A).  Hence

  **no tile crosses `L_k` for any `k` with `2 ≤ k ≤ ℓ`.**

The crossing statement is therefore *not* an independent hypothesis on those lines: it is already a
theorem there.  What `rem:onegap` leaves open is only the lines **beyond** the initial `c`-block,
`k > ℓ`.

## Scope, stated exactly

This narrows the hypothesis; it does not discharge it.  `lem:noapexline` says the chain needs the
lines `L_k` with `k ≤ bp - 1`, where `bp` is the position of the base `b`.  So the chain closes
whenever `ℓ ≥ bp - 1`, and the open case is precisely

  `ℓ < bp - 1`   (initial `c`-block shorter than the chain's reach).

At `ℓ = f` — a side of `f` `c`-edges — the block covers every line, but `ℓ = f` is `p = 0`, which is
Hypothesis (walls) itself; that route is circular and is recorded as such, not used.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CrossingHoldsInBlock

/-- `noCross k` : no tile crosses `L_k`.  `alphaUp k` : the side tile `T_k` shows `α` at `Q_k`.
`inBlock ℓ k` : `2 ≤ k ≤ ℓ`. -/
def inBlock (l k : ℕ) : Prop := 2 ≤ k ∧ k ≤ l

/-- **The corollary.**  Given the reformulation (`equiv`) and the wall climb (`climb`), the crossing
statement holds on every line inside the initial `c`-block. -/
theorem crossing_holds_in_block
    (noCross alphaUp : ℕ → Prop) (l : ℕ)
    (equiv : ∀ k, noCross k ↔ alphaUp k)
    (climb : ∀ j, inBlock l j → alphaUp j) :
    ∀ k, inBlock l k → noCross k :=
  fun k hk => (equiv k).mpr (climb k hk)

/-- **What remains open.**  The chain needs `L_k` for `k ≤ bp - 1`; the block supplies `k ≤ ℓ`.  So
the residue is exactly the range `ℓ < k ≤ bp - 1`, which is empty when `ℓ ≥ bp - 1`. -/
theorem residue_empty (l bp : ℕ) (h : bp - 1 ≤ l) :
    ∀ k, 2 ≤ k → k ≤ bp - 1 → inBlock l k :=
  fun k hk2 hkb => ⟨hk2, le_trans hkb h⟩

/-- and when the block is short the residue is a genuine range. -/
theorem residue_nonempty (l bp : ℕ) (h : l + 1 ≤ bp - 1) (hl : 2 ≤ l + 1) :
    ¬ inBlock l (l + 1) ∧ (l + 1 ≤ bp - 1) := by
  refine ⟨?_, h⟩
  intro hc
  exact absurd hc.2 (by omega)

/-- The circular route, recorded so it is not walked: `ℓ = f` covers every line, but a side of `f`
`c`-edges is `p = 0`, which is Hypothesis (walls) itself. -/
theorem block_full_is_circular (f l p : ℕ) (hblock : l = f) (hp : p = f - l) : p = 0 := by
  omega

end Erdos634.CrossingHoldsInBlock

#print axioms Erdos634.CrossingHoldsInBlock.crossing_holds_in_block
#print axioms Erdos634.CrossingHoldsInBlock.residue_empty
#print axioms Erdos634.CrossingHoldsInBlock.residue_nonempty
#print axioms Erdos634.CrossingHoldsInBlock.block_full_is_circular
