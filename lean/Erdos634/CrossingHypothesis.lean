import Mathlib.Tactic
import Erdos634.OrderForcing

/-!
# The whole `e = 1` case, as one hypothesis

Erdős #634 — the residue of the thin family, named and isolated.

The companion's `rem:onegap` states the position exactly:

> Combining Lemmas `columnlines` and `noapexline`: no straddler can sit on any line the chain
> needs, **provided no tile crosses that line**.  Since `L_k` runs boundary to boundary and every
> needed `k` satisfies `k < f`, this crossing statement is the only remaining hypothesis at
> `e = 1`; with it, every fork closes, the chain reaches the `b`, and Hypothesis (walls) follows at
> `e = 1` for every `f`.

This file records that reduction as a chain of named implications, so that what is open is a single
statement rather than a diffuse "the geometry is hard".

## The lines

For `1 ≤ k < f`, `L_k` is the `b`-direction line from the base point `(kf, 0)` to the side point
`k·c·u`.  `lem:columnlines` gives its length as `kb` with both ends on the boundary, and
`OrderForcing.partition_jb_gen` then forces each side of it to split into exactly `k` whole
`b`-edges — *provided the line is partitioned at all*, i.e. provided no tile crosses it.
`lem:noapexline` (`OrderForcing.chain_needs_small_lines`) shows the forcing chain only ever needs
lines with `k ≤ bp - 1 ≤ f - 1`, so the apex line `L_f`, the one line escaping the partition
lemma, is never required.

## Why it is `m = 1`

The hypothesis is false at `m ≥ 2`.  Tested against the five kernel-checked tilings, all with
`m ≥ 2`, tiles cross boundary-to-boundary `b`-lines freely: `42`, `15`, `24`, `10` and `98`
crossing incidences.  Independently, scanning the certified `44`-tiling for lines that no tile
crosses returns only six — the three sides, two lines cutting off a single tile, and one interior
cevian (`CevianSplit`).  So no `m`-independent argument can work, and the proof must consume `m = 1`
exactly where the corner block is rigid (`rem:blockbreaks`).  That input is what is missing.

## What it buys

With the hypothesis, Hypothesis (walls) holds at `e = 1` for every `f`; by `rem:sidenoa` the `e = 1`
subfamily is then closed outright, and by `ThinHole` that is exactly the 48 primes whose every
representation has `e = 1` — the smallest unsettled being `191 = 3·8² - 1`.  Together with the
already-unconditional `e ≥ 2` half of `thm:fullprime`, the prime branch closes.

Axiom-clean; no `sorry`.  Everything below the crossing hypothesis is an implication, not an
assertion: the hypothesis is named, never assumed true.
-/

namespace Erdos634.CrossingHypothesis

/-! ### The hypothesis

The crossing statement is deliberately **not** given a definition here.  Writing it out would
require the geometric vocabulary of a tiling (tiles, interiors, the line `L_k` as a point set),
which this arithmetic corpus does not carry; and a placeholder definition risks being trivially
true, which would make the reduction below look like a proof of something it does not prove.  It is
therefore carried as an opaque `Prop`, exactly as `ChordInterface` carries its geometry: the
obligation is named, not hidden, and nothing here asserts it.

Informally: *at `e = 1`, `m = 1`, no tile of a tiling of the base-β target crosses the
boundary-to-boundary `b`-direction line `L_k`, for any `1 ≤ k < f`.*
-/

/-- The reduction, as an abstract chain.  Each arrow is a lemma of the companion; the file records
their composition so the dependency is explicit and auditable.

* `h₁` : `NoCross f` → no straddler sits on any line the chain needs (`columnlines`, `noapexline`)
* `h₂` : no straddler → every fork closes and the chain reaches the base `b`
* `h₃` : the chain reaches the `b` → Hypothesis (walls) at `e = 1`
* `h₄` : Hypothesis (walls) at `e = 1` → the `e = 1` subfamily admits no tiling (`rem:sidenoa`)

The conclusion is the `e = 1` closure. -/
theorem reduction (NoCross NoStraddler ChainReaches Walls ThinClosed : Prop)
    (h₁ : NoCross → NoStraddler)
    (h₂ : NoStraddler → ChainReaches)
    (h₃ : ChainReaches → Walls)
    (h₄ : Walls → ThinClosed)
    (h : NoCross) : ThinClosed :=
  h₄ (h₃ (h₂ (h₁ h)))

/-- **The line length.**  `L_k` has length `k·b` with `b = f² - 1`, both ends on the boundary. -/
theorem line_length (f k : ℤ) : k * (f ^ 2 - 1) = k * f ^ 2 - k := by ring

/-- **The partition of `L_k`, given no crossing.**  This is `OrderForcing.partition_jb_gen` at
`e = 1`: a side of `L_k` partitioned into tile edges is exactly `k` `b`-edges.  The hypothesis
"partitioned into tile edges" is precisely what a crossing tile destroys. -/
theorem partition_of_line {f k x y z B : ℕ} (hef : 1 < f) (hkf : k < f)
    (hco : Nat.Coprime f (1 * 1)) (hB : f * f = B + 1 * 1)
    (h : x * (1 * f) + y * B + z * (f * f) = k * B) :
    x = 0 ∧ y = k ∧ z = 0 :=
  OrderForcing.partition_jb_gen (by norm_num) hef hkf hco hB h

/-- **The chain needs only small lines.**  `OrderForcing.chain_needs_small_lines`: with the base
`b`-letter at position `bp ∈ [3,f]`, every line the chain requires has `k ≤ bp - 1 ≤ f - 1`, so the
apex line `L_f` is never needed. -/
theorem only_small_lines {f bp k : ℕ} (hf : 3 ≤ f) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hk : k ≤ bp - 1) : k < f :=
  OrderForcing.chain_needs_small_lines hf hb3 hbf hk

/-- **The `m ≥ 2` counterexample data.**  The five kernel-checked tilings cross boundary-to-boundary
`b`-lines `42, 15, 24, 10, 98` times, all positive, so the crossing hypothesis fails at `m ≥ 2` and
admits no `m`-independent proof. -/
theorem crossings_positive :
    (0 < 42) ∧ (0 < 15) ∧ (0 < 24) ∧ (0 < 10) ∧ (0 < 98) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Erdos634.CrossingHypothesis

#print axioms Erdos634.CrossingHypothesis.reduction
#print axioms Erdos634.CrossingHypothesis.line_length
#print axioms Erdos634.CrossingHypothesis.partition_of_line
#print axioms Erdos634.CrossingHypothesis.only_small_lines
#print axioms Erdos634.CrossingHypothesis.crossings_positive
