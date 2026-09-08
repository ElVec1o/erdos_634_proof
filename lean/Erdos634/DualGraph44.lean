import Mathlib.Data.List.Defs
import Erdos634.Tiling44

/-!
# `rem:spectral` — the dual graph of the certified 44-tiling (outcome-1/nogo debt)

Erdős #634, `paper/erdos-634-obstructions.tex:1746`. The remark states four numeric facts about the
dual graph of the certified 44-tiling (`Tiling44.tiles`): 44 vertices, 45 shared full edges, degree
distribution `{1¹¹, 2²⁰, 3¹³}`, and four connected components of orders `4, 8, 16, 16`. This file
computes the first three by `decide` directly against `Tiling44.tiles`' exact `ℤ[√15]` coordinates
— no new geometric machinery, and no `Classical.choice`: everything here is the same computable
substrate `Tiling44.lean` itself already certifies `(C1)`–`(C4)` on.

## Scope, stated exactly

**Formalized here**: two tiles "share a full edge" when some edge of one exactly equals some edge
of the other as an unordered point pair — decided directly on `Tiling44`'s coordinates, the same
reading `code/dualgraph44_count.py` already used. From this: the total number of shared edges (`45`,
matches the paper) and the degree of every tile.

**The degree distribution does NOT match the paper.** `rem:spectral` claims `{1¹¹,2²⁰,3¹³}`.
`code/dualgraph44_count.py` found `{1:12,2:18,3:14}` and flagged it as an open TENSION
(`lean/PAPER_MAP.md`, 2026-09-04) — one Python script against the paper's hand computation, neither
side settled. **This file settles it**: `degree_distribution` proves `{1:12,2:18,3:14}` by kernel
`decide` directly against `Tiling44.tiles`' certified coordinates, and `paper_distribution_wrong`
proves the paper's own claimed counts do not hold of this object. The Python finding was correct.

**NOT formalized here: the connected-component count** (`4, 8, 16, 16`, also disputed — the same
tension row found `5` components of sizes `2,4,8,14,16`). Computing connectivity correctly needs a
graph-reachability closure, a real further step; this file supplies the adjacency data it would
consume, but does not build it. **Label stays PROVED**: this closes (and corrects) the
degree-distribution half of the remark's worked example, not the component half, and not the
remark's separate, already-general, decisive claim — untouched by any of this — that no spectral
criterion excludes a prime order.
-/

namespace Erdos634.DualGraph44

open Tiling44

/-- Two edges (each an unordered pair of points) are the same edge. -/
def edgeEq (e1 e2 : Pt × Pt) : Bool :=
  (e1.1 == e2.1 && e1.2 == e2.2) || (e1.1 == e2.2 && e1.2 == e2.1)

/-- Tiles `i` and `j` (by index into `Tiling44.tiles`) share a full edge: some edge of one equals
some edge of the other exactly. -/
theorem tiles_length : tiles.length = 44 := by decide

/-- A harmless default triangle; `getD`'s fallback never actually fires since every `i : Fin 44`
satisfies `i.1 < 44 = tiles.length` (`tiles_length`), so this choice is immaterial. -/
def dummyTri : Tri := ((0,0,0,0), (1,0,0,0), (0,1,0,0))

def sharesEdge (i j : Fin 44) : Bool :=
  let ti := tiles.getD i.1 dummyTri
  let tj := tiles.getD j.1 dummyTri
  (List.range 3).any fun e1 => (List.range 3).any fun e2 => edgeEq (edgeOf ti e1) (edgeOf tj e2)

/-- The degree of tile `i`: how many other tiles it shares a full edge with. -/
def degree (i : Fin 44) : Nat :=
  ((List.finRange 44).filter fun j => j ≠ i && sharesEdge i j).length

/-- The total number of shared edges, counted once each (sum of degrees, halved). -/
def totalSharedEdges : Nat :=
  (((List.finRange 44).map degree).sum) / 2

/-- **The edge count.** The certified 44-tiling has exactly 45 shared full edges. -/
theorem totalSharedEdges_eq_45 : totalSharedEdges = 45 := by decide

/-- **The degree distribution — kernel-verified, and it corrects the paper's own worked example,
not this file.** `rem:spectral` states `{1¹¹,2²⁰,3¹³}`. `code/dualgraph44_count.py` already found
`{1:12,2:18,3:14}` under the same "shares a full edge" reading (`private/RESEARCH_LOG.md`,
`lean/PAPER_MAP.md`'s TENSION row, 2026-09-04), leaving it an open, unresolved discrepancy between
one Python script and the paper's hand computation. **This theorem settles which side that
discrepancy is on**: `{1:12,2:18,3:14}` is what the Lean kernel proves, directly from
`Tiling44.tiles`' certified coordinates — the same object `(C1)`–`(C4)` already certify. `11+20+13`
and `12+18+14` both total `44`, so the *counts* alone couldn't distinguish the two; this is checked
against the real coordinate data, not against either total. -/
theorem degree_distribution :
    ((List.finRange 44).filter fun i => degree i == 1).length = 12 ∧
    ((List.finRange 44).filter fun i => degree i == 2).length = 18 ∧
    ((List.finRange 44).filter fun i => degree i == 3).length = 14 ∧
    (List.finRange 44).all (fun i => degree i == 1 || degree i == 2 || degree i == 3) := by
  decide

/-- The paper's own claimed distribution does **not** match — recorded as a theorem, not a
comment, so this file cannot silently drift from the tension it documents. -/
theorem paper_distribution_wrong :
    ¬ (((List.finRange 44).filter fun i => degree i == 1).length = 11 ∧
       ((List.finRange 44).filter fun i => degree i == 2).length = 20 ∧
       ((List.finRange 44).filter fun i => degree i == 3).length = 13) := by
  decide

/-- Non-vacuity / sanity: `sharesEdge` is symmetric (an unordered relation, as it should be for a
graph), checked directly rather than assumed. -/
theorem sharesEdge_symm (i j : Fin 44) : sharesEdge i j = sharesEdge j i := by
  revert i j; decide

/-! ## Connected components

`rem:spectral` also claims four components of sizes `4, 8, 16, 16`. `code/dualgraph44_count.py`
computed `5` components of sizes `2, 4, 8, 14, 16` and flagged this as a second, separate
discrepancy from the same 2026-09-04 TENSION row — unresolved until now. This settles it the same
way as the degree distribution: by a decidable BFS-reachability closure over `sharesEdge`, kernel
`decide`d directly against `Tiling44.tiles`. -/

/-- One step of BFS closure: add every neighbor (under `sharesEdge`) of everything already in `s`. -/
def stepClosure (s : List (Fin 44)) : List (Fin 44) :=
  (s ++ s.flatMap fun i => (List.finRange 44).filter (sharesEdge i)).dedup

/-- Insertion into a `Fin 44`-list sorted by underlying value — used only to normalize a
component's vertex list to a canonical order, so that two BFS traversals reaching the same vertex
set (in different orders) produce syntactically equal lists for `List.dedup` to merge. -/
def insertFin (x : Fin 44) : List (Fin 44) → List (Fin 44)
  | [] => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertFin x ys

def isortFin : List (Fin 44) → List (Fin 44)
  | [] => []
  | x :: xs => insertFin x (isortFin xs)

/-- The connected component containing `i`, as a canonically-sorted vertex list. Iterating
`stepClosure` 44 times from `[i]` always suffices: the graph has 44 vertices, so a BFS frontier
that keeps growing must stabilize within 44 steps. -/
def componentOf (i : Fin 44) : List (Fin 44) :=
  isortFin (((List.range 44).foldl (fun s _ => stepClosure s) [i]).dedup)

def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

def isortNat : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (isortNat xs)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- **The component count and sizes — kernel-verified, and it corrects the paper's own worked
example a second time.** `rem:spectral` claims `4` components of sizes `4, 8, 16, 16`.
`code/dualgraph44_count.py` found `5` components of sizes `2, 4, 8, 14, 16` (2026-09-04 TENSION
row), left unresolved against the paper's hand computation. This theorem settles it: `[2,4,8,14,16]`
is what the kernel proves from `Tiling44.tiles`' certified coordinates via `componentOf`'s BFS
closure — `List.dedup` on the (canonically-sorted) component lists correctly merges components
reached by different starting vertices, since sorting first makes set-equal components
list-equal. -/
theorem component_sizes :
    isortNat ((List.finRange 44).map componentOf |>.dedup |>.map (fun l => l.length))
      = [2, 4, 8, 14, 16] := by
  decide

/-- The paper's own claimed component count/sizes does **not** match. -/
theorem paper_component_sizes_wrong :
    isortNat ((List.finRange 44).map componentOf |>.dedup |>.map (fun l => l.length))
      ≠ [4, 8, 16, 16] := by
  rw [component_sizes]; decide

end Erdos634.DualGraph44

#print axioms Erdos634.DualGraph44.component_sizes
#print axioms Erdos634.DualGraph44.paper_component_sizes_wrong

#print axioms Erdos634.DualGraph44.totalSharedEdges_eq_45
#print axioms Erdos634.DualGraph44.degree_distribution
#print axioms Erdos634.DualGraph44.sharesEdge_symm
#print axioms Erdos634.DualGraph44.paper_distribution_wrong
