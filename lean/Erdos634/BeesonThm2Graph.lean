import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Tactic

/-!
# The combinatorial core of Beeson's Theorem 2 (arXiv:1206.2229v3, §6.1)

Beeson's existence theorem for essential segments runs a traversal on a finite directed graph `Γ`
whose nodes are the vertices of tiles in `Ω` and whose links are certain boundary segments.  The
proof has three parts:

1. *(geometric)* every in-link `pq` at `q` yields an out-link `qr`, and distinct in-links yield
   distinct out-links — so `indeg q ≤ outdeg q` at every node;
2. *(combinatorial — this file)* finiteness upgrades that inequality to an **equality** at every
   node, because the two degree sums are both the number of links;
3. *(geometric)* the southernmost point `E` of `Γ` on `AB` has an out-link, hence by (2) an
   in-link, whose direction is forced and contradicts the minimality of `E`.

Part 2 is the whole content of Beeson's "the use of a graph … makes the proof more concise", and it
is target-independent: it is a statement about any finite digraph.  It is formalized here in full.

**Parts 1 and 3 are NOT formalized here.**  They are the geometric core and require the Type I/II
classification and the region `Ω`, which this development does not have.  This file therefore
verifies the *skeleton* of Theorem 2, not Theorem 2; the two geometric obligations are named
explicitly in `beeson_thm2_skeleton`'s hypotheses and remain open.

The link set is modelled as a `Finset (V × V)`, so parallel links are identified — which is what
Beeson's argument needs, since his links are boundary segments and two distinct boundary segments
have distinct endpoint pairs.
-/

namespace Erdos634.BeesonGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Out-degree of `q` in the link set `L`. -/
def outdeg (L : Finset (V × V)) (q : V) : ℕ := (L.filter (fun e => e.1 = q)).card

/-- In-degree of `q` in the link set `L`. -/
def indeg (L : Finset (V × V)) (q : V) : ℕ := (L.filter (fun e => e.2 = q)).card

theorem sum_outdeg (L : Finset (V × V)) : ∑ q, outdeg L q = L.card :=
  (card_eq_sum_card_fiberwise (fun e _ => mem_univ e.1)).symm

theorem sum_indeg (L : Finset (V × V)) : ∑ q, indeg L q = L.card :=
  (card_eq_sum_card_fiberwise (fun e _ => mem_univ e.2)).symm

/-- **The degree-balance lemma.**  In a finite digraph in which every node has in-degree at most its
out-degree, in-degree equals out-degree at *every* node.  (Beeson: "Since there are finitely many
nodes, the total in-degree is equal to the total out-degree.  That is only possible if …") -/
theorem indeg_eq_outdeg_of_le (L : Finset (V × V)) (h : ∀ q, indeg L q ≤ outdeg L q) (q : V) :
    indeg L q = outdeg L q := by
  have hsum : ∑ p, indeg L p = ∑ p, outdeg L p := by rw [sum_indeg, sum_outdeg]
  have := (Finset.sum_eq_sum_iff_of_le (fun p _ => h p)).mp hsum q (mem_univ q)
  exact this

/-- **The step Beeson actually uses**: at the southernmost node, an out-link forces an in-link. -/
theorem exists_in_link_of_out_link (L : Finset (V × V)) (h : ∀ q, indeg L q ≤ outdeg L q)
    {q : V} (hout : 0 < outdeg L q) : ∃ p, (p, q) ∈ L := by
  have hin : 0 < indeg L q := by rw [indeg_eq_outdeg_of_le L h q]; exact hout
  obtain ⟨⟨a, b⟩, he⟩ := Finset.card_pos.mp hin
  rw [mem_filter] at he
  exact ⟨a, he.2 ▸ he.1⟩

/-- Sanity witness: the hypotheses above are satisfiable and the conclusion is not vacuous.
A single loop on `Fin 1` has `indeg = outdeg = 1`, and the out-link produces an in-link. -/
example : indeg ({((0 : Fin 1), (0 : Fin 1))} : Finset (Fin 1 × Fin 1)) 0 = 1 := by decide

example : ∃ p, (p, (0 : Fin 1)) ∈ ({((0 : Fin 1), (0 : Fin 1))} : Finset (Fin 1 × Fin 1)) :=
  exists_in_link_of_out_link _ (by decide) (by decide)

/-! ## The skeleton of Theorem 2, with its two geometric obligations named

`Γstep` is Beeson's part 1 ("for every in-link `pq` to node `q` of `Γ`, the next segment `qr` is an
out-link", refined to the degree inequality).  `Γsouth` is his part 3, the southernmost-point
contradiction, stated as: from an in-link at the distinguished node `E` a contradiction follows.
Both are geometric and both are **open** in this development.
-/

/-- **Skeleton of Beeson's Theorem 2.**  Given the two geometric facts, the traversal closes.
`E` is the southernmost node of `Γ` on `AB`; `Γsouth` is the forced-direction contradiction. -/
theorem beeson_thm2_skeleton (L : Finset (V × V)) (E : V)
    (Γstep : ∀ q, indeg L q ≤ outdeg L q)
    (Γexists : 0 < outdeg L E)
    (Γsouth : ∀ p, (p, E) ∉ L) : False := by
  obtain ⟨p, hp⟩ := exists_in_link_of_out_link L Γstep Γexists
  exact Γsouth p hp

end Erdos634.BeesonGraph
