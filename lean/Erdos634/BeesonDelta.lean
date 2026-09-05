import Erdos634.BeesonOmega

/-!
# Beeson §8.5: the region `Δ` and the traversal `Γ′` — a *monotone* argument, not a counting one

Erdős #634 (arXiv:1206.2229v3 §8.5, Definitions 14–16, Lemmas 33–35).  The room's structural seat
named this as the one location-sensitive device in the literature not yet tried here — it passes the
project's admission test, which the degree-balance argument of Theorem 2 does not.  This file ports
its core.

**CORRECTION (round 2 of the room, verified — read this before using the file).**  An earlier
version of this header claimed §8.5 "runs on a different engine entirely" from Theorem 2's degree
balance, driven by a strictly monotone functional.  **Both halves of that were wrong.**

* **§8.5's engine is the same count.**  Theorem 6's proof says, verbatim (`b1206.txt:2735`):
  *"As in the proof of Theorem 2, we argue that by Lemma 35, the in-degree of every node `P` in the
  graph `Γ′` is less than or equal to its out-degree; and therefore, since it is a finite graph, the
  in-degree is equal to the out-degree."*  Acyclicity and terminal nodes — the content of
  `delta_traversal_contradiction` below — are never used.  So §8.5 does **not** clear the project's
  admission test the way it was advertised.
* **Beeson's `φ` is not strictly advancing.**  Lemma 34's `φ` is the distance from line `AQ`, and
  `AQ` is itself a Direction-A segment (Lemma 31), so a *Direction-A-west* link is exactly parallel
  to it: `dφ/ds = 0`.  `StrictlyAdvancing` is therefore **not** satisfied by his own functional;
  every other candidate line (`AB`, `BC`, `AC`) is neutral on a different one of the four directions.
* **And §8.5's conclusion is FALSE.**  Beeson's Theorem 6 ("`K ∣ M²`") is refuted by this repository's
  own zero-axiom certificate `CevianTiling63.ceviantiling63_certificate` (`#print axioms`: *no*
  axioms): 63 copies of the tile `(2,3,4)` tile the target `(21,18,24)`, whose angles are exactly
  `(2α, β, α+β)`; `a/c = 2/4 = M/K` with `(M,K) = (3,6)` and `N = 2K² − M² = 63`, yet `6 ∤ 9`.
  Theorem 7 and Corollary 1 fall with it (Beeson's Table 1 omits 63).  Root cause: **Lemma 21**
  asserts "`M²/d` is relatively prime to `K`" for `d = gcd(M²,K)`, false at `(M,K) = (3,6)` where
  `d = 3`, `M²/d = 3`, `gcd(3,6) = 3`.  Its proof is valid exactly when `gcd(M,K) = 1`.

**Our own floor is unaffected**: the base-β family has `(M,K) = (e,f)` with `gcd(e,f) = 1`, and the
corpus proves `f ∣ j` independently (`RunForcing`, `SideNoB`).  Nothing here inherits the error.

**What the file still is.**  The theorems below are correct abstract graph theory — a strictly
advancing functional does give acyclicity and a terminal node — and `InDelta`'s *directedness*
(against `Ω`'s symmetry) is a real and correctly recorded contrast.  What they are not is a
faithful model of Beeson's §8.5 argument.  Kept as a tool, not as a port.

Two further structural contrasts with `Ω`, both formalized below:

* `Ω` (Def. 11) is reached by chains of tiles "each sharing part of an edge with the next" — a
  **symmetric** relation, and `BeesonOmega.inOmega_symm` proves it.  `Δ` (Def. 15) is reached by a
  **southerly path crossing in-sync borders in their legal directions** — a *directed* relation.  So
  `Δ ⊆ Ω` (Beeson's own Remark) but the reachability is **not** symmetric, and this file does not
  prove a symmetry lemma because there is none to prove.
* `Γ′`'s links carry the confinement `p ∈ triangle RAQ` (Def. 16), preserved by Lemma 34.

**Scope.**  This is the traversal engine, general and axiom-clean.  The geometric content —
Definition 14's in-sync borders, Lemma 33's "`Δ` is on the north", and the case analysis of
Lemma 35 — needs the tile-placement layer and is **not** here.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BeesonDelta

open Erdos634.Geometry Erdos634.BeesonOmega

variable {V : Type*}

/-! ## `Δ`: directed reachability, unlike `Ω` -/

/-- **`Δ`-reachability** (Def. 15): the reflexive–transitive closure of a **directed** step relation
(a legal southerly crossing).  Contrast `BeesonOmega.InOmega`, whose step relation is symmetric. -/
def InDelta (step : V → V → Prop) (t₀ v : V) : Prop := Relation.ReflTransGen step t₀ v

theorem inDelta_refl (step : V → V → Prop) (t₀ : V) : InDelta step t₀ t₀ :=
  Relation.ReflTransGen.refl

theorem inDelta_trans {step : V → V → Prop} {t₀ u v : V}
    (h1 : InDelta step t₀ u) (h2 : InDelta step u v) : InDelta step t₀ v :=
  Relation.ReflTransGen.trans h1 h2

/-- **`Δ ⊆ Ω`** (Beeson's Remark after Def. 15): a legal directed step is in particular an
`Ω`-adjacency, so everything `Δ`-reachable is `Ω`-reachable. -/
theorem inDelta_subset_inOmega {N : ℕ} (D : Dissection N) (A B C : Plane)
    (step : Fin N → Fin N → Prop) (hstep : ∀ u v, step u v → OmegaAdj D A B C u v)
    {t₀ v : Fin N} (h : InDelta step t₀ v) : InOmega D A B C t₀ v := by
  induction h with
  | refl => exact inOmega_refl D A B C t₀
  | tail _ hlast ih => exact Relation.ReflTransGen.tail ih (hstep _ _ hlast)

/-! ## The monotone traversal engine (Lemma 34's mechanism) -/

variable (φ : V → ℝ) (link : V → V → Prop)

/-- **Lemma 34, abstracted.**  `φ` strictly increases along every link — Beeson's `φ` is the distance
from the line `AQ`, and every one of `Γ′`'s four directions moves away from it. -/
def StrictlyAdvancing : Prop := ∀ p q, link p q → φ p < φ q

/-- **A strictly advancing digraph has no loops.** -/
theorem no_loop (h : StrictlyAdvancing φ link) (p : V) : ¬ link p p := fun hp =>
  lt_irrefl _ (h p p hp)

/-- **`φ` strictly increases along any nonempty directed path**, so no path returns to its start:
the traversal is acyclic.  This is what the degree-balance argument of Theorem 2 cannot give. -/
theorem advancing_along_path (h : StrictlyAdvancing φ link) {p q : V}
    (hpq : Relation.TransGen link p q) : φ p < φ q := by
  induction hpq with
  | single hstep => exact h _ _ hstep
  | tail _ hlast ih => exact lt_trans ih (h _ _ hlast)

/-- **No cycles.** -/
theorem no_cycle (h : StrictlyAdvancing φ link) (p : V)
    (hcyc : Relation.TransGen link p p) : False :=
  lt_irrefl _ (advancing_along_path φ link h hcyc)

/-! ## The contradiction: a maximum exists, but Lemma 35 forbids a terminal node -/

/-- **The §8.5 traversal closes.**  On a finite nonempty node set, `φ` attains a maximum `m`; if the
traversal is strictly advancing then `m` has no out-link, while Lemma 35 says every node reached by a
link has one.  Given a link into `m`, that is a contradiction.

This is the shape of Beeson's §8.5 argument, with `Lemma35` as the named geometric hypothesis — the
analogue of `BeesonThm2Graph.beeson_thm2_skeleton`, but driven by a monotone functional rather than a
degree count. -/
theorem delta_traversal_contradiction [Fintype V] [DecidableEq V]
    (h : StrictlyAdvancing φ link) (m : V)
    (hmax : ∀ v, φ v ≤ φ m)
    (Lemma35 : ∀ q, (∃ p, link p q) → ∃ r, link q r)
    (hin : ∃ p, link p m) : False := by
  obtain ⟨r, hr⟩ := Lemma35 m hin
  exact absurd (hmax r) (not_le.mpr (h m r hr))

/-- Non-vacuity: `StrictlyAdvancing` is satisfiable and the conclusion is not empty — the strict
order on `Fin 2` advances, and its top node genuinely has no out-link. -/
theorem advancing_witness :
    StrictlyAdvancing (fun i : Fin 2 => (i : ℝ)) (fun p q => (p : ℕ) < (q : ℕ)) := by
  intro p q hpq
  simp only []
  exact_mod_cast hpq

end Erdos634.BeesonDelta
