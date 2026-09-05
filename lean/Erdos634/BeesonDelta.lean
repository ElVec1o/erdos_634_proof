import Erdos634.BeesonOmega

/-!
# Beeson §8.5: the region `Δ` and the traversal `Γ′` — a *monotone* argument, not a counting one

Erdős #634 (arXiv:1206.2229v3 §8.5, Definitions 14–16, Lemmas 33–35).  The room's structural seat
named this as the one location-sensitive device in the literature not yet tried here — it passes the
project's admission test, which the degree-balance argument of Theorem 2 does not.  This file ports
its core.

**Why it is a different animal from Theorem 2.**  `BeesonThm2Graph` formalized Theorem 2's engine:
in a finite digraph where every node has `indeg ≤ outdeg`, finiteness forces equality everywhere.
That is a *counting* argument — bounded, hence by the project's bounded-or-locational dilemma it can
only ever produce a census.  §8.5 runs on a different engine entirely:

> **Lemma 34.** *"All the links in `Γ′` are in one of the four directions `A` or `C` west, `AB` or
> `BC` north.  Each of those directions **moves away from the line `AQ`**.  Hence `R` is farther from
> `AQ` than `P` is."*

That is a **strictly monotone functional along links** — a locational quantity, not a count.  Its
consequence is not degree balance but **acyclicity and the existence of a terminal node**, which is
what contradicts Lemma 35 ("the next boundary segment `qr` is also a link").

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
