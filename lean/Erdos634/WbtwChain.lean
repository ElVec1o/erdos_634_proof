import Erdos634.ChordBetweennessDisjointFar

/-!
# Betweenness along an arbitrary-length ordered chain

Erdős #634. The `ChordDecompositionOneStraddlerFinal` / `TwoStraddlersFinal` / `ThreeStraddlersFinal`
files each derive, by hand, facts like `Wbtw ℝ (g i) (g j) (g k)` for indices spread arbitrarily far
apart in an ordered chain of points `p, r₁, s₁, r₂, s₂, r₃, s₃, q`, from only the *consecutive*
betweenness facts (`hchain`) between adjacent triples — repeating the same
`Wbtw.trans_expand_left`/`Wbtw.trans_right` composition by hand at each new distance. This file
extracts that pattern once, for an arbitrary sequence `g : ℕ → Plane`: given only that every
consecutive triple satisfies `Wbtw` and every consecutive pair is distinct, *any* triple of indices
in order satisfies `Wbtw`. This is exactly the missing tool a fully general finite induction over
an arbitrary number of straddlers needs — with it, the chord-decomposition ladder built by hand for
one, two and three straddlers no longer needs a fresh hand-derivation at each length.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A chain of consecutive betweenness facts reaches one step further.** If every consecutive
triple of `g` satisfies `Wbtw` and every consecutive pair is distinct, then `g i, g j, g (j+1)` is a
`Wbtw` triple for every `i < j`. -/
theorem wbtw_chain_step {g : ℕ → Plane}
    (hchain : ∀ n, Wbtw ℝ (g n) (g (n + 1)) (g (n + 2)))
    (hne : ∀ n, g n ≠ g (n + 1)) :
    ∀ i j, i < j → Wbtw ℝ (g i) (g j) (g (j + 1)) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => simpa using hchain i
  | succ j hij ih =>
    have h2 : Wbtw ℝ (g j) (g (j + 1)) (g (j + 2)) := hchain j
    exact ih.trans_expand_right h2 (hne j)

/-- **Betweenness along an arbitrary-length ordered chain.** If every consecutive triple of `g`
satisfies `Wbtw`, every consecutive pair is distinct, and `g` is injective, then `Wbtw ℝ (g i) (g j)
(g k)` holds for every `i ≤ j ≤ k` — the general fact that the one/two/three-straddler
hand-derivations each specialize. -/
theorem wbtw_chain {g : ℕ → Plane}
    (hchain : ∀ n, Wbtw ℝ (g n) (g (n + 1)) (g (n + 2)))
    (hne : ∀ n, g n ≠ g (n + 1)) (hinj : Function.Injective g) :
    ∀ i j k, i ≤ j → j ≤ k → Wbtw ℝ (g i) (g j) (g k) := by
  intro i j k hij hjk
  rcases eq_or_lt_of_le hij with rfl | hij'
  · -- i = j: Wbtw (g i) (g i) (g k) holds trivially via `wbtw_self_left`.
    exact wbtw_self_left ℝ (g i) (g k)
  induction k, hjk using Nat.le_induction with
  | base => exact wbtw_self_right ℝ (g i) (g j)
  | succ k hjk ih =>
    by_cases hjk_eq : j = k
    · subst hjk_eq
      exact wbtw_chain_step hchain hne i j hij'
    · have hjltk : j < k := lt_of_le_of_ne hjk hjk_eq
      have h2 : Wbtw ℝ (g j) (g k) (g (k + 1)) := wbtw_chain_step hchain hne j k hjltk
      have hne' : g j ≠ g k := fun h => hjk_eq (hinj h)
      exact ih.trans_expand_left h2 hne'

/-- **The one-step chain fact, bounded to a finite range.** As `wbtw_chain_step`, but `hchain` and
`hne` need only hold below a bound `K` (what a genuinely finite chain of straddler traces actually
supplies), rather than for every natural number. -/
theorem wbtw_chain_step_bounded {g : ℕ → Plane} (K : ℕ)
    (hchain : ∀ n, n + 2 ≤ K → Wbtw ℝ (g n) (g (n + 1)) (g (n + 2)))
    (hne : ∀ n, n + 1 ≤ K → g n ≠ g (n + 1)) :
    ∀ i j, i < j → j + 1 ≤ K → Wbtw ℝ (g i) (g j) (g (j + 1)) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro hjK; simpa using hchain i (by omega)
  | succ j hij ih =>
    intro hjK
    have h2 := hchain j (by omega)
    exact (ih (by omega)).trans_expand_right h2 (hne j (by omega))

/-- **Betweenness along a finite ordered chain.** As `wbtw_chain`, but `hchain`, `hne` and
injectivity need only hold within a finite range `≤ K` — exactly what a genuinely finite sequence
of straddler trace endpoints supplies (an infinite injective extension is otherwise needed for
nothing). Given every consecutive triple of `g` below `K` satisfies `Wbtw`, every consecutive pair
below `K` is distinct, and `g` is injective on `{0, ..., K}`, `Wbtw ℝ (g i) (g j) (g k)` holds for
every `i ≤ j ≤ k ≤ K`. -/
theorem wbtw_chain_bounded {g : ℕ → Plane} (K : ℕ)
    (hchain : ∀ n, n + 2 ≤ K → Wbtw ℝ (g n) (g (n + 1)) (g (n + 2)))
    (hne : ∀ n, n + 1 ≤ K → g n ≠ g (n + 1))
    (hinj : ∀ a b, a ≤ K → b ≤ K → a ≠ b → g a ≠ g b) :
    ∀ i j k, i ≤ j → j ≤ k → k ≤ K → Wbtw ℝ (g i) (g j) (g k) := by
  intro i j k hij hjk
  rcases eq_or_lt_of_le hij with rfl | hij'
  · intro _; exact wbtw_self_left ℝ (g i) (g k)
  induction k, hjk using Nat.le_induction with
  | base => intro _; exact wbtw_self_right ℝ (g i) (g j)
  | succ k hjk ih =>
    intro hkK
    by_cases hjk_eq : j = k
    · subst hjk_eq
      exact wbtw_chain_step_bounded K hchain hne i j hij' (by omega)
    · have hjltk : j < k := lt_of_le_of_ne hjk hjk_eq
      have h2 := wbtw_chain_step_bounded K hchain hne j k hjltk (by omega)
      have hne' : g j ≠ g k := hinj j k (by omega) (by omega) hjk_eq
      exact (ih (by omega)).trans_expand_left h2 hne'

end Erdos634.ChordTraceReal
