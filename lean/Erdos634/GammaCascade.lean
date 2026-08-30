import Mathlib

/-!
# The γ-cascade: a side with no `c`-edge is impossible

Erdős #634, `prop:gammatrap`.  Excluding `n_c = 0` — the last input to the base word, and so to
everything bridge (c) carries — rests on a pigeonhole along the side, and that is what is proved
here.

Suppose a side is partitioned by edges `E_1, …, E_n` with junctions `J_0, …, J_n`, and every edge is
an `a`- or a `b`-edge.  Each such edge is incident to `γ` at exactly one of its two endpoints, so
each `E_i` places a `γ` at `J_{i-1}` or at `J_i`.  A junction interior to a side is a `π`-vertex and
carries at most one `γ`, and the corners `J_0`, `J_n` carry none.  Then `E_1` must place at `J_1`,
which fills it, so `E_2` places at `J_2`, and inductively `E_i` at `J_i` — until `E_n` places at
`J_n`, a corner.  Contradiction.

The cascade is the combinatorial content and is proved below.  Its three inputs are geometric and
are *not* verified: that each `a`- or `b`-edge places one `γ` (the side–angle correspondence), that
no junction takes two (`prop:vertexfigures`), and that the corners take none (`prop:cornerfig`).
The last two were relabelled PROVED in this week's audit, precisely because their Lean declarations
are the multiplicity arithmetic rather than the statements.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.GammaCascade

/-- **The cascade.**  If each of `n ≥ 1` edges places its `γ` at its left or right junction, no two
edges place at the same junction, and no edge places at `0` or at `n`, the placement is forced to
`place i = i` — which at `i = n` is a contradiction. -/
theorem cascade (n : ℕ) (hn : 1 ≤ n) (place : ℕ → ℕ)
    (hplace : ∀ i, 1 ≤ i → i ≤ n → place i = i - 1 ∨ place i = i)
    (hinj : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j → place i ≠ place j)
    (hends : ∀ i, 1 ≤ i → i ≤ n → place i ≠ 0 ∧ place i ≠ n) : False := by
  -- every edge is pushed to its right junction
  have key : ∀ i, 1 ≤ i → i ≤ n → place i = i := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hle
      rcases hplace (m + 1) (by omega) hle with h | h
      · -- it placed at `m`; but if `m ≥ 1` that junction is already taken by edge `m`
        simp only [Nat.add_sub_cancel] at h
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exact absurd h (hends 1 (by omega) hle).1
        · have hm' : place m = m := ih hm (by omega)
          exact absurd (h.trans hm'.symm) (hinj (m + 1) m (by omega) hle hm (by omega) (by omega))
      · exact h
  exact (hends n hn (le_refl n)).2 (key n hn (le_refl n))

/-- **Non-vacuity.**  Dropping `hends` leaves the satisfiable configuration `place i = i`, so the
cascade refutes the corner condition rather than restating an inconsistency already present. -/
theorem cascade_witness (n : ℕ) :
    (∀ i, 1 ≤ i → i ≤ n → (fun j => j) i = i - 1 ∨ (fun j => j) i = i) ∧
    (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j → (fun k => k) i ≠ (fun k => k) j) :=
  ⟨fun i _ _ => Or.inr rfl, fun i j _ _ _ _ h => h⟩

end Erdos634.GammaCascade
