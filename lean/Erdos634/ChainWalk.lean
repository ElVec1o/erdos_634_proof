import Mathlib
import Erdos634.ChainInstance
import Erdos634.VertexFigureReal

/-!
# The chain-to-walk dictionary

Erdős #634.  Twelve PROVED statements stop at the same place: they know a side's *chain* of tile
edges and need its *walk* — the counts `P', Q', R'` of `a`-, `b`- and `c`-edges satisfying
`P'a + Q'b + R'c = ` the side's length.

Two steps bridge that.  The lengths of a contiguous chain telescope to the side's length, and
counting the edges by their length turns that sum into the walk equation.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ChainWalk

open Finset

/-- **The chain's lengths telescope.**  Contiguous shadows, so the lengths sum to the total span. -/
theorem telescope : ∀ n : ℕ, 1 ≤ n → ∀ L R : ℕ → ℝ, (∀ j, j + 1 < n → R j = L (j + 1)) →
    ∑ j ∈ Finset.range n, (R j - L j) = R (n - 1) - L 0 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro _ L R hcontig
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hstep := ih hm L R (fun j hj => hcontig j (by omega))
      rw [Finset.sum_range_succ, hstep]
      have hc : R (m - 1) = L m := by
        have heq : m - 1 + 1 = m := by omega
        have h := hcontig (m - 1) (by omega)
        rwa [heq] at h
      simp only [Nat.add_sub_cancel]
      rw [hc]
      ring

/-- **Counting the chain by edge length gives the walk.**  If every edge of the chain has length
`a`, `b` or `c`, the total span is `P'a + Q'b + R'c` with `P'`, `Q'`, `R'` the counts. -/
theorem walk_of_chain (n : ℕ) (len : ℕ → ℝ) (a b c : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hmem : ∀ j ∈ Finset.range n, len j ∈ ({a, b, c} : Finset ℝ)) :
    ∑ j ∈ Finset.range n, len j
      = ((Finset.range n).filter (fun j => len j = a)).card * a
        + ((Finset.range n).filter (fun j => len j = b)).card * b
        + ((Finset.range n).filter (fun j => len j = c)).card * c := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmem len]
  rw [show ({a, b, c} : Finset ℝ) = insert a (insert b {c}) from rfl]
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]
  have hgen : ∀ v : ℝ, ∑ i ∈ (Finset.range n).filter (fun j => len j = v), len i
      = ((Finset.range n).filter (fun j => len j = v)).card * v := by
    intro v
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const,
      nsmul_eq_mul]
  rw [hgen a, hgen b, hgen c]
  ring

/-! ## The dictionary itself

Putting the two together: a contiguous chain whose every edge has one of the three tile lengths
satisfies the walk equation, with the walk's counts being the numbers of edges of each length. -/

/-- **The chain-to-walk dictionary.**  For a contiguous chain of `n` edges, each of length `a`, `b`
or `c`, the span from the first edge's start to the last edge's end is `P'a + Q'b + R'c`, where
`P'`, `Q'`, `R'` count the edges of each length. -/
theorem chain_walk (n : ℕ) (hn : 1 ≤ n) (L R : ℕ → ℝ) (a b c : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcontig : ∀ j, j + 1 < n → R j = L (j + 1))
    (hlen : ∀ j ∈ Finset.range n, R j - L j ∈ ({a, b, c} : Finset ℝ)) :
    R (n - 1) - L 0
      = ((Finset.range n).filter (fun j => R j - L j = a)).card * a
        + ((Finset.range n).filter (fun j => R j - L j = b)).card * b
        + ((Finset.range n).filter (fun j => R j - L j = c)).card * c := by
  rw [← telescope n hn L R hcontig]
  exact walk_of_chain n (fun j => R j - L j) a b c hab hac hbc hlen

/-- **Positivity of a count.**  If some edge of the chain has length `a`, the walk's `a`-count is
positive — the step `lem:ccornerside` needs. -/
theorem count_pos (n : ℕ) (len : ℕ → ℝ) (a : ℝ) (j : ℕ) (hj : j ∈ Finset.range n)
    (hja : len j = a) :
    0 < ((Finset.range n).filter (fun i => len i = a)).card := by
  classical
  refine Finset.card_pos.mpr ⟨j, ?_⟩
  exact Finset.mem_filter.mpr ⟨hj, hja⟩

end Erdos634.ChainWalk
