import Erdos634.FlushJoin
import Erdos634.CongruentTileEdges

/-!
# `sideLen ∈ {a, b, c}`, and the wall length as a nonnegative integer combination

Erdős #634.  `FlushJoin.sum_sideLen_eq_dist` gives `∑ sideLen = dist P Q` over the chain of a wall
segment.  `MidTriangleE1.base_single_b` consumes an identity of the shape `u·a + v·b + w·c =
length` with `u, v, w : ℕ`.  This file is the bridge: every chain edge's length is one of the
model tile's three side lengths (congruence), so the chain partitions into three blocks and the sum collapses to a counted combination.

The partition is by successive filtering, so **no distinctness of `a`, `b`, `c` is needed** — if
two of them coincided the split would merely be non-canonical, and the identity still holds.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FlushCounts

open Erdos634.Geometry Erdos634.FlushJoin Finset

variable {N : ℕ}

/-- The model's three side lengths, as the multiset congruence preserves. -/
noncomputable def modelSides (D : CongruentDissection N) : Multiset ℝ :=
  {dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
    dist (D.model.pts 1) (D.model.pts 2)}

/-- **Every tile side has one of the model's three lengths.** -/
theorem sideLen_mem_modelSides (D : CongruentDissection N) (e : Fin N × Fin 3) :
    sideLen D.toDissection e ∈ modelSides D := by
  have hshift := Tri.sideMultiset_shift (D.tile e.1) e.2
  have hmulti := (D.tiles_congruent e.1).sideMultiset_eq
  have : sideLen D.toDissection e ∈
      ({dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2+1)),
        dist ((D.tile e.1).pts (e.2+2)) ((D.tile e.1).pts e.2),
        dist ((D.tile e.1).pts (e.2+1)) ((D.tile e.1).pts (e.2+2))} : Multiset ℝ) := by
    simp [sideLen]
  rwa [hshift, hmulti] at this

/-- **`sideLen` is `a`, `b` or `c`.** -/
theorem sideLen_eq_or (D : CongruentDissection N) (e : Fin N × Fin 3) :
    sideLen D.toDissection e = dist (D.model.pts 0) (D.model.pts 1) ∨
    sideLen D.toDissection e = dist (D.model.pts 2) (D.model.pts 0) ∨
    sideLen D.toDissection e = dist (D.model.pts 1) (D.model.pts 2) := by
  have := sideLen_mem_modelSides D e
  simpa [modelSides] using this

/-! ## Collapsing the sum to a counted combination -/

variable (D : CongruentDissection N)

/-- Splitting off the `a`-block, then the `b`-block, from a sum of values in `{a, b, c}`. -/
theorem sum_eq_counts {a b c : ℝ} (s : Finset (Fin N × Fin 3)) (g : Fin N × Fin 3 → ℝ)
    (hg : ∀ e ∈ s, g e = a ∨ g e = b ∨ g e = c) :
    ∃ na nb nc : ℕ, ∑ e ∈ s, g e = na * a + nb * b + nc * c := by
  classical
  refine ⟨(s.filter (fun e => g e = a)).card,
    ((s.filter (fun e => ¬ g e = a)).filter (fun e => g e = b)).card,
    ((s.filter (fun e => ¬ g e = a)).filter (fun e => ¬ g e = b)).card, ?_⟩
  have h1 : ∑ e ∈ s.filter (fun e => g e = a), g e
      = ((s.filter (fun e => g e = a)).card : ℝ) * a := by
    rw [Finset.sum_congr rfl (fun e he => (mem_filter.mp he).2), Finset.sum_const, nsmul_eq_mul]
  set t := s.filter (fun e => ¬ g e = a) with ht
  have hgt : ∀ e ∈ t, g e = b ∨ g e = c := by
    intro e he
    rw [ht, mem_filter] at he
    rcases hg e he.1 with h | h | h
    · exact absurd h he.2
    · exact Or.inl h
    · exact Or.inr h
  have h2 : ∑ e ∈ t.filter (fun e => g e = b), g e
      = ((t.filter (fun e => g e = b)).card : ℝ) * b := by
    rw [Finset.sum_congr rfl (fun e he => (mem_filter.mp he).2), Finset.sum_const, nsmul_eq_mul]
  have h3 : ∑ e ∈ t.filter (fun e => ¬ g e = b), g e
      = ((t.filter (fun e => ¬ g e = b)).card : ℝ) * c := by
    refine (Finset.sum_congr rfl (fun e he => ?_)).trans
      (by rw [Finset.sum_const, nsmul_eq_mul])
    rw [mem_filter] at he
    rcases hgt e he.1 with h | h
    · exact absurd h he.2
    · exact h
  rw [← Finset.sum_filter_add_sum_filter_not s (fun e => g e = a) g, h1, ← ht,
    ← Finset.sum_filter_add_sum_filter_not t (fun e => g e = b) g, h2, h3]
  ring

/-- **The wall-length identity in counted form.**  On a wall segment whose chain edges are
contained in it, there are nonnegative integers `na, nb, nc` with
`na·a + nb·b + nc·c = dist P Q`. -/
theorem exists_counts_of_wall (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) (P Q : Plane) (hPQ : P ≠ Q)
    (hS : segment ℝ P Q ⊆ {y | f y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hsub : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ P Q) :
    ∃ na nb nc : ℕ,
      na * dist (D.model.pts 0) (D.model.pts 1)
        + nb * dist (D.model.pts 2) (D.model.pts 0)
        + nc * dist (D.model.pts 1) (D.model.pts 2) = dist P Q := by
  obtain ⟨na, nb, nc, hcount⟩ :=
    sum_eq_counts (a := dist (D.model.pts 0) (D.model.pts 1))
      (b := dist (D.model.pts 2) (D.model.pts 0))
      (c := dist (D.model.pts 1) (D.model.pts 2))
      (D.lineChain f c) (sideLen D.toDissection)
      (fun e _ => sideLen_eq_or D e)
  refine ⟨na, nb, nc, ?_⟩
  rw [← hcount]
  exact sum_sideLen_eq_dist D.toDissection f hf c P Q hPQ hS hint hwall hsub

end Erdos634.FlushCounts
