-- ChordInterface.lean — the geometric facts the chord arguments consume, named as hypotheses.
--
-- Most of this development's remaining PROVED-not-VERIFIED content is geometric, and the same few
-- facts recur: by frequency in the companion, "far side" (35 appeals), "corner tile" (20),
-- "both ends" (8), "whole tile edges" (5). Rather than leave those implicit in prose, this file
-- states the one that carries the chord arguments as an explicit datum, and proves the conclusions
-- from it. Nothing here is `sorry`: the geometry is a HYPOTHESIS, not a gap, so the corpus keeps its
-- zero-sorry property and the outstanding obligation is named instead of hidden.
--
-- SCOPE. The far-side covering itself is NOT introduced here: it is obligation G3 of
-- `Dissection.lean`, `HasEdgeChains`. STATUS UPDATE (2026-08-15): that covering is now PROVED —
-- `WallChain.lean` shows each side of a wall segment is covered exactly once by whole tile edges
-- (`Dissection.wall_partition`, `wall_two_sided`, per-edge `edge_two_sided`), with tile edges
-- walls by `edge_point_not_interior` and breakpoints at tiling vertices by
-- `EdgeChain.Dissection.chain_breakpoint_vertex`. What `FarSide` still packages beyond that is
-- bookkeeping, not geometry: the ORDER of the run (edges laid end to end from the blocked end,
-- so that meeting points sit at prefix sums) is an extraction from the proved partition that is
-- not yet formalized. `FarSide` remains the per-chord shadow of G3 in that ordered form.

import Mathlib.Tactic

namespace Erdos634.ChordInterface

/-- **The far-side datum of a blocked chord.** For a tile edge `[X,Y]` whose extension beyond `X`
is blocked — by the target boundary, or by the interior of a placed tile — the opposite side of
`[X,Y]` is covered by whole tile edges laid end to end starting at `X`. `run` records their lengths
in order. The meeting points, hence the vertices interior to `[X,Y]`, sit at the proper partial sums.

Blocking at `X` is what makes the list start at `X` rather than before it; the final entry may
overrun `Y`, which is why no relation between `run.sum` and the edge length is asserted. -/
structure FarSide (a b c : ℕ) where
  /-- the covering edge lengths, in order from the blocked end -/
  run : List ℕ
  /-- each entry is a tile side -/
  isSide : ∀ l ∈ run, l = a ∨ l = b ∨ l = c

/-- A nonempty run of tile sides has total at least the least side. -/
theorem sum_ge_min {a b c : ℕ} (hab : a ≤ b) (hac : a ≤ c)
    (L : List ℕ) (hL : ∀ l ∈ L, l = a ∨ l = b ∨ l = c) (hne : L ≠ []) :
    a ≤ L.sum := by
  cases L with
  | nil => exact absurd rfl hne
  | cons h t =>
    have hh : h = a ∨ h = b ∨ h = c := hL h (List.mem_cons_self)
    have : a ≤ h := by rcases hh with rfl | rfl | rfl <;> omega
    simp only [List.sum_cons]
    omega

/-- **Clearance.** If the edge `[X,Y]` has length at most the least tile side, no vertex of the
tiling lies in its relative interior. Concretely: a meeting point sits at the sum of a nonempty
proper prefix of `run`, and every such sum is at least `a`, hence not `< L`.

This is Lemma (blocked-end quantization)'s clearance half, with the geometry supplied by `FarSide`
and the arithmetic discharged here. -/
theorem no_interior_vertex {a b c L : ℕ} (hab : a ≤ b) (hac : a ≤ c) (hL : L ≤ a)
    (F : FarSide a b c) (pre : List ℕ) (hpre : pre ≠ [])
    (hsub : ∀ l ∈ pre, l ∈ F.run) (hlt : pre.sum < L) : False := by
  have hside : ∀ l ∈ pre, l = a ∨ l = b ∨ l = c := fun l hl => F.isSide l (hsub l hl)
  have := sum_ge_min hab hac pre hside hpre
  omega

/-- **Quantization.** Every meeting point lies at a distance that is a sum of tile sides, so the
positions available to interior vertices are exactly the elements of `⟨a,b,c⟩` below the edge
length. Stated here as: a prefix sum is a sum of tile sides, which is what the semigroup arguments
in `Frontier.lean` consume. -/
theorem prefix_sum_is_semigroup {a b c : ℕ} (F : FarSide a b c)
    (pre : List ℕ) (hsub : ∀ l ∈ pre, l ∈ F.run) :
    ∃ x y z : ℕ, pre.sum = x * a + y * b + z * c := by
  induction pre with
  | nil => exact ⟨0, 0, 0, by simp⟩
  | cons h t ih =>
    obtain ⟨x, y, z, hxyz⟩ := ih (fun l hl => hsub l (List.mem_cons_of_mem h hl))
    have hh : h = a ∨ h = b ∨ h = c := F.isSide h (hsub h (List.mem_cons_self))
    simp only [List.sum_cons]
    rcases hh with rfl | rfl | rfl
    · exact ⟨x + 1, y, z, by rw [hxyz]; ring⟩
    · exact ⟨x, y + 1, z, by rw [hxyz]; ring⟩
    · exact ⟨x, y, z + 1, by rw [hxyz]; ring⟩

end Erdos634.ChordInterface
