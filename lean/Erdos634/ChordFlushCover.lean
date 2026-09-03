import Erdos634.ChordTraceReal

/-!
# Towards the flush total: `upperFlush` tiles are never needed (correcting the earlier "gap")

Erdős #634. `ChordTraceReal.lean`'s header records a self-caught "gap" in the plan to show
`lowerFlush ∪ straddlers` already covers a chord (minus finitely many vertices): that two
*different* `upperFlush` tiles might share a single point without violating anything. On closer
inspection **this is not a gap once the standard non-vertex convention is applied**, exactly the
one `Dissection.two_tiles_at_edge_point`/`chain_endpoints` already use everywhere: if `x` is not a
vertex of *any* tile, and both tiles at `x` were `upperFlush`, their two edges through `x` would
share more than the single point `x` (an open neighbourhood, since `x` is non-vertex to each), which
`Dissection.sameside_edges_subsingleton` already rules out. So the only way to actually get stuck at
an `upperFlush`-`upperFlush` junction is precisely at a *vertex* — already excluded.

`upperFlush_edge_endpoints_eq_c` is the key local fact: if a tile is `upperFlush` and touches the
chord at a non-vertex edge point, *both* of that edge's endpoints already lie exactly on the chord
line (forced by convexity: a strict combination of two values `≥ c` equals `c` only if both are
`c`).

**What this does NOT yet close**: excluding `upperFlush`-`upperFlush` junctions in full needs
walking along a maximal run of same-side flush edges sharing collinear endpoints until reaching a
vertex where the run necessarily ends (at a genuine dissection vertex, already in the standard
exceptional set) — a chain-style induction comparable to `BaseChain`/`WallChain`'s existing
development for walls, not yet built. `sameside_edges_subsingleton` alone only bounds any *two*
same-side edges' overlap to one point; it does not by itself rule out an unbroken sequence of
distinct `upperFlush` tiles' edges laid end-to-end along the whole line.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- A strict two-point convex combination equal to the common lower bound forces both endpoints to
equal it. -/
theorem eq_of_combo_eq_lb {a b c s : ℝ} (ha : c ≤ a) (hb : c ≤ b)
    (hs0 : 0 < s) (hs1 : s < 1) (heq : s * a + (1 - s) * b = c) : a = c ∧ b = c := by
  constructor <;> nlinarith

/-- **A non-vertex point on an `upperFlush` tile's edge forces both edge endpoints onto the chord
line.** -/
theorem upperFlush_edge_endpoints_eq_c (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hup : ∀ y ∈ T.carrier, c ≤ f y) {k : Fin 3} {x : Plane}
    (hx : x ∈ T.edge k) (hxv : ∀ m, x ≠ T.pts m) (hfx : f x = c) :
    f (T.pts k) = c ∧ f (T.pts (k + 1)) = c := by
  obtain ⟨s, t, hs, ht, hst, hxeq⟩ := hx
  have ht0 : t ≠ 0 := by
    intro h
    apply hxv k
    rw [← hxeq, h, zero_smul, add_zero]
    have hs1 : s = 1 := by linarith
    rw [hs1, one_smul]
  have hs0 : s ≠ 0 := by
    intro h
    apply hxv (k + 1)
    rw [← hxeq, h, zero_smul, zero_add]
    have ht1 : t = 1 := by linarith
    rw [ht1, one_smul]
  have hs0' : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hs1 : s < 1 := by
    have : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    linarith
  have hak : c ≤ f (T.pts k) := hup _ (T.edge_subset_carrier k (left_mem_segment ℝ _ _))
  have hak1 : c ≤ f (T.pts (k + 1)) := hup _ (T.edge_subset_carrier k (right_mem_segment ℝ _ _))
  have hcomb : s * f (T.pts k) + t * f (T.pts (k + 1)) = c := by
    rw [← hfx, ← hxeq]; simp [map_add, map_smul, smul_eq_mul]
  have ht' : t = 1 - s := by linarith
  rw [ht'] at hcomb
  exact eq_of_combo_eq_lb hak hak1 hs0' hs1 hcomb

end Erdos634.ChordTraceReal
