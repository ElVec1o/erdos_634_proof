import Erdos634.ChordTraceReal
import Erdos634.ChordAssembly

/-!
# A chord's own extreme points lie on the target's frontier

Erdős #634. Continuing the chord-decomposition assembly: `WallChain.wall_cover`/`.wall_partition`
need `openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier`. For the chord's *own* endpoints `p, q`
(`ChordAssembly.chord_isSegment`), this file supplies the fact that makes the hypothesis reachable:
`p` and `q` themselves are never interior to the target — if `p` were interior, a small ball
around it would contain a point of the line strictly beyond `p` (away from `q`), which would then
lie in the target too (ball ⊆ target) and on the line, forcing it into `segment ℝ p q` by the
chord identity — but that point's own `lineMap` parameter is negative, while every point of the
segment has parameter in `[0, 1]`, contradiction via `AffineMap.lineMap`'s injectivity.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A chord's own extreme point is not interior to the target.** -/
theorem chord_endpoint_not_interior {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {p q : Plane} (hpq : p ≠ q)
    (hseg : D.target.carrier ∩ {x | f x = c} = segment ℝ p q) :
    p ∉ interior D.target.carrier := by
  intro hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  have hpmem : p ∈ D.target.carrier ∩ {x | f x = c} := by
    rw [hseg]; exact left_mem_segment ℝ p q
  have hqmem : q ∈ D.target.carrier ∩ {x | f x = c} := by
    rw [hseg]; exact right_mem_segment ℝ p q
  have hfp : f p = c := hpmem.2
  have hfq : f q = c := hqmem.2
  set v : Plane := p - q with hvdef
  have hvne : v ≠ 0 := sub_ne_zero.mpr hpq
  have hfv : f v = 0 := by rw [hvdef, map_sub, hfp, hfq, sub_self]
  set t : ℝ := r / (2 * ‖v‖) with htdef
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have htpos : 0 < t := by positivity
  have hmem : p + t • v ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_eq_norm, show p + t • v - p = t • v by abel, norm_smul,
      Real.norm_eq_abs, abs_of_pos htpos, htdef]
    have heq : r / (2 * ‖v‖) * ‖v‖ = r / 2 := by field_simp
    rw [heq]; linarith
  have hpt : p + t • v ∈ D.target.carrier := interior_subset (hball hmem)
  have hfpt : f (p + t • v) = c := by
    rw [map_add, map_smul, hfv, smul_eq_mul, mul_zero, add_zero, hfp]
  have hptseg : p + t • v ∈ segment ℝ p q := by
    rw [← hseg]; exact ⟨hpt, hfpt⟩
  have hlineeq : p + t • v = AffineMap.lineMap p q (-t) := by
    rw [AffineMap.lineMap_apply_module, hvdef]
    module
  rw [hlineeq, segment_eq_image_lineMap] at hptseg
  obtain ⟨s, hs, hseq⟩ := hptseg
  have : s = -t := AffineMap.lineMap_injective ℝ hpq hseq
  rw [this] at hs
  have : -t < 0 := by linarith
  linarith [hs.1]

end Erdos634.ChordTraceReal
