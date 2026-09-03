import Erdos634.ChordEndpointFrontier

/-!
# A chord's own extreme points lie on any convex region's frontier — generalized to any `Tri`

Erdős #634. `ChordEndpointFrontier.chord_endpoint_not_interior` is stated only for `D.target`, but
its proof never uses anything about `D.target` beyond its carrier and the chord identity — it
applies verbatim to *any* `Tri`, in particular a single tile. This is exactly the missing fact for
the `Finset`-sort construction's base case: a straddler's own trace endpoint is never interior to
*that tile itself* (not just never interior to the target), which is what rules out the current
position `p` (always some previous straddler's far endpoint, or `P`) from being interior to the
very last straddler placed.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A chord's own extreme point is not interior to the region it bounds.** As
`chord_endpoint_not_interior`, but for an arbitrary `Tri` `T` (in particular, a single tile) instead
of `D.target` specifically. -/
theorem chord_endpoint_not_interior' (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {T : Tri} {p q : Plane}
    (hpq : p ≠ q) (hseg : T.carrier ∩ {x | f x = c} = segment ℝ p q) :
    p ∉ interior T.carrier := by
  intro hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  have hpmem : p ∈ T.carrier ∩ {x | f x = c} := by
    rw [hseg]; exact left_mem_segment ℝ p q
  have hqmem : q ∈ T.carrier ∩ {x | f x = c} := by
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
  have hpt : p + t • v ∈ T.carrier := interior_subset (hball hmem)
  have hfpt : f (p + t • v) = c := by
    rw [map_add, map_smul, hfv, smul_eq_mul, mul_zero, add_zero, hfp]
  have hptseg : p + t • v ∈ segment ℝ p q := by
    rw [← hseg]; exact ⟨hpt, hfpt⟩
  have hlineeq : p + t • v = AffineMap.lineMap p q (-t) := by
    rw [AffineMap.lineMap_apply_module, hvdef]
    module
  rw [hlineeq, segment_eq_image_lineMap] at hptseg
  obtain ⟨s, hs, hseq⟩ := hptseg
  have hst : s = -t := AffineMap.lineMap_injective ℝ hpq hseq
  rw [hst] at hs
  have hneg : -t < 0 := by linarith
  linarith [hs.1]

end Erdos634.ChordTraceReal
