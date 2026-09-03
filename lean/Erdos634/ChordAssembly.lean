import Erdos634.ChordTraceReal
import Erdos634.WallChain

/-!
# The chord decomposition: assembly, first piece

Erdős #634. Continuing the `ChordTrace` bridge. `ChordTraceReal.isSegment_of_convex_inter_hyperplane`
is general in its convex compact set `S`; applied to a dissection's own target (rather than a single
tile), it says a chord's intersection with the *whole* target is itself a single segment — the
object the rest of the assembly (`WallChain.wall_cover`/`.wall_partition`, `straddle_total_eq_sum`)
needs to work with.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **The chord itself is a segment.** For any dissection and any line meeting the target, the
target's intersection with the line is a single segment between two of its own points — the
`ChordTrace` object's own extent. -/
theorem chord_isSegment {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {x0 : Plane} (hx0 : x0 ∈ D.target.carrier) (hfx0 : f x0 = c) :
    ∃ p q, p ∈ D.target.carrier ∩ {x | f x = c} ∧ q ∈ D.target.carrier ∩ {x | f x = c}
      ∧ D.target.carrier ∩ {x | f x = c} = segment ℝ p q :=
  isSegment_of_convex_inter_hyperplane (Tri.convex_inter_hyperplane D.target f c)
    (Tri.isCompact_inter_hyperplane D.target f c) f hf c (fun _ hx => hx.2) x0 ⟨hx0, hfx0⟩

end Erdos634.ChordTraceReal
