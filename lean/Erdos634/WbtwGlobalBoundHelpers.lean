import Erdos634.WbtwTraceInTarget

/-!
# Every straddler's own trace endpoints reach the chord's own far end

Erdős #634. The small, reusable helper `exists_geometric_chain`'s successor case needs (confirmed
to work in isolation in earlier discarded assembly attempts): given a global oriented-trace
assignment, both of any straddling tile's own trace endpoints satisfy `Wbtw ℝ P · Q` — an immediate
corollary of `wbtw_of_mem_tile_trace` applied to each endpoint via its own membership in the trace.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **A straddler's near endpoint reaches the chord's own far end.** -/
theorem wbtw_near_endpoint_to_Q {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P Q : Plane}
    (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q) (R S : Fin N → Plane)
    (k : Fin N) (hktrace : (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k)) :
    Wbtw ℝ P (R k) Q :=
  wbtw_of_mem_tile_trace D f c hPQ k (by rw [hktrace]; exact left_mem_segment ℝ (R k) (S k))

/-- **A straddler's far endpoint reaches the chord's own far end.** -/
theorem wbtw_far_endpoint_to_Q {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P Q : Plane}
    (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q) (R S : Fin N → Plane)
    (k : Fin N) (hktrace : (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k)) :
    Wbtw ℝ P (S k) Q :=
  wbtw_of_mem_tile_trace D f c hPQ k (by rw [hktrace]; exact right_mem_segment ℝ (R k) (S k))

end Erdos634.ChordTraceReal
