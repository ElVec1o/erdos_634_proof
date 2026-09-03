import Erdos634.ChordAssembly
import Erdos634.ChordTraceReal

/-!
# Every straddler's trace lies within the target's own chord

Erdős #634. The global simplification the `Finset`-sort construction needs: every straddling tile's
trace endpoints lie on the *target's own* chord (`ChordAssembly.chord_isSegment`'s `segment ℝ P Q`),
not merely on the line — so `Wbtw ℝ P x Q` holds for `x` in *any* straddler's trace, with `P, Q`
fixed once for the whole dissection. This lets every order comparison in the sort-and-recurse
construction go through `wbtw_trichotomy_of_wbtw`/`_antisymm_`/`_trans_` using the *same* fixed
upper bound `Q` throughout, rather than a bound that would otherwise need to shift with each
recursive sub-chord.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **Every straddler's trace lies within the target's own chord.** Given the target's own chord
endpoints `P, Q` (`D.target.carrier ∩ {f = c} = segment ℝ P Q`), any point of any tile's trace
(in particular, a straddler's) satisfies `Wbtw ℝ P x Q`. -/
theorem wbtw_of_mem_tile_trace {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {P Q : Plane}
    (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (k : Fin N) {x : Plane} (hx : x ∈ (D.tile k).carrier ∩ {y | f y = c}) :
    Wbtw ℝ P x Q := by
  have hxtarget : x ∈ D.target.carrier ∩ {y | f y = c} :=
    ⟨tile_subset_target D k hx.1, hx.2⟩
  rw [hPQ] at hxtarget
  exact mem_segment_iff_wbtw.mp hxtarget

end Erdos634.ChordTraceReal
