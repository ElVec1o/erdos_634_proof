import Erdos634.ChordTraceReal

/-!
# Any point strictly between two of a straddler's own chord points is interior

Erdős #634. Generalizes `Tri.straddle_midpoint_interior` (which only gave the midpoint) to any
point of the open segment between two distinct points of `T.carrier ∩ {f = c}`, given `T` straddles
the line. This is exactly what the chord-decomposition assembly's base case (zero straddlers, or
more generally each "gap" between straddler traces) needs: applied to `T = D.target` itself, it
shows the whole *open* chord between the target's own two chord endpoints is interior to the
target, matching `wall_cover`'s `hint` hypothesis.

The proof is `Tri.straddle_midpoint_interior`'s argument verbatim, with the fixed weight `1/2`
replaced by a general `s ∈ (0, 1)`.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- **Any strict convex combination of two of a straddler's own chord points is interior.** -/
theorem Tri.straddle_openSegment_interior (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hlo : ∃ i, f (T.pts i) < c) (hhi : ∃ j, c < f (T.pts j))
    {x y : Plane} (hx : x ∈ T.carrier) (hfx : f x = c) (hy : y ∈ T.carrier) (hfy : f y = c)
    (hxy : x ≠ y) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    AffineMap.lineMap x y s ∈ interior T.carrier := by
  apply Tri.mem_interior_of_pos T
  intro k
  have hxk : 0 ≤ T.basis.coord k x := by
    have h := hx; rw [T.carrier_eq_nonneg_coord] at h; exact h k
  have hyk : 0 ≤ T.basis.coord k y := by
    have h := hy; rw [T.carrier_eq_nonneg_coord] at h; exact h k
  have havg : (T.basis.coord k) (AffineMap.lineMap x y s)
      = AffineMap.lineMap (T.basis.coord k x) (T.basis.coord k y) s :=
    (T.basis.coord k).apply_lineMap x y s
  rw [havg, AffineMap.lineMap_apply_module]
  rcases eq_or_lt_of_le hxk with hxk0 | hxk0
  · rcases eq_or_lt_of_le hyk with hyk0 | hyk0
    · exfalso
      have hfline : (T.basis.coord k : Plane →ᵃ[ℝ] ℝ).linear ≠ 0 := T.coord_linear_ne_zero k
      have hgx : (T.basis.coord k) x = (T.basis.coord k) y := by rw [← hxk0, ← hyk0]
      have hffx : f.toAffineMap x = f.toAffineMap y := hfx.trans hfy.symm
      have h1 := Tri.straddle_no_edge_on_line T f c hlo hhi k
      have hk1ne : (k : Fin 3) ≠ k + 1 := by fin_cases k <;> decide
      have hk2ne : (k : Fin 3) ≠ k + 2 := by fin_cases k <;> decide
      have hpts : ∀ m : Fin 3, T.pts m = (T.basis : Fin 3 → Plane) m := fun _ => rfl
      have hz1 : (T.basis.coord k) (T.pts (k + 1)) = (T.basis.coord k) x := by
        rw [hpts, ← hxk0]; exact T.basis.coord_apply_ne hk1ne
      have hz2 : (T.basis.coord k) (T.pts (k + 2)) = (T.basis.coord k) x := by
        rw [hpts, ← hxk0]; exact T.basis.coord_apply_ne hk2ne
      have hres1 : f.toAffineMap (T.pts (k + 1)) = f.toAffineMap x :=
        eq_of_mem_line_of_agree hfline hxy hgx hz1 (f := f.toAffineMap) hffx
      have hres2 : f.toAffineMap (T.pts (k + 2)) = f.toAffineMap x :=
        eq_of_mem_line_of_agree hfline hxy hgx hz2 (f := f.toAffineMap) hffx
      simp only [LinearMap.coe_toAffineMap] at hres1 hres2
      rw [hfx] at hres1 hres2
      rcases h1 with h | h
      · exact h hres1
      · exact h hres2
    · have hsum : 0 < (1 - s) * T.basis.coord k x + s * T.basis.coord k y := by nlinarith
      simpa [smul_eq_mul] using hsum
  · have hsum : 0 < (1 - s) * T.basis.coord k x + s * T.basis.coord k y := by nlinarith
    simpa [smul_eq_mul] using hsum

end Erdos634.ChordTraceReal
