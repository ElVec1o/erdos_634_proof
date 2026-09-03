import Erdos634.ChordAssembly
import Erdos634.ChordStraddlerSegment

/-!
# A straddling target's chord endpoints are genuinely distinct

Erdős #634. Closes the remaining gap `chord_decomposition_of_no_straddlers` took as a hypothesis:
if a target straddles a line, its chord (`chord_isSegment`) has `p ≠ q`. Among the three vertices,
straddling gives some `i` with `f (pts i) < c` and some `j` with `f (pts j) > c`; the third vertex
`k` has some sign too, and pairing it with whichever of `i, j` has the opposite sign gives a
*second* crossing edge. Two crossing points on different edges are automatically distinct: a point
`lineMap a b r` (`r ∈ (0,1)`, `a ≠ b`) has the third barycentric coordinate exactly `0` and its own
two coordinates strictly positive, so a point shared between two segments built from different
pairs would need to be strictly positive *and* zero at the same coordinate.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.ChordTraceReal

/-- The barycentric coordinates of a point strictly between two vertices, via `lineMap`. -/
theorem lineMap_vertex_coords (T : Tri) (a b : Fin 3) (r : ℝ) (m : Fin 3) :
    T.basis.coord m (AffineMap.lineMap (T.pts a) (T.pts b) r)
      = AffineMap.lineMap (T.basis.coord m (T.pts a)) (T.basis.coord m (T.pts b)) r :=
  (T.basis.coord m).apply_lineMap (T.pts a) (T.pts b) r

/-- **A straddling triangle's chord has two distinct points.** -/
theorem straddle_two_distinct_points (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    {i j : Fin 3} (hi : f (T.pts i) < c) (hj : c < f (T.pts j)) :
    ∃ p q, p ∈ T.carrier ∩ {x | f x = c} ∧ q ∈ T.carrier ∩ {x | f x = c} ∧ p ≠ q := by
  have hij : i ≠ j := fun h => absurd (h ▸ hi) (not_lt.mpr hj.le)
  have hex3 : ∀ a b : Fin 3, a ≠ b → ∃ k, k ≠ a ∧ k ≠ b := by decide
  obtain ⟨k, hki, hkj⟩ := hex3 i j hij
  have hpts : ∀ n : Fin 3, T.pts n = (T.basis : Fin 3 → Plane) n := fun _ => rfl
  -- a crossing point strictly between two vertices of opposite sign
  have hcross : ∀ a b : Fin 3, f (T.pts a) < c → c < f (T.pts b) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ f (AffineMap.lineMap (T.pts a) (T.pts b) r) = c := by
    intro a b ha hb
    set g : ℝ → Plane := fun r => AffineMap.lineMap (T.pts a) (T.pts b) r with hgdef
    have hgc : Continuous g := by rw [hgdef]; fun_prop
    have hfg : Continuous (fun r => f (g r)) := f.continuous_of_finiteDimensional.comp hgc
    have h0 : f (g 0) < c := by simp [hgdef, ha]
    have h1 : c < f (g 1) := by simp [hgdef, hb]
    obtain ⟨r, hr01, hrc⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hfg.continuousOn
      (show c ∈ Set.Icc (f (g 0)) (f (g 1)) from ⟨h0.le, h1.le⟩)
    refine ⟨r, ?_, ?_, hrc⟩
    · rcases eq_or_lt_of_le hr01.1 with h | h
      · exact absurd (h ▸ hrc) (by simp only [hgdef]; simp only [← h, AffineMap.lineMap_apply_zero]; linarith)
      · exact h
    · rcases eq_or_lt_of_le hr01.2 with h | h
      · exact absurd (h ▸ hrc) (by simp only [hgdef]; simp only [h, AffineMap.lineMap_apply_one]; linarith)
      · exact h
  have hcoordm : ∀ a b m : Fin 3, m ≠ a → m ≠ b → ∀ r : ℝ,
      T.basis.coord m (AffineMap.lineMap (T.pts a) (T.pts b) r) = 0 := by
    intro a b m hma hmb r
    have h1 : T.basis.coord m (T.pts a) = 0 := by rw [hpts a]; exact T.basis.coord_apply_ne hma
    have h2 : T.basis.coord m (T.pts b) = 0 := by rw [hpts b]; exact T.basis.coord_apply_ne hmb
    rw [lineMap_vertex_coords, h1, h2, AffineMap.lineMap_apply_module]
    simp
  have hcoorda : ∀ a b : Fin 3, a ≠ b → ∀ r : ℝ,
      T.basis.coord a (AffineMap.lineMap (T.pts a) (T.pts b) r) = 1 - r := by
    intro a b hab r
    have h1 : T.basis.coord a (T.pts a) = 1 := by rw [hpts a]; exact T.basis.coord_apply_eq a
    have h2 : T.basis.coord a (T.pts b) = 0 := by
      rw [hpts b]; exact T.basis.coord_apply_ne hab
    rw [lineMap_vertex_coords, h1, h2, AffineMap.lineMap_apply_module]
    simp
  have hcoordb : ∀ a b : Fin 3, a ≠ b → ∀ r : ℝ,
      T.basis.coord b (AffineMap.lineMap (T.pts a) (T.pts b) r) = r := by
    intro a b hab r
    have h1 : T.basis.coord b (T.pts a) = 0 := by rw [hpts a]; exact T.basis.coord_apply_ne (Ne.symm hab)
    have h2 : T.basis.coord b (T.pts b) = 1 := by rw [hpts b]; exact T.basis.coord_apply_eq b
    rw [lineMap_vertex_coords, h1, h2, AffineMap.lineMap_apply_module]
    simp
  have hmem : ∀ a b : Fin 3, ∀ r ∈ Set.Icc (0:ℝ) 1,
      AffineMap.lineMap (T.pts a) (T.pts b) r ∈ T.carrier := by
    intro a b r hr
    have hav : T.pts a ∈ T.carrier := subset_convexHull ℝ _ (Set.mem_range_self a)
    have hbv : T.pts b ∈ T.carrier := subset_convexHull ℝ _ (Set.mem_range_self b)
    have hseg : AffineMap.lineMap (T.pts a) (T.pts b) r ∈ segment ℝ (T.pts a) (T.pts b) :=
      ⟨1 - r, r, by linarith [hr.2], hr.1, by ring, by rw [AffineMap.lineMap_apply_module]⟩
    exact T.convex.segment_subset hav hbv hseg
  rcases lt_trichotomy (f (T.pts k)) c with hk | hk | hk
  · obtain ⟨r1, hr1a, hr1b, hf1⟩ := hcross i j hi hj
    obtain ⟨r2, hr2a, hr2b, hf2⟩ := hcross k j hk hj
    refine ⟨AffineMap.lineMap (T.pts i) (T.pts j) r1, AffineMap.lineMap (T.pts k) (T.pts j) r2,
      ⟨hmem i j r1 ⟨hr1a.le, hr1b.le⟩, hf1⟩, ⟨hmem k j r2 ⟨hr2a.le, hr2b.le⟩, hf2⟩, ?_⟩
    intro heq
    have hc1 : T.basis.coord k (AffineMap.lineMap (T.pts i) (T.pts j) r1) = 0 :=
      hcoordm i j k hki hkj r1
    have hc2 : T.basis.coord k (AffineMap.lineMap (T.pts k) (T.pts j) r2) = 1 - r2 :=
      hcoorda k j hkj r2
    rw [heq, hc2] at hc1
    linarith
  · obtain ⟨r1, hr1a, hr1b, hf1⟩ := hcross i j hi hj
    refine ⟨T.pts k, AffineMap.lineMap (T.pts i) (T.pts j) r1,
      ⟨subset_convexHull ℝ _ (Set.mem_range_self k), hk⟩, ⟨hmem i j r1 ⟨hr1a.le, hr1b.le⟩, hf1⟩, ?_⟩
    intro heq
    have hc1 : T.basis.coord k (T.pts k) = 1 := by rw [hpts k]; exact T.basis.coord_apply_eq k
    have hc2 : T.basis.coord k (AffineMap.lineMap (T.pts i) (T.pts j) r1) = 0 :=
      hcoordm i j k hki hkj r1
    rw [heq, hc2] at hc1
    exact absurd hc1 (by norm_num)
  · obtain ⟨r1, hr1a, hr1b, hf1⟩ := hcross i j hi hj
    obtain ⟨r2, hr2a, hr2b, hf2⟩ := hcross i k hi hk
    refine ⟨AffineMap.lineMap (T.pts i) (T.pts j) r1, AffineMap.lineMap (T.pts i) (T.pts k) r2,
      ⟨hmem i j r1 ⟨hr1a.le, hr1b.le⟩, hf1⟩, ⟨hmem i k r2 ⟨hr2a.le, hr2b.le⟩, hf2⟩, ?_⟩
    intro heq
    have hc1 : T.basis.coord j (AffineMap.lineMap (T.pts i) (T.pts j) r1) = r1 :=
      hcoordb i j hij r1
    have hc2 : T.basis.coord j (AffineMap.lineMap (T.pts i) (T.pts k) r2) = 0 :=
      hcoordm i k j (Ne.symm hij) (Ne.symm hkj) r2
    rw [heq, hc2] at hc1
    linarith

end Erdos634.ChordTraceReal
