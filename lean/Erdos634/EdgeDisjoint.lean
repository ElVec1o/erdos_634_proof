import Erdos634.Dissection

/-!
# Two tiles cannot meet a line from the same side along a common stretch

Erdős #634.  `OrientBridge` records what the combinatorial march theorems still need before they
apply to a dissection: an indexing map sending a dissection and its base edge to the list of tile
orientations along it, in order.  `OrientBridge.edgePos_injOn_of_disjoint` builds that list from a
key, and leaves one geometric obligation — that distinct edges of the chain have disjoint open
spans.

This file discharges the local half of that obligation.  If two tiles have a common point in the
relative interiors of their edges, and lie on the same side of the common line there, their
interiors meet — so in a dissection, whose tiles have disjoint interiors, that cannot happen.

The machinery is already in `Dissection`: `Tri.inter_ball_eq_halfplane` says a tile is a half-plane
near a relative-interior edge point, and `Tri.ball_subset_of_pos` says a point with all
barycentric coordinates positive is interior.

**Non-vacuity.**  The hypotheses of `interiors_meet_of_same_side` are satisfiable: take `S = T`
and `l = k`, when `hside` is an identity and the conclusion is the true statement that a tile's
interior meets itself.  `no_same_side_contact` adds `i ≠ j`, so it is a genuine kill rather than a
reading of `False → False`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.EdgeDisjoint

open Erdos634.Geometry

/-- A nonconstant affine functional increases in some direction. -/
theorem exists_pos_dir (T : Tri) (k : Fin 3) : ∃ v : Plane, 0 < (T.basis.coord k).linear v := by
  have h := T.coord_linear_ne_zero k
  obtain ⟨v, hv⟩ : ∃ v, (T.basis.coord k).linear v ≠ 0 := by
    by_contra hc
    exact h (LinearMap.ext (by intro x; by_contra hx; exact hc ⟨x, hx⟩))
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · exact ⟨-v, by simpa using hlt⟩
  · exact ⟨v, hgt⟩

/-- Affine functionals along a ray. -/
theorem coord_add_smul (f : Plane →ᵃ[ℝ] ℝ) (x v : Plane) (t : ℝ) :
    f (x + t • v) = f x + t * f.linear v := by
  have h : x + t • v = (t • v) +ᵥ x := by simp [vadd_eq_add]; abel
  rw [h, f.map_vadd]
  simp [add_comm]

/-- **Same-side contact is impossible.**  Let `x` lie in the relative interior of edge `k` of `T`
and edge `l` of `S` — the two other barycentric coordinates positive at `x` in each — with `x` in
both carriers, and suppose the two tiles lie on the same side of the common line, in the sense that
the strict sides of the two edge coordinates agree.  Then the interiors of `T` and `S` meet.

In a dissection the interiors are disjoint, so two tiles never share a stretch of a line from the
same side; that is the disjointness `OrientBridge.edgePos_injOn_of_disjoint` asks for. -/
theorem interiors_meet_of_same_side (T S : Tri) (k l : Fin 3) (x : Plane)
    (hxT : x ∈ T.carrier) (hxS : x ∈ S.carrier)
    (hT1 : 0 < T.basis.coord (k + 1) x) (hT2 : 0 < T.basis.coord (k + 2) x)
    (hS1 : 0 < S.basis.coord (l + 1) x) (hS2 : 0 < S.basis.coord (l + 2) x)
    (hside : ∀ y : Plane, 0 < T.basis.coord k y ↔ 0 < S.basis.coord l y) :
    (interior T.carrier ∩ interior S.carrier).Nonempty := by
  classical
  -- every index is one of `k`, `k+1`, `k+2`
  have hfin : ∀ j i : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := by decide
  -- the four slack coordinates stay positive on a ball about `x`
  set W : Set Plane := {y | 0 < T.basis.coord (k + 1) y ∧ 0 < T.basis.coord (k + 2) y ∧
      0 < S.basis.coord (l + 1) y ∧ 0 < S.basis.coord (l + 2) y} with hW
  have hWopen : IsOpen W := by
    have c : ∀ (U : Tri) (j : Fin 3), Continuous (U.basis.coord j) := fun U j =>
      AffineMap.continuous_of_finiteDimensional _
    exact ((isOpen_lt continuous_const (c T (k+1))).inter
      ((isOpen_lt continuous_const (c T (k+2))).inter
        ((isOpen_lt continuous_const (c S (l+1))).inter
          (isOpen_lt continuous_const (c S (l+2))))))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hWopen x ⟨hT1, hT2, hS1, hS2⟩
  -- push `x` off the edge, into the tile
  obtain ⟨v, hv⟩ := exists_pos_dir T k
  have hvne : v ≠ 0 := by rintro rfl; simp at hv
  set t : ℝ := min (r / (2 * ‖v‖)) 1 with ht
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have htpos : 0 < t := lt_min (by positivity) one_pos
  set y : Plane := x + t • v with hy
  have hdist : dist y x < r := by
    have : dist y x = t * ‖v‖ := by
      simp [hy, dist_eq_norm, norm_smul, abs_of_pos htpos]
    rw [this]
    calc t * ‖v‖ ≤ (r / (2 * ‖v‖)) * ‖v‖ := by
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hvpos)
      _ = r / 2 := by field_simp
      _ < r := by linarith
  have hyW : y ∈ W := hball (Metric.mem_ball.mpr hdist)
  -- at `y` the `k`-coordinate is strictly positive
  have hTk : 0 < T.basis.coord k y := by
    have hx0 : 0 ≤ T.basis.coord k x := by
      have := (T.carrier_eq_nonneg_coord ▸ hxT : x ∈ {y | ∀ i, 0 ≤ T.basis.coord i y})
      exact this k
    have := coord_add_smul (T.basis.coord k) x v t
    rw [hy, this]
    nlinarith
  have hSl : 0 < S.basis.coord l y := (hside y).mp hTk
  -- all coordinates positive, in both tiles
  have hTall : ∀ i, 0 < T.basis.coord i y := by
    intro i
    rcases hfin k i with rfl | rfl | rfl
    · exact hTk
    · exact hyW.1
    · exact hyW.2.1
  have hSall : ∀ i, 0 < S.basis.coord i y := by
    intro i
    rcases hfin l i with rfl | rfl | rfl
    · exact hSl
    · exact hyW.2.2.1
    · exact hyW.2.2.2
  obtain ⟨rT, hrT, hsubT⟩ := T.ball_subset_of_pos hTall
  obtain ⟨rS, hrS, hsubS⟩ := S.ball_subset_of_pos hSall
  refine ⟨y, ?_, ?_⟩
  · exact mem_interior.mpr ⟨Metric.ball y rT, hsubT, Metric.isOpen_ball, Metric.mem_ball_self hrT⟩
  · exact mem_interior.mpr ⟨Metric.ball y rS, hsubS, Metric.isOpen_ball, Metric.mem_ball_self hrS⟩

/-- **The dissection form.**  Distinct tiles of a dissection never touch a line from the same side
along a common relative-interior point. -/
theorem no_same_side_contact {N : ℕ} (D : Dissection N) (i j : Fin N) (hij : i ≠ j)
    (k l : Fin 3) (x : Plane)
    (hxT : x ∈ (D.tile i).carrier) (hxS : x ∈ (D.tile j).carrier)
    (hT1 : 0 < (D.tile i).basis.coord (k + 1) x) (hT2 : 0 < (D.tile i).basis.coord (k + 2) x)
    (hS1 : 0 < (D.tile j).basis.coord (l + 1) x) (hS2 : 0 < (D.tile j).basis.coord (l + 2) x)
    (hside : ∀ y : Plane, 0 < (D.tile i).basis.coord k y ↔ 0 < (D.tile j).basis.coord l y) :
    False := by
  obtain ⟨y, hy1, hy2⟩ :=
    interiors_meet_of_same_side (D.tile i) (D.tile j) k l x hxT hxS hT1 hT2 hS1 hS2 hside
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hy1 hy2

end Erdos634.EdgeDisjoint
