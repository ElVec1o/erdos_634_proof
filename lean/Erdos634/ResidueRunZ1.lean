import Erdos634.ThickBlockingLemmas

/-!
# The residue of the 19-tile partial `Z1` at `(e,f) = (2,3)`: the run of length `4 = e²` that
# terminates on the left leg, and the tile-free blocking lemma it forces

Erdős #634, base-`β` branch, thick member `(2,3)`, tile `(6,5,9)`, `N = 23`, base word `aabbcca`.

## Provenance and what is claimed

`data/witnesses/Z1_basebeta_2_3_partial19.tsv` is a certified 19-of-23 partial dissection.  Its
uncovered region (area exactly `4` tiles, one component) has, on its boundary, a **straight run of
length exactly `4`** from the point `v = (14, √32)` — a vertex of `Z1`'s tile `5`, and a `T`-point
on the `b`-edge of `Z1`'s tile `17` — to the point `(46/3, 5√32/3)`, which is a vertex of tile
`17` and lies **on the target's left leg**.  The run is clamped at both ends by convex corners of
the uncovered region (angles `α+β` at `v`, `β+γ` at the leg end).

In any completion, the tile adjacent to that run at `v` has a corner at `v` and an edge along the
ray `d₀ = (1/3, √32/6)`, of length `5`, `6` or `9`; the ray leaves the target at distance `4`.
So **every one of the six oriented placements at `v` along `d₀` escapes the target** — a fact about
the target alone, in the exact pattern of `ThickBlockingLemmas.blocking_B1`.  That is what is proved
here (`blocking_Z1run`), together with the frame (`Z1run_frame`: vertex `0` is `v`, vertex `1` is on
the ray), the non-vacuity witness (`Z1run_witness`: tiles `5` and `17` are congruent to the tile,
inside the target, interior-disjoint, and `v`, the ray and the leg point are where the statement
says), and the arithmetic fact that the exposed lengths `1, 3, 4` seen on the `aabbcca` tree are not
in the numerical semigroup `⟨6,5,9⟩` (`gap_lengths_not_in_semigroup`).

**Not claimed.**  Neither "`Z1` extends to no dissection" nor "no dissection has base word
`aabbcca`" is stated: both need the placement-rule completeness (the geometric half of H7) and the
run-partition lemma ("a frontier run clamped by two convex corners is a union of tile edges"),
neither of which is formalized.  Every theorem below is a finite statement about explicit
coordinate triangles and the target; no `sorry`, standard axioms only.

Every coordinate is exact in `ℚ(√32)`; `rr = √32`.
-/

namespace Erdos634.ResidueRunZ1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.BaseBetaTargetCoord
open Erdos634.ThickBlockingLemmas

/-! ## 1. The corner, the ray, and the leg point -/

/-- The ray direction `d₀ = (1/3, √32/6)` is a unit vector. -/
theorem d0_unit : ((1/3 : ℝ))^2 + ((1/6 : ℝ)*rr)^2 = 1 := by nlinarith [rr_sq]

/-- `v + 4·d₀ = (46/3, 5√32/3)` lies on the target's **left leg** (`(5/2)√32·x − 23·y = 0`). -/
theorem legpoint_on_left_leg : (5/2 : ℝ)*rr*(46/3 : ℝ) - 23*((5/3 : ℝ)*rr) = 0 := by ring

/-- `v + 4·d₀` is indeed `(46/3, 5√32/3)`. -/
theorem legpoint_eq : (14 : ℝ) + 4*(1/3 : ℝ) = 46/3 ∧ (1 : ℝ)*rr + 4*((1/6 : ℝ)*rr) = (5/3 : ℝ)*rr := by
  constructor <;> ring

/-- **The ray leaves the target at distance exactly 4.**  For `t > 4` the point `v + t·d₀` is
strictly beyond the left leg, hence outside the target. -/
theorem ray_escapes_beyond_four {t : ℝ} (ht : 4 < t) :
    mkPt ((14 : ℝ) + t*(1/3 : ℝ)) ((1 : ℝ)*rr + t*((1/6 : ℝ)*rr)) ∉ target63.carrier :=
  not_mem_target63_of_left (by nlinarith [rr_pos])

/-! ## 2. Arithmetic: the exposed lengths are below the shortest side -/

/-- The run lengths exposed on the `aabbcca` tree at doubly-clamped frontier runs are `1`, `3`, `4`;
none is a nonnegative integer combination of the sides `6, 5, 9` (they are below the shortest
side).  The Frobenius structure of `⟨5,6,9⟩` beyond `min = 5` is **not** used anywhere. -/
theorem gap_lengths_not_in_semigroup :
    ∀ x y z : ℕ, 6*x + 5*y + 9*z ≠ 4 ∧ 6*x + 5*y + 9*z ≠ 3 ∧ 6*x + 5*y + 9*z ≠ 1 := by
  intro x y z; omega

/-! ## 3. The six oriented placements at `v = (14, √32)` along `d₀ = (1/3, √32/6)`,
body on the residue (clockwise) side -/

theorem det_za59 : det3 (14 : ℝ) ((1 : ℝ)*rr) (47/3 : ℝ) ((11/6 : ℝ)*rr) (65/3 : ℝ) ((11/6 : ℝ)*rr) ≠ 0 := by
  have h : det3 (14 : ℝ) ((1 : ℝ)*rr) (47/3 : ℝ) ((11/6 : ℝ)*rr) (65/3 : ℝ) ((11/6 : ℝ)*rr) = (-5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_lt (by nlinarith [rr_pos])

/-- Candidate `za59` at the corner `v = (14, √32)` on the ray `d₀ = (1/3, √32/6)`: side `5` along the ray, body clockwise of `d₀` (the residue side). -/
noncomputable def za59 : Tri := mkTri (14 : ℝ) ((1 : ℝ)*rr) (47/3 : ℝ) ((11/6 : ℝ)*rr) (65/3 : ℝ) ((11/6 : ℝ)*rr) det_za59

/-- **`za59` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_za59 :
    dist (za59.pts 0) (za59.pts 1) ^ 2 = (25 : ℝ) ∧
    dist (za59.pts 1) (za59.pts 2) ^ 2 = (36 : ℝ) ∧
    dist (za59.pts 2) (za59.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (14 : ℝ) ((1 : ℝ)*rr)) (mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq
  · show dist (mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr)) (mkPt (65/3 : ℝ) ((11/6 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (65/3 : ℝ) ((11/6 : ℝ)*rr)) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq

/-- **Escape.**  `za59`'s vertex `1` (the far end of its edge along `d₀`) lies strictly beyond the left leg. -/
theorem escape_za59 : ¬ (za59.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (za59.pts 1) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  have he : za59.pts 1 = mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_za95 : det3 (14 : ℝ) ((1 : ℝ)*rr) (17 : ℝ) ((5/2 : ℝ)*rr) (493/27 : ℝ) ((79/54 : ℝ)*rr) ≠ 0 := by
  have h : det3 (14 : ℝ) ((1 : ℝ)*rr) (17 : ℝ) ((5/2 : ℝ)*rr) (493/27 : ℝ) ((79/54 : ℝ)*rr) = (-5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_lt (by nlinarith [rr_pos])

/-- Candidate `za95` at the corner `v = (14, √32)` on the ray `d₀ = (1/3, √32/6)`: side `9` along the ray, body clockwise of `d₀` (the residue side). -/
noncomputable def za95 : Tri := mkTri (14 : ℝ) ((1 : ℝ)*rr) (17 : ℝ) ((5/2 : ℝ)*rr) (493/27 : ℝ) ((79/54 : ℝ)*rr) det_za95

/-- **`za95` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_za95 :
    dist (za95.pts 0) (za95.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (za95.pts 1) (za95.pts 2) ^ 2 = (36 : ℝ) ∧
    dist (za95.pts 2) (za95.pts 0) ^ 2 = (25 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (14 : ℝ) ((1 : ℝ)*rr)) (mkPt (17 : ℝ) ((5/2 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((9/4 : ℝ)) * rr_sq
  · show dist (mkPt (17 : ℝ) ((5/2 : ℝ)*rr)) (mkPt (493/27 : ℝ) ((79/54 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((784/729 : ℝ)) * rr_sq
  · show dist (mkPt (493/27 : ℝ) ((79/54 : ℝ)*rr)) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((625/2916 : ℝ)) * rr_sq

/-- **Escape.**  `za95`'s vertex `1` (the far end of its edge along `d₀`) lies strictly beyond the left leg. -/
theorem escape_za95 : ¬ (za95.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (za95.pts 1) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  have he : za95.pts 1 = mkPt (17 : ℝ) ((5/2 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_zb69 : det3 (14 : ℝ) ((1 : ℝ)*rr) (16 : ℝ) ((2 : ℝ)*rr) (21 : ℝ) ((2 : ℝ)*rr) ≠ 0 := by
  have h : det3 (14 : ℝ) ((1 : ℝ)*rr) (16 : ℝ) ((2 : ℝ)*rr) (21 : ℝ) ((2 : ℝ)*rr) = (-5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_lt (by nlinarith [rr_pos])

/-- Candidate `zb69` at the corner `v = (14, √32)` on the ray `d₀ = (1/3, √32/6)`: side `6` along the ray, body clockwise of `d₀` (the residue side). -/
noncomputable def zb69 : Tri := mkTri (14 : ℝ) ((1 : ℝ)*rr) (16 : ℝ) ((2 : ℝ)*rr) (21 : ℝ) ((2 : ℝ)*rr) det_zb69

/-- **`zb69` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_zb69 :
    dist (zb69.pts 0) (zb69.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (zb69.pts 1) (zb69.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (zb69.pts 2) (zb69.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (14 : ℝ) ((1 : ℝ)*rr)) (mkPt (16 : ℝ) ((2 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq
  · show dist (mkPt (16 : ℝ) ((2 : ℝ)*rr)) (mkPt (21 : ℝ) ((2 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (21 : ℝ) ((2 : ℝ)*rr)) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq

/-- **Escape.**  `zb69`'s vertex `1` (the far end of its edge along `d₀`) lies strictly beyond the left leg. -/
theorem escape_zb69 : ¬ (zb69.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (zb69.pts 1) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  have he : zb69.pts 1 = mkPt (16 : ℝ) ((2 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_zb96 : det3 (14 : ℝ) ((1 : ℝ)*rr) (17 : ℝ) ((5/2 : ℝ)*rr) (56/3 : ℝ) ((5/3 : ℝ)*rr) ≠ 0 := by
  have h : det3 (14 : ℝ) ((1 : ℝ)*rr) (17 : ℝ) ((5/2 : ℝ)*rr) (56/3 : ℝ) ((5/3 : ℝ)*rr) = (-5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_lt (by nlinarith [rr_pos])

/-- Candidate `zb96` at the corner `v = (14, √32)` on the ray `d₀ = (1/3, √32/6)`: side `9` along the ray, body clockwise of `d₀` (the residue side). -/
noncomputable def zb96 : Tri := mkTri (14 : ℝ) ((1 : ℝ)*rr) (17 : ℝ) ((5/2 : ℝ)*rr) (56/3 : ℝ) ((5/3 : ℝ)*rr) det_zb96

/-- **`zb96` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_zb96 :
    dist (zb96.pts 0) (zb96.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (zb96.pts 1) (zb96.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (zb96.pts 2) (zb96.pts 0) ^ 2 = (36 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (14 : ℝ) ((1 : ℝ)*rr)) (mkPt (17 : ℝ) ((5/2 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((9/4 : ℝ)) * rr_sq
  · show dist (mkPt (17 : ℝ) ((5/2 : ℝ)*rr)) (mkPt (56/3 : ℝ) ((5/3 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq
  · show dist (mkPt (56/3 : ℝ) ((5/3 : ℝ)*rr)) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((4/9 : ℝ)) * rr_sq

/-- **Escape.**  `zb96`'s vertex `1` (the far end of its edge along `d₀`) lies strictly beyond the left leg. -/
theorem escape_zb96 : ¬ (zb96.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (zb96.pts 1) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  have he : zb96.pts 1 = mkPt (17 : ℝ) ((5/2 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_zg65 : det3 (14 : ℝ) ((1 : ℝ)*rr) (16 : ℝ) ((2 : ℝ)*rr) (161/9 : ℝ) ((4/9 : ℝ)*rr) ≠ 0 := by
  have h : det3 (14 : ℝ) ((1 : ℝ)*rr) (16 : ℝ) ((2 : ℝ)*rr) (161/9 : ℝ) ((4/9 : ℝ)*rr) = (-5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_lt (by nlinarith [rr_pos])

/-- Candidate `zg65` at the corner `v = (14, √32)` on the ray `d₀ = (1/3, √32/6)`: side `6` along the ray, body clockwise of `d₀` (the residue side). -/
noncomputable def zg65 : Tri := mkTri (14 : ℝ) ((1 : ℝ)*rr) (16 : ℝ) ((2 : ℝ)*rr) (161/9 : ℝ) ((4/9 : ℝ)*rr) det_zg65

/-- **`zg65` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_zg65 :
    dist (zg65.pts 0) (zg65.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (zg65.pts 1) (zg65.pts 2) ^ 2 = (81 : ℝ) ∧
    dist (zg65.pts 2) (zg65.pts 0) ^ 2 = (25 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (14 : ℝ) ((1 : ℝ)*rr)) (mkPt (16 : ℝ) ((2 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq
  · show dist (mkPt (16 : ℝ) ((2 : ℝ)*rr)) (mkPt (161/9 : ℝ) ((4/9 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((196/81 : ℝ)) * rr_sq
  · show dist (mkPt (161/9 : ℝ) ((4/9 : ℝ)*rr)) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/81 : ℝ)) * rr_sq

/-- **Escape.**  `zg65`'s vertex `1` (the far end of its edge along `d₀`) lies strictly beyond the left leg. -/
theorem escape_zg65 : ¬ (zg65.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (zg65.pts 1) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  have he : zg65.pts 1 = mkPt (16 : ℝ) ((2 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

theorem det_zg56 : det3 (14 : ℝ) ((1 : ℝ)*rr) (47/3 : ℝ) ((11/6 : ℝ)*rr) (56/3 : ℝ) ((1/3 : ℝ)*rr) ≠ 0 := by
  have h : det3 (14 : ℝ) ((1 : ℝ)*rr) (47/3 : ℝ) ((11/6 : ℝ)*rr) (56/3 : ℝ) ((1/3 : ℝ)*rr) = (-5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_lt (by nlinarith [rr_pos])

/-- Candidate `zg56` at the corner `v = (14, √32)` on the ray `d₀ = (1/3, √32/6)`: side `5` along the ray, body clockwise of `d₀` (the residue side). -/
noncomputable def zg56 : Tri := mkTri (14 : ℝ) ((1 : ℝ)*rr) (47/3 : ℝ) ((11/6 : ℝ)*rr) (56/3 : ℝ) ((1/3 : ℝ)*rr) det_zg56

/-- **`zg56` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_zg56 :
    dist (zg56.pts 0) (zg56.pts 1) ^ 2 = (25 : ℝ) ∧
    dist (zg56.pts 1) (zg56.pts 2) ^ 2 = (81 : ℝ) ∧
    dist (zg56.pts 2) (zg56.pts 0) ^ 2 = (36 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (14 : ℝ) ((1 : ℝ)*rr)) (mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq
  · show dist (mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr)) (mkPt (56/3 : ℝ) ((1/3 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((9/4 : ℝ)) * rr_sq
  · show dist (mkPt (56/3 : ℝ) ((1/3 : ℝ)*rr)) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((4/9 : ℝ)) * rr_sq

/-- **Escape.**  `zg56`'s vertex `1` (the far end of its edge along `d₀`) lies strictly beyond the left leg. -/
theorem escape_zg56 : ¬ (zg56.carrier ⊆ target63.carrier) := by
  intro h
  have hv : (zg56.pts 1) ∈ target63.carrier := h (subset_convexHull ℝ _ (Set.mem_range_self 1))
  have he : zg56.pts 1 = mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr) := rfl
  rw [he] at hv
  exact not_mem_target63_of_left (by nlinarith [rr_pos]) hv

/-- **BLOCKING LEMMA at the `Z1` run.**  At the corner `v = (14, √32)` with the ray
`d₀ = (1/3, √32/6)` (the direction of the exposed run of length `4` toward the left leg), **every**
one of the six oriented placements of a triangle congruent to `(6,5,9)` with a corner at `v` and an
edge along `d₀` on the residue side escapes the target — each through the left leg, by its vertex on
the ray.  A fact about the target alone: no placed tile is referred to. -/
theorem blocking_Z1run :
    ¬ (za59.carrier ⊆ target63.carrier) ∧
    ¬ (za95.carrier ⊆ target63.carrier) ∧
    ¬ (zb69.carrier ⊆ target63.carrier) ∧
    ¬ (zb96.carrier ⊆ target63.carrier) ∧
    ¬ (zg65.carrier ⊆ target63.carrier) ∧
    ¬ (zg56.carrier ⊆ target63.carrier) :=
  ⟨escape_za59, escape_za95, escape_zb69, escape_zb96, escape_zg65, escape_zg56⟩

/-- **The frame.**  Each candidate has vertex `0` at `v` and vertex `1` at `v + t·d₀`, `t ∈ {5,9,6,9,6,5}`. -/
theorem Z1run_frame :
    (za59.pts 0 = mkPt (14 : ℝ) ((1 : ℝ)*rr) ∧ za59.pts 1 = mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr) ∧ mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr) = mkPt ((14 : ℝ) + 5*(1/3 : ℝ)) ((1 : ℝ)*rr + 5*((1/6 : ℝ)*rr))) ∧
    (za95.pts 0 = mkPt (14 : ℝ) ((1 : ℝ)*rr) ∧ za95.pts 1 = mkPt (17 : ℝ) ((5/2 : ℝ)*rr) ∧ mkPt (17 : ℝ) ((5/2 : ℝ)*rr) = mkPt ((14 : ℝ) + 9*(1/3 : ℝ)) ((1 : ℝ)*rr + 9*((1/6 : ℝ)*rr))) ∧
    (zb69.pts 0 = mkPt (14 : ℝ) ((1 : ℝ)*rr) ∧ zb69.pts 1 = mkPt (16 : ℝ) ((2 : ℝ)*rr) ∧ mkPt (16 : ℝ) ((2 : ℝ)*rr) = mkPt ((14 : ℝ) + 6*(1/3 : ℝ)) ((1 : ℝ)*rr + 6*((1/6 : ℝ)*rr))) ∧
    (zb96.pts 0 = mkPt (14 : ℝ) ((1 : ℝ)*rr) ∧ zb96.pts 1 = mkPt (17 : ℝ) ((5/2 : ℝ)*rr) ∧ mkPt (17 : ℝ) ((5/2 : ℝ)*rr) = mkPt ((14 : ℝ) + 9*(1/3 : ℝ)) ((1 : ℝ)*rr + 9*((1/6 : ℝ)*rr))) ∧
    (zg65.pts 0 = mkPt (14 : ℝ) ((1 : ℝ)*rr) ∧ zg65.pts 1 = mkPt (16 : ℝ) ((2 : ℝ)*rr) ∧ mkPt (16 : ℝ) ((2 : ℝ)*rr) = mkPt ((14 : ℝ) + 6*(1/3 : ℝ)) ((1 : ℝ)*rr + 6*((1/6 : ℝ)*rr))) ∧
    (zg56.pts 0 = mkPt (14 : ℝ) ((1 : ℝ)*rr) ∧ zg56.pts 1 = mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr) ∧ mkPt (47/3 : ℝ) ((11/6 : ℝ)*rr) = mkPt ((14 : ℝ) + 5*(1/3 : ℝ)) ((1 : ℝ)*rr + 5*((1/6 : ℝ)*rr))) := by
  refine ⟨⟨rfl, rfl, ?_⟩, ⟨rfl, rfl, ?_⟩, ⟨rfl, rfl, ?_⟩, ⟨rfl, rfl, ?_⟩, ⟨rfl, rfl, ?_⟩, ⟨rfl, rfl, ?_⟩⟩ <;> (congr 1 <;> ring)

/-! ## 4. Non-vacuity: tiles `5` and `17` of `Z1` -/

theorem det_z1t5 : det3 (12 : ℝ) (0 : ℝ) (19 : ℝ) ((1 : ℝ)*rr) (14 : ℝ) ((1 : ℝ)*rr) ≠ 0 := by
  have h : det3 (12 : ℝ) (0 : ℝ) (19 : ℝ) ((1 : ℝ)*rr) (14 : ℝ) ((1 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- `Z1` tile `5` (from `data/witnesses/Z1_basebeta_2_3_partial19.tsv`). -/
noncomputable def z1t5 : Tri := mkTri (12 : ℝ) (0 : ℝ) (19 : ℝ) ((1 : ℝ)*rr) (14 : ℝ) ((1 : ℝ)*rr) det_z1t5

/-- **`z1t5` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_z1t5 :
    dist (z1t5.pts 0) (z1t5.pts 1) ^ 2 = (81 : ℝ) ∧
    dist (z1t5.pts 1) (z1t5.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (z1t5.pts 2) (z1t5.pts 0) ^ 2 = (36 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (12 : ℝ) (0 : ℝ)) (mkPt (19 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq
  · show dist (mkPt (19 : ℝ) ((1 : ℝ)*rr)) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (14 : ℝ) ((1 : ℝ)*rr)) (mkPt (12 : ℝ) (0 : ℝ)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1 : ℝ)) * rr_sq

/-- **`z1t5` lies inside the target.** -/
theorem inside_z1t5 : z1t5.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [z1t5, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

theorem det_z1t17 : det3 (23/3 : ℝ) ((5/6 : ℝ)*rr) (41/3 : ℝ) ((5/6 : ℝ)*rr) (46/3 : ℝ) ((5/3 : ℝ)*rr) ≠ 0 := by
  have h : det3 (23/3 : ℝ) ((5/6 : ℝ)*rr) (41/3 : ℝ) ((5/6 : ℝ)*rr) (46/3 : ℝ) ((5/3 : ℝ)*rr) = (5 : ℝ)*rr := by unfold det3; ring
  rw [h]; exact ne_of_gt (by nlinarith [rr_pos])

/-- `Z1` tile `17` (from `data/witnesses/Z1_basebeta_2_3_partial19.tsv`). -/
noncomputable def z1t17 : Tri := mkTri (23/3 : ℝ) ((5/6 : ℝ)*rr) (41/3 : ℝ) ((5/6 : ℝ)*rr) (46/3 : ℝ) ((5/3 : ℝ)*rr) det_z1t17

/-- **`z1t17` is congruent to the tile `(a,b,c) = (6,5,9)`**: its three squared side lengths,
in vertex order, are a permutation of `36, 25, 81`. -/
theorem sides_z1t17 :
    dist (z1t17.pts 0) (z1t17.pts 1) ^ 2 = (36 : ℝ) ∧
    dist (z1t17.pts 1) (z1t17.pts 2) ^ 2 = (25 : ℝ) ∧
    dist (z1t17.pts 2) (z1t17.pts 0) ^ 2 = (81 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt (23/3 : ℝ) ((5/6 : ℝ)*rr)) (mkPt (41/3 : ℝ) ((5/6 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((0 : ℝ)) * rr_sq
  · show dist (mkPt (41/3 : ℝ) ((5/6 : ℝ)*rr)) (mkPt (46/3 : ℝ) ((5/3 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq
  · show dist (mkPt (46/3 : ℝ) ((5/3 : ℝ)*rr)) (mkPt (23/3 : ℝ) ((5/6 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((25/36 : ℝ)) * rr_sq

/-- **`z1t17` lies inside the target.** -/
theorem inside_z1t17 : z1t17.carrier ⊆ target63.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k <;>
    simp only [z1t17, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;>
    exact mem_target63 (by nlinarith [rr_pos]) (by nlinarith [rr_pos]) (by nlinarith [rr_pos])

/-- **Tiles `5` and `17` have disjoint interiors**: the line through `(12,0)` and `(14, √32)` (their
common edge line) separates them. -/
theorem disj_z1t5_z1t17 : Disjoint (interior z1t5.carrier) (interior z1t17.carrier) :=
  interiors_disjoint_of_separating (lineFun (12 : ℝ) (0:ℝ) (14 : ℝ) ((1 : ℝ)*rr))
    (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
    (le_of_forall_pts_le _ (by
      intro k; fin_cases k <;>
        simp [z1t5, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
        nlinarith [rr_pos]))
    (ge_of_forall_pts_ge _ (by
      intro k; fin_cases k <;>
        simp [z1t17, mkTri_pts, mkPt_zero, mkPt_one, lineFun_apply] <;>
        nlinarith [rr_pos]))

/-- **The run.**  `v = (14, √32)` is vertex `2` of tile `5`; it lies on the edge `pts 1 → pts 2` of
tile `17` (collinear, at squared distance `1` from `pts 1` and `16` from `pts 2`), so the exposed
part of that edge — from `v` to the leg point `pts 2 = (46/3, 5√32/3)` — has length exactly `4`;
and `d₀` is its direction. -/
theorem Z1run_geometry :
    z1t5.pts 2 = mkPt (14 : ℝ) ((1 : ℝ)*rr) ∧
    z1t17.pts 2 = mkPt (46/3 : ℝ) ((5/3 : ℝ)*rr) ∧
    lineFun (41/3 : ℝ) ((5/6 : ℝ)*rr) (46/3 : ℝ) ((5/3 : ℝ)*rr) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) = 0 ∧
    dist (z1t17.pts 1) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) ^ 2 = 1 ∧
    dist (mkPt (14 : ℝ) ((1 : ℝ)*rr)) (z1t17.pts 2) ^ 2 = 16 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · simp only [lineFun_apply, mkPt_zero, mkPt_one]; ring
  · show dist (mkPt (41/3 : ℝ) ((5/6 : ℝ)*rr)) (mkPt (14 : ℝ) ((1 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((1/36 : ℝ)) * rr_sq
  · show dist (mkPt (14 : ℝ) ((1 : ℝ)*rr)) (mkPt (46/3 : ℝ) ((5/3 : ℝ)*rr)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((4/9 : ℝ)) * rr_sq

/-- **Non-vacuity.**  The configuration in which `blocking_Z1run` is invoked exists: two triangles
congruent to `(6,5,9)` (`sides_z1t5`, `sides_z1t17`), inside the target, with disjoint interiors,
with `v` a vertex of the first and on an edge of the second, that edge ending on the left leg. -/
theorem Z1run_witness :
    z1t5.carrier ⊆ target63.carrier ∧ z1t17.carrier ⊆ target63.carrier ∧
    Disjoint (interior z1t5.carrier) (interior z1t17.carrier) ∧
    z1t5.pts 2 = mkPt (14 : ℝ) ((1 : ℝ)*rr) ∧
    z1t17.pts 2 = mkPt (46/3 : ℝ) ((5/3 : ℝ)*rr) ∧
    (5/2 : ℝ)*rr*(46/3 : ℝ) - 23*((5/3 : ℝ)*rr) = 0 :=
  ⟨inside_z1t5, inside_z1t17, disj_z1t5_z1t17, rfl, rfl, legpoint_on_left_leg⟩

end Erdos634.ResidueRunZ1
