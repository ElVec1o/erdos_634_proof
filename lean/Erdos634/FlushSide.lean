import Erdos634.Dissection
import Mathlib.Analysis.Convex.Between

/-!
# The placement step: a tile side meeting a line in positive length lies wholly on it

Erdős #634.  Both remaining conditionals — Beeson's Theorem 2 and `MidTriangleE1`'s exclusion of
the middle triangle — consume the same geometric hypothesis: *the tile sides lying on a boundary
segment are **whole** sides, so their lengths are drawn from `{a, b, c}` and partition the
segment's length.*  `Contiguity` and `LineParam.lineChain_covers_Icc` already supply the partition
half.  The half that was missing is the "whole side" half, and it is this file.

The fact is elementary and completely general: a linear functional is affine along a segment, so if
it takes the value `c` at two distinct points of the segment, it is constant `= c` on the whole
segment — in particular at both endpoints.  "Positive length part of a side lies on the line" gives
two distinct such points, hence the whole side lies on the line.

Consequence for a tiling: a tile whose side has a positive-length part on a boundary segment
contributes to that segment **the full side**, of length `dist (T.pts j) (T.pts k)` — which for a
`CongruentDissection` is one of the tile's three side lengths.  That is exactly what upgrades an
edge-length bookkeeping identity (`ua + vb + wc = length`) from a hypothesis to a theorem.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FlushSide

open Erdos634.Geometry

/-- A linear functional is affine along `lineMap`: `f (lineMap p q t) = f p + t • (f q - f p)`. -/
theorem map_lineMap (f : Plane →ₗ[ℝ] ℝ) (p q : Plane) (t : ℝ) :
    f (AffineMap.lineMap p q t) = f p + t * (f q - f p) := by
  simp [AffineMap.lineMap_apply, map_add, map_smul, map_sub, smul_eq_mul]
  ring

/-- **Two distinct level points force the whole line.**  If `f` takes the value `c` at
`lineMap p q s` and `lineMap p q t` for `s ≠ t`, then `f p = c` and `f q = c`. -/
theorem endpoints_eq_of_two_level {f : Plane →ₗ[ℝ] ℝ} {p q : Plane} {c s t : ℝ} (hst : s ≠ t)
    (hs : f (AffineMap.lineMap p q s) = c) (ht : f (AffineMap.lineMap p q t) = c) :
    f p = c ∧ f q = c := by
  rw [map_lineMap] at hs ht
  have hd : f q - f p = 0 := by
    have : (s - t) * (f q - f p) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith : s = t) hst
    · exact h
  have hfp : f p = c := by rw [hd] at hs; linarith
  exact ⟨hfp, by linarith⟩

/-- **The whole side lies on the line.**  With both endpoints at level `c`, every point of the
segment is at level `c`. -/
theorem segment_subset_level {f : Plane →ₗ[ℝ] ℝ} {p q : Plane} {c : ℝ}
    (hp : f p = c) (hq : f q = c) : segment ℝ p q ⊆ {y | f y = c} := by
  rintro y ⟨u, v, hu, hv, huv, rfl⟩
  simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul, hp, hq]
  linear_combination c * huv

/-- **The placement step, packaged.**  If a side `pq` of a tile has two distinct points on the line
`{f = c}` — which is what "a positive-length part of the side lies on the line" provides — then the
side lies wholly on the line, and its contribution to the line is the full segment `[p, q]`, of
length `dist p q`. -/
theorem whole_side_of_two_level {f : Plane →ₗ[ℝ] ℝ} {p q : Plane} {c : ℝ}
    {x y : Plane} (hx : x ∈ segment ℝ p q) (hy : y ∈ segment ℝ p q) (hxy : x ≠ y)
    (hfx : f x = c) (hfy : f y = c) (hpq : p ≠ q) :
    segment ℝ p q ⊆ {y | f y = c} := by
  obtain ⟨s, _, rfl⟩ := (segment_eq_image_lineMap ℝ p q ▸ hx : x ∈ _)
  obtain ⟨t, _, rfl⟩ := (segment_eq_image_lineMap ℝ p q ▸ hy : y ∈ _)
  have hst : s ≠ t := fun h => hxy (by rw [h])
  obtain ⟨hp, hq⟩ := endpoints_eq_of_two_level hst hfx hfy
  exact segment_subset_level hp hq

/-- The two-distinct-points hypothesis is satisfiable and the conclusion is not vacuous: a side
already on the line satisfies it. -/
theorem whole_side_witness (f : Plane →ₗ[ℝ] ℝ) (p q : Plane) (c : ℝ)
    (hp : f p = c) (hq : f q = c) : segment ℝ p q ⊆ {y | f y = c} :=
  segment_subset_level hp hq

end Erdos634.FlushSide
