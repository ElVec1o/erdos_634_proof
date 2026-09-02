import Erdos634.CellCoord
import Erdos634.InteriorCoord

/-!
# The three geometric checks a certificate performs, as lemmas about `Tri`

Erdős #634. The certificate files (`Tiling44`, `Tiling99`, `CevianTiling63`, `PgramTiling22`, …)
are `decide`-checked in exact arithmetic over `ℤ[√15]`, and they check:

* **(C2)** each piece's three vertices lie in the closed target — three half-plane tests per vertex,
  each the sign of a `2 × 2` determinant, which is the sign of a barycentric coordinate;
* **(C3)** each *pair* of pieces has an explicit separating edge-line;
* **(C1)** each piece's squared side multiset equals the tile's.

Those are statements about numbers. This file turns each into the statement about `Tri` that
`CertBridge.ofCert` consumes, with no arithmetic in sight:

* `carrier_subset_of_pts_mem` — (C2): a triangle whose vertices lie in a convex target lies in it;
* `mem_carrier_of_combo` — the vertex test itself: nonnegative barycentric weights summing to one
  put a point in the carrier, which is what a determinant-sign check certifies;
* `interiors_disjoint_of_separating` — (C3): a separating affine functional gives disjoint
  *interiors*. This is the only one with content: a piece may touch the separating line, so one
  must know that no *interior* point lies on it, which is `exists_neg_near_of_affine_zero`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CertGeom

open Erdos634.Geometry Metric

/-- **(C2).** A triangle whose three vertices lie in the target lies in the target. -/
theorem carrier_subset_of_pts_mem {t T : Tri} (h : ∀ k, t.pts k ∈ T.carrier) :
    t.carrier ⊆ T.carrier :=
  convexHull_min (Set.range_subset_iff.mpr h) T.convex

/-- **The vertex test.** Nonnegative weights summing to one exhibit a point of the carrier — the
conclusion a determinant-sign check certifies. -/
theorem mem_carrier_of_combo (T : Tri) (x : Plane) (w : Fin 3 → ℝ)
    (hsum : w 0 + w 1 + w 2 = 1) (hnn : ∀ k, 0 ≤ w k)
    (hx : x = w 0 • T.pts 0 + w 1 • T.pts 1 + w 2 • T.pts 2) :
    x ∈ T.carrier := by
  rw [T.carrier_eq_nonneg_coord]
  intro k
  rw [Erdos634.Subdivision.Tri.coord_eq_of_combo T x w hsum hx k]
  exact hnn k

/-- **(C3).** An affine functional separating two triangles — bounded above by `c` on one and below
by `c` on the other — makes their interiors disjoint. The functional must be nonconstant; a piece
is allowed to *touch* the line, and the content of the lemma is that no interior point can. -/
theorem interiors_disjoint_of_separating {t u : Tri} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (c : ℝ) (h1 : ∀ x ∈ t.carrier, f x ≤ c) (h2 : ∀ x ∈ u.carrier, c ≤ f x) :
    Disjoint (interior t.carrier) (interior u.carrier) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hxt : x ∈ t.carrier := interior_subset hx1
  have hxu : x ∈ u.carrier := interior_subset hx2
  have hxc : f x = c := le_antisymm (h1 x hxt) (h2 x hxu)
  -- `c - f` is a nonconstant affine functional vanishing at `x`, so it is negative nearby
  set g : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane c - f with hg
  have hglin : g.linear ≠ 0 := by
    intro hcon
    apply hf
    have : (AffineMap.const ℝ Plane c).linear - f.linear = 0 := hcon
    have hzero : (AffineMap.const ℝ Plane c).linear = 0 := rfl
    rw [hzero, zero_sub, neg_eq_zero] at this
    exact this
  have hgx : g x = 0 := by simp [hg, hxc]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx1)
  obtain ⟨y, hy, hyneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hyt : y ∈ t.carrier := hball hy
  have : c < f y := by
    have hgy : g y = c - f y := rfl
    rw [hgy] at hyneg
    linarith
  exact absurd (h1 y hyt) (not_le.mpr this)

/-- **(C3), in the pairwise form `Dissection` asks for.** -/
theorem pairwise_disjoint_of_separating {N : ℕ} (tile : Fin N → Tri)
    (sep : ∀ i j, i ≠ j → ∃ (f : Plane →ᵃ[ℝ] ℝ) (_ : f.linear ≠ 0) (c : ℝ),
      (∀ x ∈ (tile i).carrier, f x ≤ c) ∧ (∀ x ∈ (tile j).carrier, c ≤ f x)) :
    Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier) := by
  intro i j hij
  obtain ⟨f, hf, c, h1, h2⟩ := sep i j hij
  exact interiors_disjoint_of_separating f hf c h1 h2

end Erdos634.CertGeom
