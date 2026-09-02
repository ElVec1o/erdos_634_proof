import Erdos634.CellCoord
import Erdos634.InteriorCoord
import Erdos634.AreaDet

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

/-! ## The separating line a certificate names

A certificate separates two pieces by an *edge*: it names two points `P ≠ Q` and checks the sign of
`cross P Q v` at the six vertices. `lineFun` is that cross product as an affine functional of `v`,
which is what `interiors_disjoint_of_separating` consumes. -/

/-- The signed area functional `v ↦ det(Q - P, v - P)`, as an affine map. -/
noncomputable def lineFun (px py qx qy : ℝ) : Plane →ᵃ[ℝ] ℝ where
  toFun v := (qx - px) * (v 1 - py) - (v 0 - px) * (qy - py)
  linear :=
    { toFun := fun w => (qx - px) * w 1 - w 0 * (qy - py)
      map_add' := by intro w z; simp only [PiLp.add_apply]; ring
      map_smul' := by intro c w; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_vadd' := by
    intro v w
    simp only [vadd_eq_add, PiLp.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring

@[simp] theorem lineFun_apply (px py qx qy : ℝ) (v : Plane) :
    lineFun px py qx qy v = (qx - px) * (v 1 - py) - (v 0 - px) * (qy - py) := rfl

/-- **The functional is nonconstant as soon as the two points differ.** -/
theorem lineFun_linear_ne_zero {px py qx qy : ℝ} (h : px ≠ qx ∨ py ≠ qy) :
    (lineFun px py qx qy).linear ≠ 0 := by
  intro hcon
  set e0 : Plane := EuclideanSpace.single 0 (1 : ℝ) with he0
  set e1 : Plane := EuclideanSpace.single 1 (1 : ℝ) with he1
  have hb00 : e0 0 = 1 := by simp [he0]
  have hb01 : e0 1 = 0 := by simp [he0]
  have hb10 : e1 0 = 0 := by simp [he1]
  have hb11 : e1 1 = 1 := by simp [he1]
  have h0 : (lineFun px py qx qy).linear e0 = 0 := by rw [hcon]; rfl
  have h1 : (lineFun px py qx qy).linear e1 = 0 := by rw [hcon]; rfl
  have eq0 : (qx - px) * e0 1 - e0 0 * (qy - py) = 0 := h0
  have eq1 : (qx - px) * e1 1 - e1 0 * (qy - py) = 0 := h1
  rw [hb00, hb01] at eq0
  rw [hb10, hb11] at eq1
  rcases h with h | h
  · exact h (by linarith)
  · exact h (by linarith)

end Erdos634.CertGeom
