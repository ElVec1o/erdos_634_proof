import Erdos634.PgramTiling22
import Erdos634.Z15Real
import Erdos634.CertGeom
import Erdos634.SssCongruent
import Erdos634.ConvexCover
import Erdos634.AreaDet

/-!
# `PgramTiling22`, toward a genuine covering statement of the unit parallelogram

Erdős #634. `lem:pgram`/`prop:widecol`'s recorded blocker is "the general parallelogram is a
region with no Lean notion of dissection" — `Dissection`'s `target` field is a `Tri`, so a
parallelogram target cannot literally be packaged as one. But nothing in `ConvexCover`'s actual
*proof* is triangle-specific: `Tri.isCompact`, `.nullMeasurableSet`, `.volume_frontier`,
`.interior_nonempty` all come from generic facts (`Set.finite_range`, `Convex.addHaar_frontier`,
`Convex.interior_nonempty_iff_affineSpan_eq_top`) that hold for the convex hull of *any* finite
point set with full affine span — not just three points. This file builds that generic base for
the specific unit-parallelogram target `(q1,q2,q3,q4)`, as a first step toward a real covering
statement (not yet a `Dissection`, since that type doesn't fit a 4-gon target — the eventual
statement will be a bespoke pointwise-covering `Prop`, built the same way `ConvexCover` was).

**Not a paper-row flip**: this is the target-region groundwork only. The covering statement
itself, the per-piece (C1)-(C4) transfer, and the containment test (needs a diagonal split into
two triangles, since `CertCoord.mem_carrier_of_dets` is a 3-vertex barycentric test) are not done.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PgramTiling22Bridge

open Erdos634.Z15Real Erdos634.Geometry

def toZPt (p : PgramTiling22.Pt) : ZPt := p

/-- The parallelogram's four real vertices. -/
noncomputable def v1 : Plane := Erdos634.CertCoord.mkPt (toR (zx (toZPt PgramTiling22.q1)))
  (toR (zy (toZPt PgramTiling22.q1)))
noncomputable def v2 : Plane := Erdos634.CertCoord.mkPt (toR (zx (toZPt PgramTiling22.q2)))
  (toR (zy (toZPt PgramTiling22.q2)))
noncomputable def v3 : Plane := Erdos634.CertCoord.mkPt (toR (zx (toZPt PgramTiling22.q3)))
  (toR (zy (toZPt PgramTiling22.q3)))
noncomputable def v4 : Plane := Erdos634.CertCoord.mkPt (toR (zx (toZPt PgramTiling22.q4)))
  (toR (zy (toZPt PgramTiling22.q4)))

/-- The parallelogram, as the convex hull of its four vertices. -/
noncomputable def carrier : Set Plane := convexHull ℝ {v1, v2, v3, v4}

theorem convex : Convex ℝ carrier := convex_convexHull ℝ _

theorem isCompact : IsCompact carrier :=
  (Set.toFinite ({v1, v2, v3, v4} : Set Plane)).isCompact_convexHull ℝ

theorem measurableSet : MeasurableSet carrier := isCompact.measurableSet

theorem nullMeasurableSet : MeasureTheory.NullMeasurableSet carrier MeasureTheory.volume :=
  measurableSet.nullMeasurableSet

theorem volume_frontier : MeasureTheory.volume (frontier carrier) = 0 :=
  convex.addHaar_frontier MeasureTheory.volume

/-- **Non-degeneracy**: `q1, q2, q3` are affinely independent (a nonzero determinant, `decide`d in
`ℤ[√15]` the same way a triangle's is), so their affine span is already the whole plane. -/
theorem affineIndependent_123 :
    AffineIndependent ℝ (![v1, v2, v3] : Fin 3 → Plane) := by
  apply (affineIndependent_iff_not_collinear_of_ne
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)).mpr
  apply Erdos634.CertCoord.not_collinear_of_det
  show Erdos634.CertCoord.det3 (toR (zx (toZPt PgramTiling22.q1))) (toR (zy (toZPt PgramTiling22.q1)))
    (toR (zx (toZPt PgramTiling22.q2))) (toR (zy (toZPt PgramTiling22.q2)))
    (toR (zx (toZPt PgramTiling22.q3))) (toR (zy (toZPt PgramTiling22.q3))) ≠ 0
  rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt PgramTiling22.q1))) (toR (zy (toZPt PgramTiling22.q1)))
      (toR (zx (toZPt PgramTiling22.q2))) (toR (zy (toZPt PgramTiling22.q2)))
      (toR (zx (toZPt PgramTiling22.q3))) (toR (zy (toZPt PgramTiling22.q3)))
    = toR (zcross (toZPt PgramTiling22.q1) (toZPt PgramTiling22.q2) (toZPt PgramTiling22.q3))
    from toR_zcross _ _ _]
  exact toR_ne_zero_of_sq_ne (by decide)

/-- **The affine span of the parallelogram's carrier is the whole plane** — via three of its four
vertices being affinely independent, so their span already fills `Plane`. -/
theorem affineSpan_eq_top : affineSpan ℝ carrier = ⊤ := by
  have h : affineSpan ℝ carrier = affineSpan ℝ ({v1, v2, v3, v4} : Set Plane) :=
    affineSpan_convexHull _
  rw [h]
  have h3 : affineSpan ℝ (Set.range (![v1, v2, v3] : Fin 3 → Plane)) = ⊤ :=
    affineIndependent_123.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
  refine top_unique ?_
  rw [← h3]
  apply affineSpan_mono
  intro x hx
  simp only [Set.mem_range] at hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i <;> simp

theorem interior_nonempty : (interior carrier).Nonempty :=
  convex.interior_nonempty_iff_affineSpan_eq_top.mpr affineSpan_eq_top

theorem volume_ne_top : MeasureTheory.volume carrier ≠ ⊤ := isCompact.measure_lt_top.ne

end Erdos634.PgramTiling22Bridge
