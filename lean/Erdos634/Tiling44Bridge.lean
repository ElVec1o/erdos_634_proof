import Erdos634.Tiling44
import Erdos634.Z15Real

/-!
# Instantiating `Tiling44`'s target and first piece as real `Tri` objects

Erdős #634. The per-tiling data-entry work `private/VERIFY_PLAN.md` records: `Tiling44`'s
certificate checks (C1)–(C4) over `ℤ[√15]`, and `Z15Real.toPlanePt`/`zcross`/`toR_zcross` are the
bridge from those checks to `CertCoord`/`CertGeom`. This file is the first end-to-end test of that
bridge — the target triangle and the certificate's first piece, both built as genuine `Tri`
objects with their determinant-positivity hypothesis discharged by `decide` + `toR_zcross`, before
scaling the same pattern to all 44 pieces.

Not a paper-row flip: this is one target and one of 44 pieces, not the whole certificate.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Tiling44Bridge

open Erdos634.Z15Real Erdos634.Geometry

/-- A `Tiling44.Pt` read as a `Z15Real.ZPt` — the same underlying type. -/
def toZPt (p : Tiling44.Pt) : ZPt := p

/-- **The real determinant of a `Tiling44.Tri`'s three vertices**, transferred from its `ℤ[√15]`
cross product. -/
theorem det3_eq_toR_cross (t : Tiling44.Tri) :
    Erdos634.CertCoord.det3
      (toR (zx (toZPt (Tiling44.t1 t)))) (toR (zy (toZPt (Tiling44.t1 t))))
      (toR (zx (toZPt (Tiling44.t2 t)))) (toR (zy (toZPt (Tiling44.t2 t))))
      (toR (zx (toZPt (Tiling44.t3 t)))) (toR (zy (toZPt (Tiling44.t3 t))))
    = toR (zcross (toZPt (Tiling44.t1 t)) (toZPt (Tiling44.t2 t)) (toZPt (Tiling44.t3 t))) :=
  toR_zcross _ _ _

/-- **The target's determinant is `4224√15`**, positive. -/
theorem target_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (Tiling44.t1 Tiling44.target))))
      (toR (zy (toZPt (Tiling44.t1 Tiling44.target))))
      (toR (zx (toZPt (Tiling44.t2 Tiling44.target))))
      (toR (zy (toZPt (Tiling44.t2 Tiling44.target))))
      (toR (zx (toZPt (Tiling44.t3 Tiling44.target))))
      (toR (zy (toZPt (Tiling44.t3 Tiling44.target)))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (Tiling44.t1 Tiling44.target))
    (toZPt (Tiling44.t2 Tiling44.target)) (toZPt (Tiling44.t3 Tiling44.target))) (by decide)

/-- **The target, as a real `Tri`.** -/
noncomputable def targetTri : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (Tiling44.t1 Tiling44.target))))
    (toR (zy (toZPt (Tiling44.t1 Tiling44.target))))
    (toR (zx (toZPt (Tiling44.t2 Tiling44.target))))
    (toR (zy (toZPt (Tiling44.t2 Tiling44.target))))
    (toR (zx (toZPt (Tiling44.t3 Tiling44.target))))
    (toR (zy (toZPt (Tiling44.t3 Tiling44.target))))
    target_det_pos.ne'

/-- **The first piece's determinant is `48√15`**, positive — a smaller instance of the same
computation, confirming the pattern generalizes piece-by-piece. -/
theorem piece0_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (Tiling44.t1 (Tiling44.tiles.headI)))))
      (toR (zy (toZPt (Tiling44.t1 (Tiling44.tiles.headI)))))
      (toR (zx (toZPt (Tiling44.t2 (Tiling44.tiles.headI)))))
      (toR (zy (toZPt (Tiling44.t2 (Tiling44.tiles.headI)))))
      (toR (zx (toZPt (Tiling44.t3 (Tiling44.tiles.headI)))))
      (toR (zy (toZPt (Tiling44.t3 (Tiling44.tiles.headI))))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (Tiling44.t1 (Tiling44.tiles.headI)))
    (toZPt (Tiling44.t2 (Tiling44.tiles.headI))) (toZPt (Tiling44.t3 (Tiling44.tiles.headI))))
    (by decide)

end Erdos634.Tiling44Bridge
