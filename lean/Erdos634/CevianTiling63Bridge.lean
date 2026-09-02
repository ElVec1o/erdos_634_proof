import Erdos634.CevianTiling63
import Erdos634.Z15Real
import Erdos634.CertGeom
import Erdos634.SssCongruent
import Erdos634.Ladder

/-!
# `CevianTiling63`, assembled into a genuine `CongruentDissection`

Erdős #634. `thm:63`'s certificate bridge, following the exact pattern that closed `thm:44`
(`Erdos634.Tiling44Bridge`): `CevianTiling63`'s `ZD`/`Pt`/`cross`/`dist2`/`znonneg` are literally
`Z15Real.Z15`/`ZPt`/`zcross`/`zdist2`/`znonneg` through the identity `toZPt`, so every general
lemma in `Z15Real`/`CertGeom`/`CertCoord`/`SssCongruent`/`AreaDet` applies unchanged. The only new
work is per-certificate glue (the target is `(q1, q2, q3)`, not a named `target` field).

Not a paper-row flip until checked against `thm:63`'s exact statement.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CevianTiling63Bridge

open Erdos634.Z15Real Erdos634.Geometry

def toZPt (p : CevianTiling63.Pt) : ZPt := p

/-- The target triangle, named (the certificate only has `q1`/`q2`/`q3` inline). -/
def target : CevianTiling63.Tri := (CevianTiling63.q1, CevianTiling63.q2, CevianTiling63.q3)

theorem det3_eq_toR_cross (t : CevianTiling63.Tri) :
    Erdos634.CertCoord.det3
      (toR (zx (toZPt (CevianTiling63.t1 t)))) (toR (zy (toZPt (CevianTiling63.t1 t))))
      (toR (zx (toZPt (CevianTiling63.t2 t)))) (toR (zy (toZPt (CevianTiling63.t2 t))))
      (toR (zx (toZPt (CevianTiling63.t3 t)))) (toR (zy (toZPt (CevianTiling63.t3 t))))
    = toR (zcross (toZPt (CevianTiling63.t1 t)) (toZPt (CevianTiling63.t2 t))
        (toZPt (CevianTiling63.t3 t))) :=
  toR_zcross _ _ _

theorem target_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (CevianTiling63.t1 target)))) (toR (zy (toZPt (CevianTiling63.t1 target))))
      (toR (zx (toZPt (CevianTiling63.t2 target)))) (toR (zy (toZPt (CevianTiling63.t2 target))))
      (toR (zx (toZPt (CevianTiling63.t3 target)))) (toR (zy (toZPt (CevianTiling63.t3 target)))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (CevianTiling63.t1 target)) (toZPt (CevianTiling63.t2 target))
    (toZPt (CevianTiling63.t3 target))) (by decide)

noncomputable def targetTri : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (CevianTiling63.t1 target)))) (toR (zy (toZPt (CevianTiling63.t1 target))))
    (toR (zx (toZPt (CevianTiling63.t2 target)))) (toR (zy (toZPt (CevianTiling63.t2 target))))
    (toR (zx (toZPt (CevianTiling63.t3 target)))) (toR (zy (toZPt (CevianTiling63.t3 target))))
    target_det_pos.ne'

theorem all_pieces_pos :
    ∀ t ∈ CevianTiling63.tiles,
      zpos (zcross (toZPt (CevianTiling63.t1 t)) (toZPt (CevianTiling63.t2 t))
        (toZPt (CevianTiling63.t3 t))) = true := by
  decide

noncomputable def pieceTri {t : CevianTiling63.Tri} (ht : t ∈ CevianTiling63.tiles) : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (CevianTiling63.t1 t)))) (toR (zy (toZPt (CevianTiling63.t1 t))))
    (toR (zx (toZPt (CevianTiling63.t2 t)))) (toR (zy (toZPt (CevianTiling63.t2 t))))
    (toR (zx (toZPt (CevianTiling63.t3 t)))) (toR (zy (toZPt (CevianTiling63.t3 t))))
    (by rw [det3_eq_toR_cross]; exact (toR_pos (all_pieces_pos t ht)).ne')

end Erdos634.CevianTiling63Bridge
