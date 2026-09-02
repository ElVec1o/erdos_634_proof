import Erdos634.Tiling44
import Erdos634.Z15Real
import Erdos634.CertGeom

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

/-- **Every one of the 44 pieces is positively oriented** — `decide` on the whole list, ~15s to
build, not per-piece: this is the scaling probe `private/VERIFY_PLAN.md` asked for, answered. It
means the indexed-`∀`-over-`Fin 44` shape (rather than 44 separate named theorems) is the right
approach for (C1)/(C2), and there is no elaboration-cost obstruction at this level. -/
theorem all_pieces_pos :
    ∀ t ∈ Tiling44.tiles,
      zpos (zcross (toZPt (Tiling44.t1 t)) (toZPt (Tiling44.t2 t)) (toZPt (Tiling44.t3 t)))
        = true := by
  decide

/-- **Every piece, as a real `Tri`**, uniformly — the general form `thm:44`'s data entry needs,
combining `all_pieces_pos` with `det3_eq_toR_cross` instead of writing 44 separate constructions. -/
noncomputable def pieceTri {t : Tiling44.Tri} (ht : t ∈ Tiling44.tiles) : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (Tiling44.t1 t)))) (toR (zy (toZPt (Tiling44.t1 t))))
    (toR (zx (toZPt (Tiling44.t2 t)))) (toR (zy (toZPt (Tiling44.t2 t))))
    (toR (zx (toZPt (Tiling44.t3 t)))) (toR (zy (toZPt (Tiling44.t3 t))))
    (by
      rw [det3_eq_toR_cross]
      exact (toR_pos (all_pieces_pos t ht)).ne')

/-- **The `lineFun` of a certificate edge is nonconstant**, for two *concrete* endpoints `P ≠ Q`
whose real coordinates differ — resolved via `Z15Real.toR_ne_zero_of_sq_ne` rather than injectivity
of `toR` (which this project deliberately never proves). `hx`/`hy` are the decidable `ℤ[√15]`
side conditions (`zx Q - zx P` resp. `zy Q - zy P` squared-nonequal to `15 * (other coord)²`); one
of the two always holds for a genuine edge, matching whichever coordinate actually differs. -/
theorem lineFun_ne_zero_of_sq_ne {P Q : ZPt}
    (h : (zsub (zx P) (zx Q)).1 ^ 2 ≠ 15 * (zsub (zx P) (zx Q)).2 ^ 2
       ∨ (zsub (zy P) (zy Q)).1 ^ 2 ≠ 15 * (zsub (zy P) (zy Q)).2 ^ 2) :
    (Erdos634.CertGeom.lineFun (toR (zx P)) (toR (zy P)) (toR (zx Q)) (toR (zy Q))).linear ≠ 0 := by
  apply Erdos634.CertGeom.lineFun_linear_ne_zero
  rcases h with h | h
  · exact Or.inl (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))
  · exact Or.inr (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))

end Erdos634.Tiling44Bridge
