import Erdos634.Tiling44WallFinal
import Erdos634.SideWalk
import Erdos634.Tiling44Scalene

/-!
# `side_walk_of_dissection`, instantiated for `Tiling44Bridge.dissection`'s equal side

Erdős #634. The first real instantiation anywhere in the corpus of
`SideWalk.side_walk_of_dissection` — all seven of its named hypotheses (`hker`, `hwall`, `hbase`,
`hline`, `hface`, `hthird`, `hiso`) plus `hscalene` are discharged for the equal side of
`Tiling44Bridge.dissection`'s target (from `(176,0)` to the apex `(88,24√15)`), giving a genuine
walk equation for a real dissection's side, not merely the abstract `ChainWalk.chain_walk` shape.

Toward `lem:ccornerside`: this gives `∃ Pc Qc Rc, dist = Pc·s₀+Qc·s₁+Rc·s₂`, but not yet `Pc>0`
(or whichever count corresponds to the corner tile's forced `a`-edge) — that is the remaining step.

Axiom-clean; no `sorry`.
-/

open Erdos634.CertCoord Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge
open Erdos634.SideWalk Erdos634.TilePlacement

/-- **The equal side's walk equation.** `dist (pts 1) (pts 2) = 128` is a sum of the model's three
side lengths (`sideOpp 0,1,2`) with natural-number multiplicities — the first real, concrete
instance of a dissection side's walk equation in this project. -/
theorem equal_side_walk :
    ∃ Pc Qc Rc : ℕ,
      dist (targetTri.pts 1) (targetTri.pts 2)
        = Pc * sideOpp dissection.model 0 + Qc * sideOpp dissection.model 1
          + Rc * sideOpp dissection.model 2 := by
  have hdirab : dirWall (targetTri.pts 1) ≤ dirWall (targetTri.pts 2) := by
    rw [tiling44_targetTri_pts1, tiling44_targetTri_pts2, dirWall_mkPt, dirWall_mkPt]
    nlinarith [Real.sqrt_nonneg (15:ℝ), Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num)]
  have hab : targetTri.pts 1 ≠ targetTri.pts 2 := by
    rw [tiling44_targetTri_pts1, tiling44_targetTri_pts2]
    intro h
    have := congrArg (fun p => xFun p) h
    simp [xFun_mkPt] at this
  have hkerl : ∀ v : Plane, gWallAff.linear v = 0 → dirWall v = 0 → v = 0 := hker_wall
  exact side_walk_of_dissection dissection gWallAff (4224 * Real.sqrt 15) dirWall
    hkerl hwall_wall (targetTri.pts 1) (targetTri.pts 2) hab hdirab
    hbase_wall hline_wall hface_wall hthird_wall hiso_wall tiling44_model_scalene
    (by
      show 0 < Tiling44.tiles.length
      decide)
