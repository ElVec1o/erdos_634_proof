import Erdos634.WallThird
import Erdos634.GammaTrap
import Erdos634.SideWalk

/-!
# The γ-trap's walk equation, assembled for any real base-β dissection

Erdős #634. `GammaTrap.congruentDissection_gammatrap` gives a `c`-edge witness on any side of any
real `CongruentDissection` matching a base-β corner's angle structure, but stops there — it never
composed with `SideWalk.side_walk_of_dissection` to turn that witness into an actual walk-count
positivity fact. Now that `WallDir`/`WallThird` make every one of `side_walk_of_dissection`'s
hypotheses (`hker`, `hwall`, `hbase`, `hline`, `hface`, `hiso`, `hthird`) available generically via
`wallFun`/`dirFun`, that composition is immediate: `base_walk_pos_general` gives, for *any* side of
*any* such dissection, the real walk equation with `Rc ≥ 1` — no coordinates, no fixed target, no
per-target certificate.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.SideWall Erdos634.TilePlacement
open Erdos634.SideWalk

/-- `dirFun`'s linear part is calibrated the same way `dirFun` itself is: the difference of its
values at two points on a wall line equals the difference of the affine `dirFun`'s own values
there (since `dirFun`'s constant part cancels in any difference). Lets `hiso_wallFun` serve
`side_walk_of_dissection`'s `dir`-as-linear-map convention directly. -/
theorem hiso_wallFun' (T : Tri) (k : Fin 3) (p q : Plane)
    (hp : wallFun T k p = 0) (hq : wallFun T k q = 0) :
    dist p q = |(dirFun T k).linear p - (dirFun T k).linear q| := by
  rw [hiso_wallFun T k hp hq]
  congr 1
  have h1 : (dirFun T k).linear (p -ᵥ q) = (dirFun T k) p -ᵥ (dirFun T k) q :=
    AffineMap.linearMap_vsub _ p q
  have h2 : (dirFun T k).linear (p -ᵥ q) = (dirFun T k).linear p - (dirFun T k).linear q := by
    rw [vsub_eq_sub]; exact map_sub _ p q
  rw [← h2, h1, vsub_eq_sub]

/-- **The `γ`-trap's real walk equation, for any real base-β dissection.** Given a
`CongruentDissection` whose model and target match a base-β corner's known angle structure at
side `k`, that side's walk carries `Rc ≥ 1` (the `γ`-trap) with the real walk equation
`dist a b = Pc·s₀ + Qc·s₁ + Rc·s₂`. No coordinates: `g`/`dir` are `wallFun`/`dirFun`, and every
one of `side_walk_of_dissection`'s geometric hypotheses is discharged generically. -/
theorem base_walk_pos_general {N : ℕ} (hN : 0 < N) (D : CongruentDissection N)
    (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hdirab : (dirFun D.target k).linear (D.target.pts k)
      ≤ (dirFun D.target k).linear (D.target.pts (k + 1)))
    (hcornerbase : cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = 3 * α) :
    ∃ Pc Qc Rc : ℕ, 1 ≤ Rc ∧
      dist (D.target.pts k) (D.target.pts (k+1))
        = Pc * sideOpp D.model 0 + Qc * sideOpp D.model 1 + Rc * sideOpp D.model 2 := by
  have hne : k ≠ k + 1 := by fin_cases k <;> decide
  have hab : D.target.pts k ≠ D.target.pts (k+1) := Erdos634.TilePlacement.pts_ne D.target hne
  have hthirdD : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0 :=
    hthird_general D.toDissection (wallFun D.target k) 0 (wallFun_linear_ne_zero D.target k)
      (fun y hy => by simpa using wallFun_le D.target k hy)
  have hgtrap := Erdos634.Geometry.Dissection.congruentDissection_gammatrap hN D α β γ hαβ hαγ
    hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hscalene hα' hβ' hγ' k
    (dirFun D.target k).linear (hker_wallFun D.target k) hdirab hthirdD hcornerbase hcornerapex
  obtain ⟨p0, hp0, hp0len⟩ := hgtrap
  exact side_walk_pos2_of_dissection D (wallFun D.target k) 0 (dirFun D.target k).linear
    (hker_wallFun D.target k) (fun y hy => wallFun_le D.target k hy) (D.target.pts k)
    (D.target.pts (k+1)) hab hdirab (edge_subset_frontier D.target k)
    (fun y hy => wallFun_eq_zero D.target k hy) (hface_wallFun D.target k) hthirdD
    (hiso_wallFun' D.target k)
    ⟨hscalene 0 1 (by decide), hscalene 0 2 (by decide), hscalene 1 2 (by decide)⟩
    hN p0 hp0 hp0len
