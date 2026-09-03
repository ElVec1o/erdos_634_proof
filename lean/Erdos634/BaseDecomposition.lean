import Erdos634.BaseWalkGeneral
import Erdos634.CChord

/-!
# The base decomposition, for any real base-β dissection

Erdős #634. `base_walk_pos_general` gives the real walk equation with `Rc ≥ 1` for any side of any
real base-β dissection. This file casts that to the `ℤ`-typed arithmetic `CChord.lean` already has
(`base_dichotomy_thick`, itself composing the already-VERIFIED `base_trichotomy` with the γ-trap's
`z ≥ 1`), giving the base's decomposition as a genuine consequence for a real dissection — not a
hand-built certificate, and not merely the abstract arithmetic alone.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.SideWall Erdos634.TilePlacement
open Erdos634.SideWalk

/-- **The γ-trap's walk equation, as `ℤ` arithmetic**, given the target's known integer side
lengths. Casts `base_walk_pos_general`'s real conclusion directly. -/
theorem base_walk_pos_int {N : ℕ} (hN : 0 < N) (D : CongruentDissection N)
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
      (D.target.pts (k + 1 + 2)) = 3 * α)
    (e0 f0 L0 : ℕ)
    (hA : sideOpp D.model 0 = ((e0 * f0 : ℕ) : ℝ))
    (hB : sideOpp D.model 1 = ((f0 * f0 - e0 * e0 : ℕ) : ℝ))
    (hC : sideOpp D.model 2 = ((f0 * f0 : ℕ) : ℝ))
    (hLen : dist (D.target.pts k) (D.target.pts (k+1)) = ((L0 : ℕ) : ℝ)) :
    ∃ x y z : ℕ, 1 ≤ z ∧ x * (e0 * f0) + y * (f0 * f0 - e0 * e0) + z * (f0 * f0) = L0 := by
  obtain ⟨Pc, Qc, Rc, hRpos, heq⟩ :=
    base_walk_pos_general hN D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr
      hscalene hα' hβ' hγ' k hdirab hcornerbase hcornerapex
  refine ⟨Pc, Qc, Rc, hRpos, ?_⟩
  have hcast : ((Pc * (e0 * f0) + Qc * (f0 * f0 - e0 * e0) + Rc * (f0 * f0) : ℕ) : ℝ)
      = (L0 : ℝ) := by
    push_cast
    rw [hA, hB, hC] at heq
    push_cast at heq
    linarith
  exact_mod_cast hcast

/-- **`lem:basedi`, as a conditional on any real base-β dissection at a separated member.** Given
a `CongruentDissection` whose model has the base-β `(e,f)` side lengths `ef, f²-e², f²` and whose
target's side `k` has the base's own known length `e(3f²-e²)`, at a separated member
(`f²>2ef+e²`) the base admits exactly the two decompositions `(0,e,2e)` or `(f,e,e)` — the γ-trap's
`z≥1` combined with the already-VERIFIED `base_trichotomy`. -/
theorem base_decomposition_general {N : ℕ} (hN : 0 < N) (D : CongruentDissection N)
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
      (D.target.pts (k + 1 + 2)) = 3 * α)
    (e0 f0 : ℕ) (he0 : 1 ≤ e0) (hef0 : e0 < f0) (hco : Nat.Coprime e0 f0)
    (hsep : 2 * e0 * f0 + e0 * e0 < f0 * f0)
    (hA : sideOpp D.model 0 = ((e0 * f0 : ℕ) : ℝ))
    (hB : sideOpp D.model 1 = ((f0 * f0 - e0 * e0 : ℕ) : ℝ))
    (hC : sideOpp D.model 2 = ((f0 * f0 : ℕ) : ℝ))
    (hLen : dist (D.target.pts k) (D.target.pts (k+1))
      = ((e0 * (3 * (f0 * f0) - e0 * e0) : ℕ) : ℝ)) :
    ∃ x y z : ℕ, (x = 0 ∧ y = e0 ∧ z = 2 * e0) ∨ (x = f0 ∧ y = e0 ∧ z = e0) := by
  obtain ⟨x, y, z, hz, heq⟩ := base_walk_pos_int hN D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr hscalene hα' hβ' hγ' k hdirab hcornerbase hcornerapex
    e0 f0 (e0 * (3 * (f0*f0) - e0*e0)) hA hB hC hLen
  exact ⟨x, y, z, Erdos634.CChord.base_dichotomy_thick he0 hef0 hco hsep hz heq⟩
