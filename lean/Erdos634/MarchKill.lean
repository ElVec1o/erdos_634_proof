import Erdos634.MarchOverlap
import Erdos634.MarchCoords

/-!
# The `BG → GB` transition dies in a dissection

The assembly of the three pieces, with nothing left between them:

* `MarchCoords.bg_then_gb_straddles` — the sign facts (arithmetic);
* `MarchCoords.vertical_in_bg_gb_wedges` — the vertical solves both coefficient systems (scalar);
* `MarchOverlap.Dissection.wedge_disjoint_combo` — a common in-wedge direction is fatal (geometry).

The theorem takes the placed configuration through **component hypotheses**: the two tiles share
the junction vertex, tile 1's edges there have components `(-f, 0)` and `(dBG f - f, h)` (a `BG`
tile seen from its right base corner), tile 2's have `(f, 0)` and `(dGB f, h)` (a `GB` tile seen
from its left base corner).  Conclusion: `False`.  So in any dissection, a `BG` `a`-tile is never
followed along the run by a `GB` one — the content of `prop:orientmono`'s hard direction, at one
junction, from coordinates.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchKill

open Erdos634.Geometry Erdos634.MarchCoords

/-- The vertical direction of the run's coordinate frame. -/
noncomputable def vert : Plane := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- **A `BG` tile followed by a `GB` tile at a shared junction is impossible in a dissection.** -/
theorem bg_gb_dies {N : ℕ} (D : Dissection N) {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂)
    {k₁ k₂ : Fin 3} (hshare : (D.tile i₁).pts k₁ = (D.tile i₂).pts k₂)
    (f h : ℝ) (hf : 1 < f) (hh : 0 < h)
    (hA0 : ((D.tile i₁).pts (k₁ + 1) - (D.tile i₁).pts k₁) 0 = -f)
    (hA1 : ((D.tile i₁).pts (k₁ + 1) - (D.tile i₁).pts k₁) 1 = 0)
    (hC0 : ((D.tile i₁).pts (k₁ + 2) - (D.tile i₁).pts k₁) 0 = dBG f - f)
    (hC1 : ((D.tile i₁).pts (k₁ + 2) - (D.tile i₁).pts k₁) 1 = h)
    (hD0 : ((D.tile i₂).pts (k₂ + 1) - (D.tile i₂).pts k₂) 0 = f)
    (hD1 : ((D.tile i₂).pts (k₂ + 1) - (D.tile i₂).pts k₂) 1 = 0)
    (hE0 : ((D.tile i₂).pts (k₂ + 2) - (D.tile i₂).pts k₂) 0 = dGB f)
    (hE1 : ((D.tile i₂).pts (k₂ + 2) - (D.tile i₂).pts k₂) 1 = h) :
    False := by
  obtain ⟨⟨α₁, β₁, hα₁, hβ₁, hs₁, hb₁⟩, ⟨α₂, β₂, hα₂, hβ₂, hs₂, hb₂⟩⟩ :=
    vertical_in_bg_gb_wedges f h hf hh
  set u₁ := (D.tile i₁).pts (k₁ + 1) - (D.tile i₁).pts k₁ with hu₁
  set w₁ := (D.tile i₁).pts (k₁ + 2) - (D.tile i₁).pts k₁ with hw₁
  set u₂ := (D.tile i₂).pts (k₂ + 1) - (D.tile i₂).pts k₂ with hu₂
  set w₂ := (D.tile i₂).pts (k₂ + 2) - (D.tile i₂).pts k₂ with hw₂
  have happ : ∀ (a b : ℝ) (u w : Plane) (j : Fin 2),
      (a • u + b • w) j = a * u j + b * w j := fun a b u w j => rfl
  have hv0 : vert (0 : Fin 2) = 0 := by
    simp [vert, EuclideanSpace.single_apply]
  have hv1 : vert (1 : Fin 2) = 1 := by
    simp [vert, EuclideanSpace.single_apply]
  refine Erdos634.MarchOverlap.Dissection.wedge_disjoint_combo D hne hshare
    (v := vert) hα₁ hβ₁ hα₂ hβ₂ ?_ ?_
  · ext j
    fin_cases j
    · show vert (0 : Fin 2) = (α₁ • u₁ + β₁ • w₁) (0 : Fin 2)
      rw [hv0, happ, hA0, hC0]; linarith [hs₁]
    · show vert (1 : Fin 2) = (α₁ • u₁ + β₁ • w₁) (1 : Fin 2)
      rw [hv1, happ, hA1, hC1]; linarith [hb₁]
  · ext j
    fin_cases j
    · show vert (0 : Fin 2) = (α₂ • u₂ + β₂ • w₂) (0 : Fin 2)
      rw [hv0, happ, hD0, hE0]; linarith [hs₂]
    · show vert (1 : Fin 2) = (α₂ • u₂ + β₂ • w₂) (1 : Fin 2)
      rw [hv1, happ, hD1, hE1]; linarith [hb₂]

end Erdos634.MarchKill
