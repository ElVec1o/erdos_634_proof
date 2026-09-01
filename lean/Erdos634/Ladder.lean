import Erdos634.CellCoord
import Erdos634.Compose
import Erdos634.DissectionMap
import Erdos634.CongruentArea

/-!
# `thm:ladder`: the scaling ladder, as a construction

Erdős #634, `thm:ladder`:

> Let a triangle `T` be cut into `N` copies of a tile `t`. Then for every integer `k ≥ 1` the
> scaled triangle `kT` is cut into `k²N` copies of `t`.

The paper's proof is two sentences: subdivide `kT` by the triangular grid of side `k` into `k²`
triangles congruent to `T`, then cut each into `N` copies of `t`. Both sentences are now theorems.

* `Subdivision.ladderDissection` is the grid: a genuine `Dissection (k*k)` of `kT`, with
  `ladderDissection_congruent` saying every cell is congruent to `T`.
* `Compose.compose` is the refinement: a dissection of each tile of a dissection composes with it.

What is left, and is what this file does, is to move the given dissection of `T` onto each cell.
A congruence supplies an isometry of the plane; by Mazur–Ulam that isometry is affine
(`isoAff`), so `DissectionMap.mapDissection` transports the whole dissection along it, and
`CongruentArea.image_carrier_of_congruent` identifies the transported target with the cell.

`ladder` is the theorem as stated: an honest `CongruentDissection (k*k*N)` of `kT` with the same
model tile `t`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Ladder

open Erdos634.Geometry Erdos634.Subdivision Erdos634.DissectionMap MeasureTheory

/-- An isometry of the plane as an affine equivalence (Mazur–Ulam). -/
noncomputable def isoAff (f : Plane ≃ᵢ Plane) : Plane ≃ᵃ[ℝ] Plane :=
  f.toRealAffineIsometryEquiv.toAffineEquiv

@[simp] theorem isoAff_coe (f : Plane ≃ᵢ Plane) : ⇑(isoAff f) = ⇑f := rfl

/-- **Transporting a triangle by an isometry gives a congruent triangle.** -/
theorem congruent_mapTri (f : Plane ≃ᵢ Plane) (T : Tri) : T.Congruent (mapTri (isoAff f) T) :=
  ⟨f, Equiv.refl _, fun k => rfl⟩

variable {N : ℕ} (A B C : Plane)

/-- **`thm:ladder`.** If `T = ABC` is cut into `N` copies of a tile `t`, then for every `k ≥ 1`
the scaled triangle `kT` is cut into `k²N` copies of `t`. -/
theorem ladder (hindep : AffineIndependent ℝ ![A, B, C])
    (D : CongruentDissection N) (hT : D.target = (⟨![A, B, C], hindep⟩ : Tri))
    (k : ℕ) (hk : 0 < k) :
    ∃ E : CongruentDissection (k * k * N),
      E.target = bigTri A B C hindep k hk ∧ E.model = D.model := by
  classical
  set LD := ladderDissection A B C hindep k hk with hLD
  -- every cell of the grid is congruent to `T`; name the isometry realising it
  have hcong : ∀ n, Tri.Congruent (⟨![A, B, C], hindep⟩ : Tri) (LD.tile n) :=
    fun n => ladderDissection_congruent A B C hindep k hk n
  choose f σ hf using hcong
  -- transport `D` onto each cell
  set inner : Fin (k * k) → Dissection N :=
    fun n => mapDissection (isoAff (f n)) D.toDissection with hinner
  have hin : ∀ n, ((inner n).target).carrier = (LD.tile n).carrier := by
    intro n
    show (mapTri (isoAff (f n)) D.target).carrier = _
    rw [mapTri_carrier, hT, isoAff_coe]
    exact Erdos634.CongruentArea.image_carrier_of_congruent (hf n)
  refine ⟨{ Erdos634.Compose.compose LD inner hin with
            model := D.model
            tiles_congruent := ?_ }, ?_, rfl⟩
  · intro n
    show Tri.Congruent (mapTri (isoAff (f _)) (D.tile _)) D.model
    exact (congruent_mapTri (f _) (D.tile _)).symm.trans (D.tiles_congruent _)
  · rfl

end Erdos634.Ladder
