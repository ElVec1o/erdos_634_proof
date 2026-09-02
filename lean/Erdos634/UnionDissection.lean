import Erdos634.Dissection
import Erdos634.Congruence

/-!
# Union of two dissections with disjoint interiors — the missing composition primitive

Erdős #634. `Compose.compose` is a *refinement* composer: given a `Dissection M` and, for each of
its `M` tiles, a `Dissection N` of that same tile, it produces a `Dissection (M*N)` of the whole
target — every macro-tile subdivided the same way. That is not what `thm:realize12`'s collar
induction needs: there, `Δ_m` (already tiled) and a collar piece (also already tiled) are two
*different* regions with disjoint interiors whose union is the bigger target `Δ_{m+2}`, and the
piece counts are added (`M+N`), not multiplied. No such union tool existed in the corpus before
this file — confirmed by search, see `private/VERIFY_PLAN.md`'s 2026-09-04 entry.

`unionDissection` supplies it, for plain `Dissection`s: given `D1 : Dissection M`, `D2 : Dissection
N` whose targets' carriers have disjoint interiors and union to a bigger triangle `T`'s carrier, the
`M+N` tiles (indexed by `Fin.append`) form a `Dissection (M+N)` of `T`. No measure-theoretic
argument is needed — unlike `ConvexCover.ofCertificate`'s route (containment + disjointness + area
identity), here `covers` is a direct consequence of `D1.covers`/`D2.covers`, and
`interiors_disjoint` splits into the two given dissections' own disjointness (same-side pairs) and
monotonicity of `interior` under the tile-carrier-⊆-target-carrier inclusion, composed with the
given disjointness of the two *targets'* interiors (cross-side pairs).

`unionCongruentDissection` is the `CongruentDissection` version needed for the actual collar step:
two dissections of the *same* model glue into one `CongruentDissection` of that model.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.UnionDissection

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {M N : ℕ}

/-- **Gluing two dissections with disjoint-interior targets into one, over their union.** -/
noncomputable def unionDissection (T : Tri) (D1 : Dissection M) (D2 : Dissection N)
    (hcov : D1.target.carrier ∪ D2.target.carrier = T.carrier)
    (hdisj : Disjoint (interior D1.target.carrier) (interior D2.target.carrier)) :
    Dissection (M + N) where
  target := T
  tile := Fin.append D1.tile D2.tile
  covers := by
    rw [← hcov, ← D1.covers, ← D2.covers]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      induction i using Fin.addCases with
      | left j => left; exact ⟨j, by rwa [Fin.append_left] at hi⟩
      | right j => right; exact ⟨j, by rwa [Fin.append_right] at hi⟩
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · exact ⟨Fin.castAdd N j, by rwa [Fin.append_left]⟩
      · exact ⟨Fin.natAdd M j, by rwa [Fin.append_right]⟩
  interiors_disjoint := by
    intro i j hij
    induction i using Fin.addCases with
    | left i' =>
      induction j using Fin.addCases with
      | left j' =>
        simp only [Fin.append_left]
        exact D1.interiors_disjoint (by simpa using hij)
      | right j' =>
        simp only [Fin.append_left, Fin.append_right]
        have h1 : interior (D1.tile i').carrier ⊆ interior D1.target.carrier :=
          interior_mono (by rw [← D1.covers]; exact Set.subset_iUnion (fun k => (D1.tile k).carrier) i')
        have h2 : interior (D2.tile j').carrier ⊆ interior D2.target.carrier :=
          interior_mono (by rw [← D2.covers]; exact Set.subset_iUnion (fun k => (D2.tile k).carrier) j')
        exact hdisj.mono h1 h2
    | right i' =>
      induction j using Fin.addCases with
      | left j' =>
        simp only [Fin.append_left, Fin.append_right]
        have h1 : interior (D1.tile j').carrier ⊆ interior D1.target.carrier :=
          interior_mono (by rw [← D1.covers]; exact Set.subset_iUnion (fun k => (D1.tile k).carrier) j')
        have h2 : interior (D2.tile i').carrier ⊆ interior D2.target.carrier :=
          interior_mono (by rw [← D2.covers]; exact Set.subset_iUnion (fun k => (D2.tile k).carrier) i')
        exact hdisj.symm.mono h2 h1
      | right j' =>
        simp only [Fin.append_right]
        exact D2.interiors_disjoint (by simpa using hij)

@[simp] theorem unionDissection_target (T : Tri) (D1 : Dissection M) (D2 : Dissection N)
    (hcov : D1.target.carrier ∪ D2.target.carrier = T.carrier)
    (hdisj : Disjoint (interior D1.target.carrier) (interior D2.target.carrier)) :
    (unionDissection T D1 D2 hcov hdisj).target = T := rfl

/-- The union dissection's tiles with index below `M` are `D1`'s own tiles. -/
theorem unionDissection_tile_left (T : Tri) (D1 : Dissection M) (D2 : Dissection N)
    (hcov : D1.target.carrier ∪ D2.target.carrier = T.carrier)
    (hdisj : Disjoint (interior D1.target.carrier) (interior D2.target.carrier)) (i : Fin M) :
    (unionDissection T D1 D2 hcov hdisj).tile (Fin.castAdd N i) = D1.tile i := by
  show Fin.append D1.tile D2.tile (Fin.castAdd N i) = D1.tile i
  rw [Fin.append_left]

/-- The union dissection's tiles with index `M` or above are `D2`'s own tiles. -/
theorem unionDissection_tile_right (T : Tri) (D1 : Dissection M) (D2 : Dissection N)
    (hcov : D1.target.carrier ∪ D2.target.carrier = T.carrier)
    (hdisj : Disjoint (interior D1.target.carrier) (interior D2.target.carrier)) (i : Fin N) :
    (unionDissection T D1 D2 hcov hdisj).tile (Fin.natAdd M i) = D2.tile i := by
  show Fin.append D1.tile D2.tile (Fin.natAdd M i) = D2.tile i
  rw [Fin.append_right]

end Erdos634.UnionDissection

open Erdos634.Geometry Erdos634.UnionDissection in
/-- **Gluing two `CongruentDissection`s of the same model.** The collar-induction step
(`thm:realize12`) needs exactly this: a real `Δ_m` witness glued to a same-tile collar piece into
one `Δ_{m+2}` witness. -/
noncomputable def unionCongruentDissection {M N : ℕ} (T : Tri)
    (D1 : CongruentDissection M) (D2 : CongruentDissection N) (hmodel : D1.model = D2.model)
    (hcov : D1.target.carrier ∪ D2.target.carrier = T.carrier)
    (hdisj : Disjoint (interior D1.target.carrier) (interior D2.target.carrier)) :
    CongruentDissection (M + N) where
  toDissection := unionDissection T D1.toDissection D2.toDissection hcov hdisj
  model := D1.model
  tiles_congruent := by
    intro i
    induction i using Fin.addCases with
    | left i' =>
      rw [unionDissection_tile_left]
      exact D1.tiles_congruent i'
    | right i' =>
      rw [unionDissection_tile_right, hmodel]
      exact D2.tiles_congruent i'
