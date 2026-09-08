import Erdos634.CornerBaseEdgesReal

/-!
# `prop:cornerfig`'s edge clause, apex half: real apex tiles' edges are `{b,c}`

Erdős #634, tile-placement layer. `CornerBaseEdgesReal.lean` closed the base-corner half of
`prop:cornerfig`'s edge clause. This file closes the apex half: each of the three real tiles
presenting `α` at the apex has its two corner-incident edges equal to `{b,c}`, as an unordered
pair — not merely the abstract shape fact.

The apex has *three* tiles, not one, so `TileAt`'s "the unique tile" argument
(`congruentDissection_base_corner_tile_vertex`) does not directly apply. What generalizes without
needing uniqueness: a tile presenting a genuine corner angle (not `0`, `π`, or `2π`) at a point
necessarily has that point as one of its own vertices — `Tri.localAngle`'s definition forces this
branch regardless of how many *other* tiles also cover the point. So each of the three
`α`-presenting tiles individually gets the same vertex-identification and edge-length treatment
`CornerBaseEdgesReal` gave the single base-corner tile.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ApexEdgesReal

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.TilePlacement
open Erdos634.CornerBaseEdgesReal

/-- **A tile presenting a genuine corner angle at a point has that point as one of its own
vertices.** Same case-split `Tri.localAngle`'s definition forces, used inline in
`congruentDissection_base_corner_tile_vertex` — extracted here since the apex case needs it for
*each* of three tiles, not one unique witness. -/
theorem isVertex_of_localAngle_ne (T : Tri) {p : Plane} {v : ℝ}
    (hv2π : v ≠ 2 * Real.pi) (hvπ : v ≠ Real.pi) (hv0 : v ≠ 0)
    (hangle : T.localAngle p = v) : ∃ j : Fin 3, p = T.pts j := by
  classical
  by_contra hcon
  push_neg at hcon
  rw [Erdos634.Geometry.Tri.localAngle] at hangle
  simp only [hcon, exists_false, dif_neg, not_false_eq_true] at hangle
  split at hangle
  · exact hv2π hangle.symm
  · split at hangle
    · exact hvπ hangle.symm
    · exact hv0 hangle.symm

/-- **Each real apex tile's two edges are `{b,c}`, as an unordered pair.** For every tile `i`
presenting `α` at the apex (there are exactly three, by `congruentDissection_apex_counts`), its
two corner-incident edges at the apex point have lengths `b` and `c` in one order or the other. -/
theorem congruentDissection_apex_edges (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0) (hα2π : α ≠ 2 * Real.pi)
    (hβγ : β ≠ γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hc : sideOpp D.model 0 ≠ 0)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (i : Fin N) (hi : (D.tile i).localAngle (D.target.pts k) = α) :
    ∃ j : Fin 3, D.target.pts k = (D.tile i).pts j ∧
      ((dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 1 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 2) ∨
       (dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 2 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 1)) := by
  classical
  obtain ⟨j, hij⟩ := isVertex_of_localAngle_ne (D.tile i) (v := α) hα2π hαπ hα0 hi
  refine ⟨j, hij, ?_⟩
  have hcorner_tile : cornerAngle ((D.tile i).pts (j+1)) ((D.tile i).pts j) ((D.tile i).pts (j+2))
      = α := by rw [← Tri.localAngle_vertex, ← hij]; exact hi
  obtain ⟨k0, hk0angle, hk0side⟩ :=
    congruent_opposite_side (D.tiles_congruent i).symm j
  rw [hcorner_tile] at hk0angle
  have hk0eq : k0 = 0 := by
    fin_cases k0
    · rfl
    · exact absurd (hk0angle.trans hβ') hαβ
    · exact absurd (hk0angle.trans hγ') hαγ
  subst hk0eq
  have hopp : dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 0 := by
    rw [← hk0side]; unfold sideOpp; norm_num
  have hmulti := (D.tiles_congruent i).sideMultiset_eq
  have hshift := Tri.sideMultiset_shift (D.tile i) j
  have hmul : ({dist ((D.tile i).pts j) ((D.tile i).pts (j+1)),
      dist ((D.tile i).pts (j+2)) ((D.tile i).pts j),
      dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2))} : Multiset ℝ)
      = {sideOpp D.model 1, sideOpp D.model 0, sideOpp D.model 2} := by
    rw [hshift, hmulti]
    simp only [sideOpp, show (2:Fin 3)+1=0 from rfl, show (2:Fin 3)+2=1 from rfl,
      show (0:Fin 3)+1=1 from rfl, show (0:Fin 3)+2=2 from rfl,
      show (1:Fin 3)+1=2 from rfl, show (1:Fin 3)+2=0 from rfl]
    show ({_,_,_}:Multiset ℝ) = {_,_,_}
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    simp only [add_comm, add_assoc, add_left_comm]
  rcases corner_tile_edges (D.tile i) j (sideOpp D.model 1) (sideOpp D.model 0) (sideOpp D.model 2)
      hc hopp hmul with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

end Erdos634.ApexEdgesReal

#print axioms Erdos634.ApexEdgesReal.isVertex_of_localAngle_ne
#print axioms Erdos634.ApexEdgesReal.congruentDissection_apex_edges
