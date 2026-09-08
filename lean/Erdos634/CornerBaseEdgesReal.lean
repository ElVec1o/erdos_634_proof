import Erdos634.TileAt
import Erdos634.CongruentTileEdges
import Erdos634.CongruentAngles

/-!
# `prop:cornerfig`'s edge clause, for the real base-corner tile of a real `CongruentDissection`

Erdős #634, tile-placement layer. `congruentDissection_base_corner_tile_vertex` (`TileAt.lean`)
identifies the real tile at a base corner and its vertex, with local angle `β` there — but only as
an *angle* fact, not yet an *edge-length* fact. `TilePlacement.corner_tile_edges` is the abstract
`Tri`-level statement that the two edges at a corner opposite the `b`-side are `a` and `c` (in one
order or the other). This file bridges the two for a real tile: the corner tile's two edges at the
base corner have lengths `{a, c}` as an unordered pair — real content about a real dissection's
actual corner tile, not merely the abstract shape fact.

**What this does NOT do**: it does not say *which* of the two edges (`a` or `c`) lies specifically
along the base direction — that needs the base line's actual direction, a separate, harder fact
(`lem:ccornerside`'s full content, still open). This file closes the edge-*identification* half
only: the corner tile's two corner-incident edges are `a` and `c`, some way round.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CornerBaseEdgesReal

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.TilePlacement

/-- **A congruent triangle's opposite side matches too, not just its angle.** Same proof
technique as `congruent_corner_angles` (the vertex correspondence `σ` from `dist_eq`, split on
whether it preserves or reverses the cyclic order), but concluding the *side* equality that same
case split already establishes as a byproduct. -/
theorem congruent_opposite_side {T U : Tri} (h : T.Congruent U) (j : Fin 3) :
    ∃ k : Fin 3, cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
      ∧ dist (T.pts (k+1)) (T.pts (k+2)) = dist (U.pts (j+1)) (U.pts (j+2)) := by
  obtain ⟨σ, hd⟩ := h.dist_eq
  set k := σ.symm j with hk
  have hσk : σ k = j := by rw [hk]; simp
  refine ⟨k, ?_, ?_⟩
  · have h1 : σ (k + 1) ≠ j := by
      intro hh; have := σ.injective (hh.trans hσk.symm); simp at this
    have h2 : σ (k + 2) ≠ j := by
      intro hh; have := σ.injective (hh.trans hσk.symm); simp at this
    have hne12 : σ (k + 1) ≠ σ (k + 2) := by
      intro hh; have := σ.injective hh; simp at this
    have hUne1 : U.pts (j + 1) ≠ U.pts j := by
      intro hh; have := U.indep.injective hh
      exact (by fin_cases j <;> decide : j + 1 ≠ j) this
    have hUne2 : U.pts (j + 2) ≠ U.pts j := by
      intro hh; have := U.indep.injective hh
      exact (by fin_cases j <;> decide : j + 2 ≠ j) this
    rcases fin3_cases (σ (k+1)) j h1 with hc1 | hc1
    · have hc2 : σ (k + 2) = j + 2 := by
        rcases fin3_cases (σ (k+2)) j h2 with hx | hx
        · exact absurd (by rw [hc1, hx]) hne12
        · exact hx
      have ptj : U.pts j = U.pts (σ k) := by rw [hσk]
      have pt1 : U.pts (j + 1) = U.pts (σ (k + 1)) := by rw [hc1]
      have pt2 : U.pts (j + 2) = U.pts (σ (k + 2)) := by rw [hc2]
      refine angle_of_sss ?_ ?_ ?_ hUne1 hUne2
      · rw [pt1, ptj]; exact (hd (k+1) k).symm
      · rw [ptj, pt2]; exact (hd k (k+2)).symm
      · rw [pt1, pt2]; exact (hd (k+1) (k+2)).symm
    · have hc2 : σ (k + 2) = j + 1 := by
        rcases fin3_cases (σ (k+2)) j h2 with hx | hx
        · exact hx
        · exact absurd (by rw [hc1, hx]) hne12
      have hcomm : cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
          = cornerAngle (U.pts (j + 2)) (U.pts j) (U.pts (j + 1)) :=
        EuclideanGeometry.angle_comm (V := Plane) _ _ _
      rw [hcomm]
      have ptj : U.pts j = U.pts (σ k) := by rw [hσk]
      have pt1 : U.pts (j + 2) = U.pts (σ (k + 1)) := by rw [hc1]
      have pt2 : U.pts (j + 1) = U.pts (σ (k + 2)) := by rw [hc2]
      refine angle_of_sss ?_ ?_ ?_ hUne2 hUne1
      · rw [pt1, ptj]; exact (hd (k+1) k).symm
      · rw [ptj, pt2]; exact (hd k (k+2)).symm
      · rw [pt1, pt2]; exact (hd (k+1) (k+2)).symm
  · have h1 : σ (k + 1) ≠ j := by
      intro hh; have := σ.injective (hh.trans hσk.symm); simp at this
    have h2 : σ (k + 2) ≠ j := by
      intro hh; have := σ.injective (hh.trans hσk.symm); simp at this
    have hne12 : σ (k + 1) ≠ σ (k + 2) := by
      intro hh; have := σ.injective hh; simp at this
    rcases fin3_cases (σ (k+1)) j h1 with hc1 | hc1
    · have hc2 : σ (k + 2) = j + 2 := by
        rcases fin3_cases (σ (k+2)) j h2 with hx | hx
        · exact absurd (by rw [hc1, hx]) hne12
        · exact hx
      rw [hd (k+1) (k+2), hc1, hc2]
    · have hc2 : σ (k + 2) = j + 1 := by
        rcases fin3_cases (σ (k+2)) j h2 with hx | hx
        · exact hx
        · exact absurd (by rw [hc1, hx]) hne12
      rw [hd (k+1) (k+2), hc1, hc2, dist_comm]

/-- **The real base-corner tile's two edges are `{a,c}`, as an unordered pair.** Given the base
corner's angle is `β` (occurring, among the model's three pairwise-distinct corner angles, only at
model vertex `1`), the real corner tile's two edges at its own corner vertex have lengths `a` and
`c` in one order or the other — `prop:cornerfig`'s edge clause, for a real tile, not just the
abstract shape. -/
theorem congruentDissection_base_corner_edges (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0) (hβ2π : β ≠ 2 * Real.pi)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hb : sideOpp D.model 1 ≠ 0)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    ∃ i : Fin N, ∃ j : Fin 3, D.target.pts k = (D.tile i).pts j ∧
      ((dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 2 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 0) ∨
       (dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 0 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 2)) := by
  classical
  obtain ⟨i, j, hij, hangle, _⟩ :=
    congruentDissection_base_corner_tile_vertex D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hβ2π
      hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' k hcorner
  refine ⟨i, j, hij, ?_⟩
  have hcorner_tile : cornerAngle ((D.tile i).pts (j+1)) ((D.tile i).pts j) ((D.tile i).pts (j+2))
      = β := by rw [← Tri.localAngle_vertex, ← hij]; exact hangle
  -- One application, correctly directed: T' := D.model, U' := D.tile i, U'-vertex := j.
  -- Gives a *single* model vertex k0 with matching angle and matching opposite side, both
  -- traced through the same underlying correspondence — no separate extraction to reconcile.
  obtain ⟨k0, hk0angle, hk0side⟩ :=
    congruent_opposite_side (D.tiles_congruent i).symm j
  rw [hcorner_tile] at hk0angle
  -- `k0` is the model vertex matching the tile's angle `β`; among `0,1,2` (angles `α,β,γ`,
  -- pairwise distinct) that is forced to be `1`.
  have hk0eq : k0 = 1 := by
    fin_cases k0
    · exact absurd (hk0angle.trans hα') hαβ.symm
    · rfl
    · exact absurd (hk0angle.trans hγ') hβγ
  subst hk0eq
  -- `hk0side` now reads: `dist (D.model.pts 2) (D.model.pts 0) = dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2))`.
  have hopp : dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 1 := by
    rw [← hk0side]; unfold sideOpp; norm_num
  -- Now apply the abstract shape fact `corner_tile_edges` to the real tile.
  have hmulti := (D.tiles_congruent i).sideMultiset_eq
  have hshift := Tri.sideMultiset_shift (D.tile i) j
  have hmul : ({dist ((D.tile i).pts j) ((D.tile i).pts (j+1)),
      dist ((D.tile i).pts (j+2)) ((D.tile i).pts j),
      dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2))} : Multiset ℝ)
      = {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} := by
    rw [hshift, hmulti]
    simp only [sideOpp, show (2:Fin 3)+1=0 from rfl, show (2:Fin 3)+2=1 from rfl,
      show (0:Fin 3)+1=1 from rfl, show (0:Fin 3)+2=2 from rfl,
      show (1:Fin 3)+1=2 from rfl, show (1:Fin 3)+2=0 from rfl]
  rcases corner_tile_edges (D.tile i) j (sideOpp D.model 2) (sideOpp D.model 1) (sideOpp D.model 0)
      hb hopp hmul with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

end Erdos634.CornerBaseEdgesReal

#print axioms Erdos634.CornerBaseEdgesReal.congruent_opposite_side
#print axioms Erdos634.CornerBaseEdgesReal.congruentDissection_base_corner_edges
