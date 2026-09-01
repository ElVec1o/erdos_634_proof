import Erdos634.Dissection
import Erdos634.Congruence

/-!
# Restricting a dissection to a tile subset

Erdős #634. Several `PROVED` rows — `thm:farregion`/`cor:farvacuous` ("the region cut off by a
wall as an object; no Lean notion of a sub-region of a dissection"), and `prop:orientmono`'s
inflated-tile instantiation (a real occurrence `Δ_k` restricted from a real tiling) — all cite the
identical missing piece: given a real `Dissection` and a subset of its tiles whose union happens to
equal some other triangle `T`, package that subset as a `Dissection` of `T` in its own right.

This file is that packaging. It does NOT establish the covering-equality hypothesis for any
specific application (that a wall's far region, or an inflated tile's occurrence, actually is
covered by some particular tile subset) — that is real geometric content specific to each row, and
remains exactly as unbuilt as before. What it removes is the *bookkeeping* obstacle: once the
covering-equality is in hand, producing the `Dissection` object itself is now mechanical.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SubDissection

open Erdos634.Geometry

variable {N : ℕ}

/-- **A dissection restricted to a tile subset**, given that the subset's tiles cover exactly some
other triangle `T`. The new dissection has `S.card` tiles, indexed via `Finset.orderEmbOfFin`. -/
noncomputable def restrict (D : Dissection N) (S : Finset (Fin N)) (T : Tri)
    (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier) :
    Dissection S.card where
  target := T
  tile := fun j => D.tile (S.orderEmbOfFin rfl j)
  covers := by
    rw [← hcov]
    apply le_antisymm
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨j, hxj⟩ := hx
      simp only [Set.mem_iUnion]
      exact ⟨S.orderEmbOfFin rfl j, S.orderEmbOfFin_mem rfl j, hxj⟩
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hiS, hxi⟩ := hx
      have hiS' : i ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hiS
      obtain ⟨j, hji⟩ := hiS'
      simp only [Set.mem_iUnion]
      exact ⟨j, hji ▸ hxi⟩
  interiors_disjoint := by
    intro j j' hjj'
    exact D.interiors_disjoint (fun h => hjj' ((S.orderEmbOfFin rfl).injective h))

/-- **The restricted dissection's tiles are exactly `D`'s tiles indexed by `S`.** -/
theorem restrict_tile (D : Dissection N) (S : Finset (Fin N)) (T : Tri)
    (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier) (j : Fin S.card) :
    (restrict D S T hcov).tile j = D.tile (S.orderEmbOfFin rfl j) := rfl

/-- **The restricted dissection's target is `T`.** -/
theorem restrict_target (D : Dissection N) (S : Finset (Fin N)) (T : Tri)
    (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier) :
    (restrict D S T hcov).target = T := rfl

/-- **A `CongruentDissection` restricted to a tile subset**, preserving the model — needed for
`prop:orientmono`'s inflated-tile instantiation, where the restricted piece must still be a real
`CongruentDissection` (congruent to the same tile), not just a plain `Dissection`. -/
noncomputable def restrictCongruent (D : CongruentDissection N) (S : Finset (Fin N)) (T : Tri)
    (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier) :
    CongruentDissection S.card where
  toDissection := restrict D.toDissection S T hcov
  model := D.model
  tiles_congruent := fun j => D.tiles_congruent (S.orderEmbOfFin rfl j)

theorem restrictCongruent_target (D : CongruentDissection N) (S : Finset (Fin N)) (T : Tri)
    (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier) :
    (restrictCongruent D S T hcov).target = T := rfl

theorem restrictCongruent_model (D : CongruentDissection N) (S : Finset (Fin N)) (T : Tri)
    (hcov : (⋃ i ∈ S, (D.tile i).carrier) = T.carrier) :
    (restrictCongruent D S T hcov).model = D.model := rfl

end Erdos634.SubDissection
