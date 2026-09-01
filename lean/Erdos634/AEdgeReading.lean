import Erdos634.EdgeType
import Erdos634.OrientBridge
import Erdos634.Placement
import Erdos634.MarchRunObject
import Erdos634.OrientWord

/-!
# The orientation word, read off a real `a`-edge

Erdős #634, bridge (c)'s remaining fact, named in `PAPER_MAP`'s `prop:orientmono` row: "the
orientation word is the one read off the tiles rather than an abstract `Bool` sequence"
(`MarchRunObject`'s header), equivalently "which of its edges are `a`-edges" (the row's own note).

`OrientBridge.orient_reading`/`.orient_BG_east_gamma`/`.orient_GB_west_gamma` already prove the
combinatorial content, but each took as *hypotheses* exactly the facts a real `a`-edge supplies:
its two ends carry `β` and `γ`, distinct. `EdgeType.a_edge_endpoints` proved those facts (vertex-
indexed); this file moves them to the `edgeWest`/`edgeEast` (direction-indexed) form the readings
need, via `EdgeType.localAngle_edgeWest_edgeEast`, and discharges the readings unconditionally for
any real `a`-edge — then assembles a real `MarchRunObject.aRun`'s word into
`OrientWord.word_isChain`, given its junction incidence (still a hypothesis: the run's contiguity
along the line is `BaseChain.base_chain_consecutive_meet`'s unclosed business).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.AEdgeReading

open Erdos634.Geometry Erdos634.Placement Erdos634.Inflation Erdos634.TilePlacement

variable {N : ℕ}

/-- **A real `a`-edge's `edgeWest`/`edgeEast` carry `β` and `γ`, distinct.** The direction-indexed
form of `EdgeType.a_edge_endpoints`, obtained by tracking which of `angleAt k`/`angleAt (k+1)`
`localAngle_edgeWest_edgeEast` assigns to `edgeWest`/`edgeEast`. -/
theorem a_edge_west_east (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 0) :
    ((D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = β ∨
      (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = γ) ∧
    ((D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = β ∨
      (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = γ) ∧
    (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) ≠
      (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) := by
  obtain ⟨hk, hk1, hne⟩ := a_edge_endpoints D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ i k hlen
  rcases Erdos634.Geometry.localAngle_edgeWest_edgeEast D.toDissection dir i k with
    ⟨hw, he⟩ | ⟨hw, he⟩
  · rw [hw, he]; exact ⟨hk, hk1, hne⟩
  · rw [hw, he]; exact ⟨hk1, hk, hne.symm⟩

/-- **The `BG` reading, unconditionally, for a real `a`-edge.** No hypothesis about the endpoint
angles remains: they follow from `hlen` alone. -/
theorem tile_orient_BG_east_gamma (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 0)
    (h : Erdos634.OrientBridge.tileOrient D.toDissection β i
      (edgeWest D.toDissection dir (i, k)) = Orient.BG) :
    (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = γ := by
  obtain ⟨hw, he, hne⟩ := a_edge_west_east D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir i k hlen
  exact Erdos634.OrientBridge.orient_BG_east_gamma D.toDissection i
    (edgeWest D.toDissection dir (i, k)) (edgeEast D.toDissection dir (i, k)) β γ hβγ hw he hne h

/-- **The `GB` reading, unconditionally, for a real `a`-edge.** -/
theorem tile_orient_GB_west_gamma (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 0)
    (h : Erdos634.OrientBridge.tileOrient D.toDissection β i
      (edgeWest D.toDissection dir (i, k)) = Orient.GB) :
    (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = γ := by
  obtain ⟨hw, _, _⟩ := a_edge_west_east D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir i k hlen
  exact Erdos634.OrientBridge.orient_GB_west_gamma D.toDissection i
    (edgeWest D.toDissection dir (i, k)) β γ hw h

/-! ## Assembling a real `a`-run's word

`MarchRunObject.aRun` selects the `a`-edges of the wall; given an enumeration `E` of its members
(any enumeration — `ChainEnum.exists_sorted_enum` supplies a canonical one for any list) and the
run's junction incidence (`edgeEast (E k) = edgeWest (E (k+1))`, still unproved for the *filtered*
run — `BaseChain.base_chain_consecutive_meet` closes it only for the unfiltered `wallList`), the
word read off the tiles via `OrientBridge.tileOrient` at each edge's west end is an admissible
chain, hence (`Inflation.orient_monotone`) of the form `GB^j BG^(L-j)`. This is `prop:orientmono`'s
statement, for a real run, conditional on the still-missing junction incidence. -/

open Erdos634.MarchRunObject Erdos634.OrientWord Erdos634.Inflation in
/-- **A real `a`-run's word is admissible**, hence monotone. Conditional on `hjunc` (junction
incidence for the filtered run — not yet derived from contiguity) and `hne`/`hfront`/`hvert`
(distinct tiles, non-vertex frontier junctions — the placement facts `BridgeC.chain_junctions`
supplies for the *unfiltered* wall and which have not been re-derived here for the filtered run). -/
theorem aRun_word_monotone (D : CongruentDissection N) (g : Plane →ᵃ[ℝ] ℝ) (c a : ℝ)
    (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαpos : 0 < α) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hγeq : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi)
    (ha : a = sideOpp D.model 0)
    (dir : Plane →ₗ[ℝ] ℝ) (L : ℕ) (hL : L = runLength D.toDissection g c a)
    (E : ℕ → Fin N × Fin 3)
    (hmem : ∀ k, k < L → E k ∈ aRun D.toDissection g c a)
    (hne : ∀ k, k + 1 < L → (E k).1 ≠ (E (k + 1)).1)
    (hjunc : ∀ k, k + 1 < L →
      edgeEast D.toDissection dir (E k) = edgeWest D.toDissection dir (E (k + 1)))
    (hfront : ∀ k, k + 1 < L → edgeEast D.toDissection dir (E k) ∈ frontier D.target.carrier)
    (hvert : ∀ k, k + 1 < L →
      edgeEast D.toDissection dir (E k) ∉ Set.range D.target.pts) :
    ∃ j k : ℕ, j + k = L ∧
      (word L (fun k => Erdos634.OrientBridge.tileOrient D.toDissection β (E k).1
        (edgeWest D.toDissection dir (E k)))) =
        List.replicate j Orient.GB ++ List.replicate k Orient.BG := by
  classical
  set o : ℕ → Orient := fun k =>
    Erdos634.OrientBridge.tileOrient D.toDissection β (E k).1 (edgeWest D.toDissection dir (E k))
    with ho
  have hlen : ∀ k, k < L →
      dist ((D.tile (E k).1).pts (E k).2) ((D.tile (E k).1).pts ((E k).2 + 1)) =
        sideOpp D.model 0 := by
    intro k hk
    have := (mem_aRun D.toDissection g c a (E k)).mp (hmem k hk)
    rw [← ha]; exact this.2
  have hword : (word L o).IsChain (fun l r => admissiblePair l r = true) := by
    refine word_isChain D.toDissection L o (fun k => (E k).1)
      (fun k => edgeEast D.toDissection dir (E k)) α β γ hαpos hγeq hπ hfront hvert hne ?_ ?_
    · intro j hj hBG
      exact tile_orient_BG_east_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir (E j).1
        (E j).2 (hlen j (by omega)) hBG
    · intro j hj hGB
      simp only
      rw [hjunc j hj]
      exact tile_orient_GB_west_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
        (E (j + 1)).1 (E (j + 1)).2 (hlen (j + 1) (by omega)) hGB
  obtain ⟨j, k, hjk⟩ := orient_monotone (word L o) hword
  refine ⟨j, k, ?_, hjk⟩
  have hlenword : (word L o).length = L := word_length L o
  rw [hjk] at hlenword
  simpa using hlenword

end Erdos634.AEdgeReading
