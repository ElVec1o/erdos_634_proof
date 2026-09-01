import Erdos634.EdgeType
import Erdos634.OrientBridge
import Erdos634.Placement

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
any real `a`-edge.

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

end Erdos634.AEdgeReading
