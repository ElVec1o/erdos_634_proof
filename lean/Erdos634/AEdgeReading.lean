import Erdos634.EdgeType
import Erdos634.OrientBridge
import Erdos634.Placement
import Erdos634.MarchRunObject
import Erdos634.OrientWord
import Erdos634.BridgeC
import Erdos634.WallEndpoints
import Erdos634.BaseSelection
import Erdos634.WallSide

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

/-! ## The same assembly, driven by `WallEndpoints.chain_endpoints` directly

`aRun_word_monotone` above took the run's junction incidence as a hypothesis, because
`MarchRunObject.aRun`'s *filtered* sublist has no junction theorem of its own. But
`WallEndpoints.chain_endpoints` already gives junction incidence, membership, injectivity, *and*
strict interior position bounds **unconditionally** for the *entire* wall (no filtering) — so when
the whole wall is an `a`-run (the natural setting: a full side, as in `thm:chain` and
`prop:orientmono`), none of those needs to be assumed. This section removes every hypothesis the
previous version could not derive, using only `chain_endpoints`, `BridgeC.g_ends`,
`WallSide.wall_edges_same_tile` and `BridgeC.junction_frontier_nonvertex` — all pre-existing. -/

open Erdos634.OrientWord Erdos634.Inflation Erdos634.BridgeC Erdos634.WallEndpoints
  Erdos634.BaseChain Erdos634.WallSide in
/-- **A whole `a`-side's word is admissible, hence monotone.** The only hypotheses beyond the
standard wall/line setup (`hker`,`hwall`,`hbase`,`hline`,`hface`,`hthird`,`hvertt` — all already
used unconditionally elsewhere in this project's bridge (c)) are `hdirab` (a choice of reading
direction) and `hlen` (every wall edge is an `a`-edge, i.e. the whole side is the run). Everything
else — junction incidence, distinct tiles, non-vertex frontier junctions — is derived. -/
theorem side_word_monotone (D : CongruentDissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαpos : 0 < α) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hγeq : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi)
    (hN : 0 < N) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b) (hdirab : dir a ≤ dir b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hthird : ∀ p ∈ wallList D.toDissection g c, g ((D.tile p.1).pts (p.2 + 2)) < c)
    (hvertt : ∀ j : Fin 3, D.target.pts j = a ∨ D.target.pts j = b ∨ g (D.target.pts j) < c)
    (hlen : ∀ p ∈ wallList D.toDissection g c,
      dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = sideOpp D.model 0) :
    ∃ E : ℕ → Fin N × Fin 3, ∃ n j k' : ℕ, n = (wallList D.toDissection g c).length ∧
      j + k' = n ∧
      (word n (fun m => Erdos634.OrientBridge.tileOrient D.toDissection β (E m).1
        (edgeWest D.toDissection dir (E m)))) =
        List.replicate j Orient.GB ++ List.replicate k' Orient.BG := by
  classical
  obtain ⟨E, n, hneq, hn0, hwest0, heastlast, hjunc, hmem, hinj, hlba, hlbend, hnondeg⟩ :=
    chain_endpoints hN D.toDissection g c dir hker hwall a b hab hdirab hbase hline hface hthird
  refine ⟨E, n, ?_⟩
  set o : ℕ → Orient := fun m =>
    Erdos634.OrientBridge.tileOrient D.toDissection β (E m).1 (edgeWest D.toDissection dir (E m))
    with ho
  have hlenE : ∀ m, m < n →
      dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1)) =
        sideOpp D.model 0 := fun m hm => hlen (E m) (hmem m hm)
  have hlinE : ∀ m, m < n → ∃ y, g y ≠ c := by
    intro m hm
    refine ⟨(D.tile (E m).1).pts ((E m).2 + 2), ?_⟩
    have := hthird (E m) (hmem m hm); linarith
  have hneE : ∀ m, m + 1 < n → (E m).1 ≠ (E (m + 1)).1 := by
    intro m hm heq
    have hef : E m ≠ E (m + 1) := by
      intro h; exact absurd (hinj m (m + 1) (by omega) (by omega) h) (by omega)
    have hwm := (mem_wallList D.toDissection g c (E m)).mp (hmem m (by omega))
    have hwm1 := (mem_wallList D.toDissection g c (E (m + 1))).mp (hmem (m + 1) (by omega))
    exact wall_edges_same_tile D.toDissection g c (hlinE m (by omega)) (E m) (E (m + 1)) hef heq
      hwm hwm1
  have hfrontE : ∀ m, m + 1 < n → edgeEast D.toDissection dir (E m) ∈ frontier D.target.carrier
      ∧ edgeEast D.toDissection dir (E m) ∉ Set.range D.target.pts := by
    intro m hm
    have hwm := (mem_wallList D.toDissection g c (E m)).mp (hmem m (by omega))
    have hp : edgeEast D.toDissection dir (E m) ∈ D.target.carrier :=
      Erdos634.BaseSelection.tile_subset_target D.toDissection (E m).1
        (by unfold edgeEast; split <;>
          exact subset_convexHull ℝ _ (Set.mem_range_self _))
    have hgp : g (edgeEast D.toDissection dir (E m)) = c :=
      (g_ends D.toDissection g c dir (E m) hwm).2
    have h1 : dir a < Erdos634.OrientBridge.edgePos D.toDissection dir (E (m + 1)) :=
      hlba (m + 1) (by omega) (by omega)
    have h2 : Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m) < dir b := hlbend m hm
    have heq : Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m)
        = Erdos634.OrientBridge.edgePos D.toDissection dir (E (m + 1)) := by
      rw [← dir_edgeEast, ← dir_edgeWest, hjunc m hm]
    have hstrict : min (dir a) (dir b) < dir (edgeEast D.toDissection dir (E m)) ∧
        dir (edgeEast D.toDissection dir (E m)) < max (dir a) (dir b) := by
      constructor
      · rw [min_eq_left hdirab, dir_edgeEast, heq]; exact h1
      · rw [max_eq_right hdirab, dir_edgeEast]; exact h2
    exact junction_frontier_nonvertex D.toDissection g c dir a b hbase hface hvertt hp hgp hstrict
  have hword : (word n o).IsChain (fun l r => admissiblePair l r = true) := by
    refine word_isChain D.toDissection n o (fun m => (E m).1)
      (fun m => edgeEast D.toDissection dir (E m)) α β γ hαpos hγeq hπ
      (fun m hm => (hfrontE m hm).1) (fun m hm => (hfrontE m hm).2) hneE ?_ ?_
    · intro j hj hBG
      exact tile_orient_BG_east_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir (E j).1
        (E j).2 (hlenE j (by omega)) hBG
    · intro j hj hGB
      simp only
      rw [hjunc j hj]
      exact tile_orient_GB_west_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
        (E (j + 1)).1 (E (j + 1)).2 (hlenE (j + 1) (by omega)) hGB
  obtain ⟨j, k', hjk⟩ := orient_monotone (word n o) hword
  refine ⟨j, k', hneq, ?_, hjk⟩
  have hlenword : (word n o).length = n := word_length n o
  rw [hjk] at hlenword
  simpa using hlenword

end Erdos634.AEdgeReading
