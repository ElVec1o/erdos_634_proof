import Erdos634.EdgeType
import Erdos634.OrientBridge
import Erdos634.Placement
import Erdos634.OrientWord
import Erdos634.BridgeC
import Erdos634.WallEndpoints
import Erdos634.BaseSelection
import Erdos634.WallSide
import Erdos634.TileAt

/-!
# The orientation word, read off a real `b`-edge — `thm:chain`

Erdős #634, `thm:chain`'s remaining fact, named in `PAPER_MAP`'s own row: "the passage from a real
run to the word is bridge (c) at that side... what remains is the readings at that side, i.e. which
of its edges are `a`-edges" — the same shape of gap `prop:orientmono` has (closed for `a`-edges in
`AEdgeReading.lean`), but for **`b`-edges** (flanking angles `α`,`γ`, not `β`,`γ`) and with the
CONSTANT conclusion (`thm:chain` says every edge is uniformly oriented, seeded by an apex tile),
not just monotone.

`OrientBridge.orient_reading`/`.orient_BG_east_gamma`/`.orient_GB_west_gamma` and
`OrientWord.corner_anchored_word` are all generic in the "own" angle parameter (called `β` in their
signatures, but not tied to it) — this file supplies `EdgeType.b_edge_endpoints`'s facts in that
slot instead, closing the same unconditional-reading gap for `b`-edges.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BEdgeReading

open Erdos634.Geometry Erdos634.Placement Erdos634.Inflation Erdos634.TilePlacement

variable {N : ℕ}

/-- **A real `b`-edge's `edgeWest`/`edgeEast` carry `α` and `γ`, distinct.** -/
theorem b_edge_west_east (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 1) :
    ((D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = α ∨
      (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = γ) ∧
    ((D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = α ∨
      (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = γ) ∧
    (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) ≠
      (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) := by
  obtain ⟨hk, hk1, hne⟩ := b_edge_endpoints D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ i k hlen
  rcases Erdos634.Geometry.localAngle_edgeWest_edgeEast D.toDissection dir i k with
    ⟨hw, he⟩ | ⟨hw, he⟩
  · rw [hw, he]; exact ⟨hk, hk1, hne⟩
  · rw [hw, he]; exact ⟨hk1, hk, hne.symm⟩

/-- **The `BG` reading, unconditionally, for a real `b`-edge.** -/
theorem tile_orient_BG_east_gamma (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 1)
    (h : Erdos634.OrientBridge.tileOrient D.toDissection α i
      (edgeWest D.toDissection dir (i, k)) = Orient.BG) :
    (D.tile i).localAngle (edgeEast D.toDissection dir (i, k)) = γ := by
  obtain ⟨hw, he, hne⟩ := b_edge_west_east D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir i k hlen
  exact Erdos634.OrientBridge.orient_BG_east_gamma D.toDissection i
    (edgeWest D.toDissection dir (i, k)) (edgeEast D.toDissection dir (i, k)) α γ hαγ hw he hne h

/-- **The `GB` reading, unconditionally, for a real `b`-edge.** -/
theorem tile_orient_GB_west_gamma (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (dir : Plane →ₗ[ℝ] ℝ) (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 1)
    (h : Erdos634.OrientBridge.tileOrient D.toDissection α i
      (edgeWest D.toDissection dir (i, k)) = Orient.GB) :
    (D.tile i).localAngle (edgeWest D.toDissection dir (i, k)) = γ := by
  obtain ⟨hw, _, _⟩ := b_edge_west_east D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir i k hlen
  exact Erdos634.OrientBridge.orient_GB_west_gamma D.toDissection i
    (edgeWest D.toDissection dir (i, k)) α γ hw h

/-! ## Assembly: a real `b`-side's word is constant, given it is seeded at an apex tile

`thm:chain`'s own conclusion is stronger than mere monotonicity — the whole run is uniformly `BG`
(`α` at the apex end, `γ` at the far end), *given* the seed condition (the first tile presents `α`
at its own apex end). This uses `OrientWord.corner_anchored_word`
(`RunOrientation.corner_anchored_run_all_BG`) instead of `Inflation.orient_monotone`. -/

open Erdos634.OrientWord Erdos634.Inflation Erdos634.BridgeC Erdos634.WallEndpoints
  Erdos634.WallSide in
/-- **A whole `b`-side's word is constantly `BG`, given it is seeded at an apex tile.** Same
unconditional derivation as `AEdgeReading.side_word_monotone` (junction incidence, distinct tiles,
non-vertex frontier junctions all come from `chain_endpoints`/`wall_edges_same_tile`/
`junction_frontier_nonvertex`), but for `b`-edges and the constant (not merely monotone) conclusion
`thm:chain` needs. `hseed` is "seeded at an apex tile": the first tile of the run presents `α` at
its own west end. -/
theorem side_word_constant (D : CongruentDissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
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
    (hthird : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection g c,
      g ((D.tile p.1).pts (p.2 + 2)) < c)
    (hlen : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection g c,
      dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = sideOpp D.model 1)
    (hvertt : ∀ j : Fin 3, D.target.pts j = a ∨ D.target.pts j = b ∨ g (D.target.pts j) < c)
    (hseed : ∀ E : ℕ → Fin N × Fin 3,
      Erdos634.OrientBridge.tileOrient D.toDissection α (E 0).1
        (edgeWest D.toDissection dir (E 0)) = Orient.BG) :
    ∃ E : ℕ → Fin N × Fin 3,
      word (Erdos634.BaseChain.wallList D.toDissection g c).length
        (fun m => Erdos634.OrientBridge.tileOrient D.toDissection α (E m).1
          (edgeWest D.toDissection dir (E m))) =
      List.replicate (Erdos634.BaseChain.wallList D.toDissection g c).length Orient.BG := by
  classical
  set L := (Erdos634.BaseChain.wallList D.toDissection g c).length with hL
  obtain ⟨E, n, hneq, hn0, hwest0, heastlast, hjunc, hmem, hinj, hlba, hlbend, hnondeg, hsurj⟩ :=
    chain_endpoints hN D.toDissection g c dir hker hwall a b hab hdirab hbase hline hface hthird
  refine ⟨E, ?_⟩
  set o : ℕ → Orient := fun m =>
    Erdos634.OrientBridge.tileOrient D.toDissection α (E m).1 (edgeWest D.toDissection dir (E m))
    with ho
  have hlenE : ∀ m, m < n →
      dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1))
        = sideOpp D.model 1 := fun m hm => hlen (E m) (hmem m hm)
  have hne : ∀ m, m + 1 < n → (E m).1 ≠ (E (m + 1)).1 := by
    intro m hm heq
    have hlin : ∃ y, g y ≠ c := by
      refine ⟨(D.tile (E m).1).pts ((E m).2 + 2), ?_⟩
      have := hthird (E m) (hmem m (by omega)); linarith
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E m)).mp (hmem m (by omega))
    have hwm1 := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E (m + 1))).mp
      (hmem (m + 1) (by omega))
    exact wall_edges_same_tile D.toDissection g c hlin (E m) (E (m + 1))
      (by intro h; exact absurd (hinj m (m + 1) (by omega) (by omega) h) (by omega)) heq hwm hwm1
  have hfrontE : ∀ m, m + 1 < n → edgeEast D.toDissection dir (E m) ∈ frontier D.target.carrier
      ∧ edgeEast D.toDissection dir (E m) ∉ Set.range D.target.pts := by
    intro m hm
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E m)).mp (hmem m (by omega))
    have hp : edgeEast D.toDissection dir (E m) ∈ D.target.carrier :=
      Erdos634.BaseSelection.tile_subset_target D.toDissection (E m).1
        (by unfold edgeEast; split <;> exact subset_convexHull ℝ _ (Set.mem_range_self _))
    have hgp : g (edgeEast D.toDissection dir (E m)) = c :=
      (g_ends D.toDissection g c dir (E m) hwm).2
    have h1 : dir a < Erdos634.OrientBridge.edgePos D.toDissection dir (E (m + 1)) := hlba (m + 1) (by omega) (by omega)
    have h2 : Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m) < dir b := hlbend m hm
    have heq2 : Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m) = Erdos634.OrientBridge.edgePos D.toDissection dir (E (m + 1)) := by
      rw [← dir_edgeEast, ← dir_edgeWest, hjunc m hm]
    have hstrict : min (dir a) (dir b) < dir (edgeEast D.toDissection dir (E m)) ∧
        dir (edgeEast D.toDissection dir (E m)) < max (dir a) (dir b) := by
      constructor
      · rw [min_eq_left hdirab, dir_edgeEast, heq2]; exact h1
      · rw [max_eq_right hdirab, dir_edgeEast]; exact h2
    exact junction_frontier_nonvertex D.toDissection g c dir a b hbase hface hvertt hp hgp hstrict
  have hseed' : (word n o).head? = some Orient.BG := by
    unfold word
    rw [List.head?_map, List.head?_range, if_neg (by omega : n ≠ 0)]
    exact congrArg some (hseed E)
  have hwordn : word n o = List.replicate (word n o).length Orient.BG :=
    corner_anchored_word D.toDissection n o (fun m => (E m).1)
      (fun m => edgeEast D.toDissection dir (E m)) α β γ hαpos hγeq hπ
      (fun m hm => (hfrontE m hm).1) (fun m hm => (hfrontE m hm).2) hne
      (fun j hj hBG => tile_orient_BG_east_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
        (E j).1 (E j).2 (hlenE j (by omega)) hBG)
      (fun j hj hGB => by
        simp only
        rw [hjunc j hj]
        exact tile_orient_GB_west_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
          (E (j + 1)).1 (E (j + 1)).2 (hlenE (j + 1) (by omega)) hGB)
      hseed'
  rw [word_length] at hwordn
  rw [hneq] at hwordn
  exact hwordn

/-! ## Per-edge reading: `thm:chain` claim 1, composed

`side_word_constant` gives existence of a chain enumeration whose orientation *word* is constantly
`BG`; that is a fact about a list, not about individual edges. This composes it with
`OrientWord.word_apply` (read a word index) and `tile_orient_BG_east_gamma` (an individual `BG`
edge shows `α` west, `γ` east) to get the per-edge conclusion `thm:chain` claim 1 actually states:
every edge of the chain shows `α` at its west end and `γ` at its east end. -/

open Erdos634.OrientWord Erdos634.Inflation Erdos634.BridgeC Erdos634.WallEndpoints
  Erdos634.WallSide in
/-- **Every edge of a real, seeded `b`-side shows `α` west and `γ` east** — `thm:chain` claim 1,
fully composed from `side_word_constant`'s word-level fact and the per-edge readings. -/
theorem side_alpha_gamma (D : CongruentDissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
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
    (hthird : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection g c,
      g ((D.tile p.1).pts (p.2 + 2)) < c)
    (hlen : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection g c,
      dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = sideOpp D.model 1)
    (hvertt : ∀ j : Fin 3, D.target.pts j = a ∨ D.target.pts j = b ∨ g (D.target.pts j) < c)
    (hseed : ∀ E : ℕ → Fin N × Fin 3,
      Erdos634.OrientBridge.tileOrient D.toDissection α (E 0).1
        (edgeWest D.toDissection dir (E 0)) = Orient.BG) :
    ∃ E : ℕ → Fin N × Fin 3,
      ∀ m < (Erdos634.BaseChain.wallList D.toDissection g c).length,
        (D.tile (E m).1).localAngle (edgeWest D.toDissection dir (E m)) = α ∧
        (D.tile (E m).1).localAngle (edgeEast D.toDissection dir (E m)) = γ := by
  classical
  obtain ⟨E, n, hneq, hn0, hwest0, heastlast, hjunc, hmem, hinj, hlba, hlbend, hnondeg, hsurj⟩ :=
    chain_endpoints hN D.toDissection g c dir hker hwall a b hab hdirab hbase hline hface hthird
  refine ⟨E, ?_⟩
  set o : ℕ → Orient := fun m =>
    Erdos634.OrientBridge.tileOrient D.toDissection α (E m).1 (edgeWest D.toDissection dir (E m))
    with ho
  have hlenE : ∀ m, m < n →
      dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1))
        = sideOpp D.model 1 := fun m hm => hlen (E m) (hmem m hm)
  have hne : ∀ m, m + 1 < n → (E m).1 ≠ (E (m + 1)).1 := by
    intro m hm heq
    have hlin : ∃ y, g y ≠ c := by
      refine ⟨(D.tile (E m).1).pts ((E m).2 + 2), ?_⟩
      have := hthird (E m) (hmem m (by omega)); linarith
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E m)).mp (hmem m (by omega))
    have hwm1 := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E (m + 1))).mp
      (hmem (m + 1) (by omega))
    exact wall_edges_same_tile D.toDissection g c hlin (E m) (E (m + 1))
      (by intro h; exact absurd (hinj m (m + 1) (by omega) (by omega) h) (by omega)) heq hwm hwm1
  have hfrontE : ∀ m, m + 1 < n → edgeEast D.toDissection dir (E m) ∈ frontier D.target.carrier
      ∧ edgeEast D.toDissection dir (E m) ∉ Set.range D.target.pts := by
    intro m hm
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E m)).mp (hmem m (by omega))
    have hp : edgeEast D.toDissection dir (E m) ∈ D.target.carrier :=
      Erdos634.BaseSelection.tile_subset_target D.toDissection (E m).1
        (by unfold edgeEast; split <;> exact subset_convexHull ℝ _ (Set.mem_range_self _))
    have hgp : g (edgeEast D.toDissection dir (E m)) = c :=
      (g_ends D.toDissection g c dir (E m) hwm).2
    have h1 : dir a < Erdos634.OrientBridge.edgePos D.toDissection dir (E (m + 1)) :=
      hlba (m + 1) (by omega) (by omega)
    have h2 : Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m) < dir b := hlbend m hm
    have heq2 : Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m)
        = Erdos634.OrientBridge.edgePos D.toDissection dir (E (m + 1)) := by
      rw [← dir_edgeEast, ← dir_edgeWest, hjunc m hm]
    have hstrict : min (dir a) (dir b) < dir (edgeEast D.toDissection dir (E m)) ∧
        dir (edgeEast D.toDissection dir (E m)) < max (dir a) (dir b) := by
      constructor
      · rw [min_eq_left hdirab, dir_edgeEast, heq2]; exact h1
      · rw [max_eq_right hdirab, dir_edgeEast]; exact h2
    exact junction_frontier_nonvertex D.toDissection g c dir a b hbase hface hvertt hp hgp hstrict
  have hseed' : (word n o).head? = some Orient.BG := by
    unfold word
    rw [List.head?_map, List.head?_range, if_neg (by omega : n ≠ 0)]
    exact congrArg some (hseed E)
  have hwordn : word n o = List.replicate (word n o).length Orient.BG :=
    corner_anchored_word D.toDissection n o (fun m => (E m).1)
      (fun m => edgeEast D.toDissection dir (E m)) α β γ hαpos hγeq hπ
      (fun m hm => (hfrontE m hm).1) (fun m hm => (hfrontE m hm).2) hne
      (fun j hj hBG => tile_orient_BG_east_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
        (E j).1 (E j).2 (hlenE j (by omega)) hBG)
      (fun j hj hGB => by
        simp only
        rw [hjunc j hj]
        exact tile_orient_GB_west_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
          (E (j + 1)).1 (E (j + 1)).2 (hlenE (j + 1) (by omega)) hGB)
      hseed'
  rw [word_length] at hwordn
  intro m hm
  have hmn : m < n := by omega
  have hBG : o m = Orient.BG := word_apply hwordn m hmn
  have hwestα : (D.tile (E m).1).localAngle (edgeWest D.toDissection dir (E m)) = α := by
    by_contra hcon
    simp only [ho, Erdos634.OrientBridge.tileOrient] at hBG
    rw [if_neg hcon] at hBG
    exact absurd hBG (by decide)
  refine ⟨hwestα, ?_⟩
  exact tile_orient_BG_east_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
    (E m).1 (E m).2 (hlenE m hmn) (by simp only [ho] at hBG; exact hBG)

/-! ## `thm:chain` claim 2: the interior junction figure

Every interior junction of a seeded real `b`-side carries a `γ` (from `side_alpha_gamma`'s east
reading). `VertexFigureReal.gamma_boundary_figure_real` already proves that a `γ` at a real
boundary non-vertex point forces the figure `{α,β,γ}` (one tile each, no straight angle) — this was
built for `lem:onegamma`/the march step, not for `thm:chain`, but it is exactly claim 2's statement.
Composing it with the same chain machinery as `side_alpha_gamma` gives claim 2 directly, closing
`thm:chain` in full. -/

open Erdos634.OrientWord Erdos634.Inflation Erdos634.BridgeC Erdos634.WallEndpoints
  Erdos634.WallSide Erdos634.VertexFigureReal in
/-- **Every interior junction of a seeded real `b`-side is a genuine `(α,β,γ)` π-vertex** —
`thm:chain` claim 2, composed from `side_alpha_gamma`'s per-edge `γ` reading and
`VertexFigureReal.gamma_boundary_figure_real`. -/
theorem side_junction_figure (D : CongruentDissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαpos : 0 < α) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγeq : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hN : 0 < N) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b) (hdirab : dir a ≤ dir b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hthird : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection g c,
      g ((D.tile p.1).pts (p.2 + 2)) < c)
    (hlen : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection g c,
      dist ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) = sideOpp D.model 1)
    (hvertt : ∀ j : Fin 3, D.target.pts j = a ∨ D.target.pts j = b ∨ g (D.target.pts j) < c)
    (hseed : ∀ E : ℕ → Fin N × Fin 3,
      Erdos634.OrientBridge.tileOrient D.toDissection α (E 0).1
        (edgeWest D.toDissection dir (E 0)) = Orient.BG) :
    ∃ E : ℕ → Fin N × Fin 3,
      ∀ m, m + 1 < (Erdos634.BaseChain.wallList D.toDissection g c).length →
        ({i | (D.tile i).localAngle (edgeEast D.toDissection dir (E m)) = α} :
          Finset (Fin N)).card = 1 ∧
        ({i | (D.tile i).localAngle (edgeEast D.toDissection dir (E m)) = β} :
          Finset (Fin N)).card = 1 ∧
        ({i | (D.tile i).localAngle (edgeEast D.toDissection dir (E m)) = γ} :
          Finset (Fin N)).card = 1 ∧
        ({i | (D.tile i).localAngle (edgeEast D.toDissection dir (E m)) = Real.pi} :
          Finset (Fin N)).card = 0 := by
  classical
  obtain ⟨E, n, hneq, hn0, hwest0, heastlast, hjunc, hmem, hinj, hlba, hlbend, hnondeg, hsurj⟩ :=
    chain_endpoints hN D.toDissection g c dir hker hwall a b hab hdirab hbase hline hface hthird
  refine ⟨E, ?_⟩
  have hfrontE : ∀ m, m + 1 < n → edgeEast D.toDissection dir (E m) ∈ frontier D.target.carrier
      ∧ edgeEast D.toDissection dir (E m) ∉ Set.range D.target.pts := by
    intro m hm
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E m)).mp (hmem m (by omega))
    have hp : edgeEast D.toDissection dir (E m) ∈ D.target.carrier :=
      Erdos634.BaseSelection.tile_subset_target D.toDissection (E m).1
        (by unfold edgeEast; split <;> exact subset_convexHull ℝ _ (Set.mem_range_self _))
    have hgp : g (edgeEast D.toDissection dir (E m)) = c :=
      (g_ends D.toDissection g c dir (E m) hwm).2
    have h1 : dir a < Erdos634.OrientBridge.edgePos D.toDissection dir (E (m + 1)) :=
      hlba (m + 1) (by omega) (by omega)
    have h2 : Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m) < dir b := hlbend m hm
    have heq2 : Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m)
        = Erdos634.OrientBridge.edgePos D.toDissection dir (E (m + 1)) := by
      rw [← dir_edgeEast, ← dir_edgeWest, hjunc m hm]
    have hstrict : min (dir a) (dir b) < dir (edgeEast D.toDissection dir (E m)) ∧
        dir (edgeEast D.toDissection dir (E m)) < max (dir a) (dir b) := by
      constructor
      · rw [min_eq_left hdirab, dir_edgeEast, heq2]; exact h1
      · rw [max_eq_right hdirab, dir_edgeEast]; exact h2
    exact junction_frontier_nonvertex D.toDissection g c dir a b hbase hface hvertt hp hgp hstrict
  have hlenE : ∀ m, m < n →
      dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1))
        = sideOpp D.model 1 := fun m hm => hlen (E m) (hmem m hm)
  set o : ℕ → Orient := fun m =>
    Erdos634.OrientBridge.tileOrient D.toDissection α (E m).1 (edgeWest D.toDissection dir (E m))
    with ho
  have hne : ∀ m, m + 1 < n → (E m).1 ≠ (E (m + 1)).1 := by
    intro m hm heq
    have hlin : ∃ y, g y ≠ c := by
      refine ⟨(D.tile (E m).1).pts ((E m).2 + 2), ?_⟩
      have := hthird (E m) (hmem m (by omega)); linarith
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E m)).mp (hmem m (by omega))
    have hwm1 := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E (m + 1))).mp
      (hmem (m + 1) (by omega))
    exact wall_edges_same_tile D.toDissection g c hlin (E m) (E (m + 1))
      (by intro h; exact absurd (hinj m (m + 1) (by omega) (by omega) h) (by omega)) heq hwm hwm1
  have hseed' : (word n o).head? = some Orient.BG := by
    unfold word
    rw [List.head?_map, List.head?_range, if_neg (by omega : n ≠ 0)]
    exact congrArg some (hseed E)
  have hwordn : word n o = List.replicate (word n o).length Orient.BG :=
    corner_anchored_word D.toDissection n o (fun m => (E m).1)
      (fun m => edgeEast D.toDissection dir (E m)) α β γ hαpos hγeq hπ
      (fun m hm => (hfrontE m hm).1) (fun m hm => (hfrontE m hm).2) hne
      (fun j hj hBG => tile_orient_BG_east_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
        (E j).1 (E j).2 (hlenE j (by omega)) hBG)
      (fun j hj hGB => by
        simp only
        rw [hjunc j hj]
        exact tile_orient_GB_west_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
          (E (j + 1)).1 (E (j + 1)).2 (hlenE (j + 1) (by omega)) hGB)
      hseed'
  rw [word_length] at hwordn
  intro m hm0
  have hm : m + 1 < n := by omega
  have hmn : m < n := by omega
  have hBG : o m = Orient.BG := word_apply hwordn m hmn
  have hγatv : (D.tile (E m).1).localAngle (edgeEast D.toDissection dir (E m)) = γ :=
    tile_orient_BG_east_gamma D α β γ hα' hβ' hγ' hscalene hαβ hαγ hβγ dir
      (E m).1 (E m).2 (hlenE m (by omega)) (by simp only [ho] at hBG; exact hBG)
  have hcorners := Erdos634.Geometry.Dissection.congruentDissection_hcorners D α β γ hα' hβ' hγ'
  have hvals : ∀ i, (D.tile i).localAngle (edgeEast D.toDissection dir (E m)) ∈
      ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => localAngle_mem D.toDissection α β γ (hfrontE m hm).1 (hfrontE m hm).2 hcorners i
  obtain ⟨ha, hbeta, hgam, hpi⟩ := gamma_boundary_figure_real D.toDissection hαβ hαγ hαπ hα0
    hβγ hβπ hβ0 hγπ hγ0 hπ0 hγeq hπ hirr (hfrontE m hm).1 (hfrontE m hm).2 hvals (E m).1 hγatv
  exact ⟨ha, hbeta, hgam, hpi⟩

end Erdos634.BEdgeReading
