import Mathlib
import Erdos634.BaseChain
import Erdos634.WallInjective
import Erdos634.Placement

/-!
# Bridge (c): the base chain's junctions, as a theorem about a dissection

Erdős #634.  Everything the chain needed is now proved separately; this file threads it.

* `BaseChain.base_chain_reach` — no gap between consecutive edges;
* `WallInjective.shadows_disjoint` — no overlap;
* `Placement.contiguous_of_no_gap` — hence consecutive shadows share an endpoint;
* `Placement.shared_junction` with `WallInjective.dir_injOn_wall` — hence the *points* coincide.

The conclusion is the incidence `OrientWord.word_isChain` asks for: the east end of each chain edge
is the west end of the next.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BridgeC

open Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.BaseChain
open Erdos634.Placement Erdos634.WallInjective Set

/-- Both ends of a wall edge lie on the wall. -/
theorem g_ends {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (dir : Plane →ₗ[ℝ] ℝ)
    (p : Fin N × Fin 3) (hp : Erdos634.WallEdges.WallEdge D g c p) :
    g (edgeWest D dir p) = c ∧ g (edgeEast D dir p) = c := by
  classical
  unfold edgeWest edgeEast
  split <;> exact ⟨by first | exact hp.1 | exact hp.2, by first | exact hp.2 | exact hp.1⟩

/-- **The chain's junctions.**  Enumerating the wall edges in order of `edgePos`, the east end of
each edge is the west end of the next. -/
theorem chain_junctions {N : ℕ} (hN : 0 < N) (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hthird : ∀ p ∈ wallList D g c, g ((D.tile p.1).pts (p.2 + 2)) < c) :
    ∃ E : ℕ → Fin N × Fin 3, ∀ k, k + 1 < (wallList D g c).length →
      edgeEast D dir (E k) = edgeWest D dir (E (k + 1)) := by
  classical
  haveI : Inhabited (Fin N × Fin 3) := ⟨(⟨0, hN⟩, 0)⟩
  obtain ⟨E, hmono, hmem, hsurj, hinj⟩ :=
    Erdos634.ChainEnum.exists_sorted_enum (wallList D g c) (fun p => edgePos D dir p)
      (wallList_nodup D g c)
  set n := (wallList D g c).length with hn
  refine ⟨E, fun k hk1 => ?_⟩
  -- the wall functional is not constant, since some third vertex is strictly inside
  have hlin : ∃ y, g y ≠ c := by
    refine ⟨(D.tile (E k).1).pts ((E k).2 + 2), ?_⟩
    have := hthird (E k) (hmem k (by omega))
    linarith
  -- the shadows are nondegenerate
  have hnondeg : ∀ j, j < n → edgePos D dir (E j) < edgeEnd D dir (E j) := by
    intro j hj
    have hw := (mem_wallList D g c (E j)).mp (hmem j hj)
    exact shadow_nondegenerate D g dir c hker (E j).1 (E j).2 hw.1 hw.2
  -- and they do not overlap
  have hnoov : ∀ i j, i < j → j < n → edgeEnd D dir (E i) ≤ edgePos D dir (E j) := by
    intro i j hij hj
    have hi : i < n := lt_trans hij hj
    have hwi := (mem_wallList D g c (E i)).mp (hmem i hi)
    have hwj := (mem_wallList D g c (E j)).mp (hmem j hj)
    have hne : E i ≠ E j := fun h => absurd (hinj i j hi hj h) (Nat.ne_of_lt hij)
    have htile : (E i).1 ≠ (E j).1 := by
      intro h
      exact Erdos634.WallSide.wall_edges_same_tile D g c hlin (E i) (E j) hne h hwi hwj
    have hdisj := shadows_disjoint D g dir c hker (E i).1 (E j).1 htile (E i).2 (E j).2
      hwi.1 hwi.2 (hthird (E i) (hmem i hi)) hwj.1 hwj.2 (hthird (E j) (hmem j hj))
    rcases hdisj with h | h
    · exact h
    · exact absurd h (not_le.mpr (lt_of_le_of_lt (hmono i j (le_of_lt hij) hj) (hnondeg j hj)))
  -- no gap
  have hreach := base_chain_reach D g c dir hwall a b hab hbase hline hface E hmono hmem hsurj k hk1
  -- hence the shadows abut
  have hcontig : edgeEnd D dir (E k) = edgePos D dir (E (k + 1)) :=
    contiguous_of_no_gap (fun j => edgePos D dir (E j)) (fun j => edgeEnd D dir (E j)) n k hk1
      (fun j hj => edgePos_le_edgeEnd D dir (E j)) (fun i j hij hj => hmono i j hij hj) hnoov
      hreach
  -- and the points coincide
  have hwk := (mem_wallList D g c (E k)).mp (hmem k (by omega))
  have hwk1 := (mem_wallList D g c (E (k + 1))).mp (hmem (k + 1) hk1)
  exact shared_junction D dir {y : Plane | g y = c} (dir_injOn_wall g dir c hker) (E k) (E (k + 1))
    ((g_ends D g c dir (E k) hwk).2) ((g_ends D g c dir (E (k + 1)) hwk1).1) hcontig

/-! ## The junction is a non-vertex point of the frontier

`OrientWord.word_isChain` asks, at each junction, for a point of the target's frontier that is not
a vertex of the target.  The junction is on the base, hence on the frontier; and it is strictly
inside the base's shadow, hence neither endpoint — while the target's third vertex is off the wall
altogether. -/

/-- **The junction is a non-vertex frontier point.**  `hstrict` says the junction's coordinate is
strictly between the base's endpoints, which is what the ordering supplies; `hvert` says the
target's vertices are the base's two endpoints and one point strictly inside the half-plane, which
is what makes the base a side. -/
theorem junction_frontier_nonvertex {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (a b : Plane)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hvert : ∀ j : Fin 3, D.target.pts j = a ∨ D.target.pts j = b ∨ g (D.target.pts j) < c)
    {p : Plane} (hp : p ∈ D.target.carrier) (hgp : g p = c)
    (hstrict : min (dir a) (dir b) < dir p ∧ dir p < max (dir a) (dir b)) :
    p ∈ frontier D.target.carrier ∧ p ∉ Set.range D.target.pts := by
  refine ⟨hbase (hface p hp hgp), ?_⟩
  rintro ⟨j, hj⟩
  rcases hvert j with h | h | h
  · rw [h] at hj
    rw [← hj] at hstrict
    rcases hstrict with ⟨h1, h2⟩
    rcases le_total (dir a) (dir b) with hle | hle
    · rw [min_eq_left hle] at h1; exact absurd rfl (ne_of_lt h1)
    · rw [max_eq_left hle] at h2; exact absurd rfl (ne_of_lt h2)
  · rw [h] at hj
    rw [← hj] at hstrict
    rcases hstrict with ⟨h1, h2⟩
    rcases le_total (dir a) (dir b) with hle | hle
    · rw [max_eq_right hle] at h2; exact absurd rfl (ne_of_lt h2)
    · rw [min_eq_right hle] at h1; exact absurd rfl (ne_of_lt h1)
  · rw [hj] at h; exact absurd hgp (ne_of_lt h)

end Erdos634.BridgeC
