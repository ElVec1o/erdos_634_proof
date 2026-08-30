import Mathlib
import Erdos634.ChainEnum

/-!
# The base chain of a dissection: its edges, in order, meet

Erdős #634, bridge (c), assembled.  The pieces proved separately —

* `WallEdges.base_covered_by_wall_edges`, the base covered by edges lying along it;
* `ShadowCover.shadow_cover`, the same covering one level down, as intervals;
* `ChainEnum.exists_sorted_enum`, an enumeration nondecreasing in `edgePos`;
* `ChainInstance.consecutive_edges_meet`, the no-gap property of a sorted interval cover;

— join here into a statement about a dissection: enumerating the wall edges in order of their
`edgePos`, one of the first `k+1` reaches the `(k+1)`-st edge's key.  There is no uncovered stretch
of the base between consecutive edges of the chain.

The hypothesis `hface` says the wall line meets the target exactly in the base, which is what makes
the base a side of the target rather than an arbitrary segment of its frontier.  It is a property
of the target triangle, not of the dissection.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BaseChain

open Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance Set

/-- The wall edges of a dissection, as a list. -/
noncomputable def wallList {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) :
    List (Fin N × Fin 3) :=
  open Classical in
  (Finset.univ : Finset (Fin N × Fin 3)).toList.filter
    (fun p => decide (Erdos634.WallEdges.WallEdge D g c p))

theorem wallList_nodup {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) :
    (wallList D g c).Nodup := by
  classical
  exact List.Nodup.filter _ (Finset.univ.nodup_toList)

theorem mem_wallList {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (p : Fin N × Fin 3) : p ∈ wallList D g c ↔ Erdos634.WallEdges.WallEdge D g c p := by
  classical
  simp [wallList, List.mem_filter]

/-- **The reach property for a given enumeration.**  The content of
`base_chain_consecutive_meet`, stated for an enumeration supplied by the caller so that the same
`E` can be reused downstream. -/
theorem base_chain_reach {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (E : ℕ → Fin N × Fin 3)
    (hmono : ∀ i j, i ≤ j → j < (wallList D g c).length →
      edgePos D dir (E i) ≤ edgePos D dir (E j))
    (hmem : ∀ i < (wallList D g c).length, E i ∈ wallList D g c)
    (hsurj : ∀ x ∈ wallList D g c, ∃ i < (wallList D g c).length, E i = x)
    (k : ℕ) (hk1 : k + 1 < (wallList D g c).length) :
    ∃ j ≤ k, edgePos D dir (E (k + 1)) ≤ edgeEnd D dir (E j) := by
  classical
  set n := (wallList D g c).length with hn
  have hedge_sub : ∀ p : Fin N × Fin 3, p ∈ wallList D g c →
      dir '' ((D.tile p.1).edge p.2) ⊆ uIcc (dir a) (dir b) := by
    intro p hp
    have hw := (mem_wallList D g c p).mp hp
    have himg : dir '' (segment ℝ a b) = uIcc (dir a) (dir b) := by
      have h := image_segment ℝ dir.toAffineMap a b
      simp only [LinearMap.coe_toAffineMap] at h
      rw [h, segment_eq_uIcc]
    rw [← himg]
    rintro y ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    have hxt : x ∈ (D.tile p.1).carrier :=
      (D.tile p.1).edge_subset_carrier p.2 (by rw [Tri.edge]; exact hx)
    have hxc : g x = c := by
      obtain ⟨u, v, hu, hv, huv, rfl⟩ := hx
      have hx' : u • (D.tile p.1).pts p.2 + v • (D.tile p.1).pts (p.2 + 1)
          = AffineMap.lineMap ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2+1)) v := by
        rw [AffineMap.lineMap_apply]
        simp only [vsub_eq_sub, vadd_eq_add, smul_sub]
        have : u = 1 - v := by linarith
        rw [this]; module
      rw [hx', AffineMap.apply_lineMap, hw.1, hw.2]
      simp
    exact hface x (Erdos634.BaseSelection.tile_subset_target D p.1 hxt) hxc
  refine Erdos634.ChainInstance.consecutive_edges_meet D dir n E (dir a ⊓ dir b) (dir a ⊔ dir b)
    k hk1 ?_ ?_ (fun i j hij hj => hmono i j hij hj)
  · have hcov := Erdos634.ShadowCover.shadow_cover D g c dir hwall a b hab hbase hline
    rw [uIcc] at hcov
    intro y hy
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hcov hy)
    obtain ⟨i, hi, rfl⟩ := hsurj p ((mem_wallList D g c p).mpr hp)
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hi, by
      rw [edge_image_eq_Icc]; exact hyp⟩
  · intro j hj
    have := hedge_sub (E j) (hmem j hj)
    rwa [uIcc] at this

/-- **The base chain's consecutive edges meet.**  With the wall edges enumerated in order of
`edgePos`, one of the first `k+1` reaches the next edge's key. -/
theorem base_chain_consecutive_meet {N : ℕ} (hN : 0 < N) (D : Dissection N)
    (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (dir : Plane →ₗ[ℝ] ℝ)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b) :
    ∃ E : ℕ → Fin N × Fin 3, ∀ k, k + 1 < (wallList D g c).length →
      ∃ j ≤ k, edgePos D dir (E (k + 1)) ≤ edgeEnd D dir (E j) := by
  classical
  haveI : Inhabited (Fin N × Fin 3) := ⟨(⟨0, hN⟩, 0)⟩
  obtain ⟨E, hmono, hmem, hsurj, _hinj⟩ :=
    Erdos634.ChainEnum.exists_sorted_enum (wallList D g c) (fun p => edgePos D dir p)
      (wallList_nodup D g c)
  exact ⟨E, fun k hk1 =>
    base_chain_reach D g c dir hwall a b hab hbase hline hface E hmono hmem hsurj k hk1⟩

end Erdos634.BaseChain
