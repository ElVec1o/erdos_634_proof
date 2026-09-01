import Erdos634.BaseChain
import Erdos634.WallInjective
import Erdos634.Placement
import Erdos634.BridgeC

/-!
# The wall chain's first edge starts exactly at the named corner

Erdős #634, bridge (c), the last piece.  `BaseChain.base_chain_consecutive_meet` gives the
internal incidences of the sorted wall-edge enumeration; nothing so far says the *enumeration
itself* begins at `a` — the segment's own named endpoint, which is what `lem:endpoints` and the
inductive step of `prop:gammatrap` both actually need.

The argument: `a` is covered by some wall edge (`WallEdges.base_covered_by_wall_edges`), and every
wall edge's shadow sits inside `[dir a, dir b]`. The covering edge's west end therefore has
`dir`-value `≥ dir a`, but it also contains `a` itself in its shadow, forcing the west end's value
to equal `dir a` exactly. `dir` is injective on the wall (`WallInjective.dir_injOn_wall`), so the
point itself is `a`. Sortedness plus `WallInjective.shadows_disjoint` then pin the covering edge to
index `0`: a different index with the same west value would overlap it.

`hthird` is the same third-vertex-strictness hypothesis `BridgeC.chain_junctions` already carries;
it is not re-derived here, only reused.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.WallEndpoints

open Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.BaseChain
open Erdos634.Placement Erdos634.WallInjective Set

/-- **Every wall edge's shadow sits inside `[dir a, dir b]`.** -/
theorem shadow_subset_Icc {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane)
    (hdirab : dir a ≤ dir b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (p : Fin N × Fin 3) (hp : Erdos634.WallEdges.WallEdge D g c p) :
    dir '' ((D.tile p.1).edge p.2) ⊆ Icc (dir a) (dir b) := by
  have himg : dir '' (segment ℝ a b) = Icc (dir a) (dir b) := by
    have h := image_segment ℝ dir.toAffineMap a b
    simp only [LinearMap.coe_toAffineMap] at h
    rw [h, segment_eq_uIcc, uIcc_of_le hdirab]
  rw [← himg]
  rintro y ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  have hxt : x ∈ (D.tile p.1).carrier :=
    (D.tile p.1).edge_subset_carrier p.2 (by rw [Tri.edge]; exact hx)
  have hxc : g x = c := by
    obtain ⟨u, v, hu, hv, huv, rfl⟩ := hx
    have hx' : u • (D.tile p.1).pts p.2 + v • (D.tile p.1).pts (p.2 + 1)
        = AffineMap.lineMap ((D.tile p.1).pts p.2) ((D.tile p.1).pts (p.2 + 1)) v := by
      rw [AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, smul_sub]
      have : u = 1 - v := by linarith
      rw [this]; module
    rw [hx', AffineMap.apply_lineMap, hp.1, hp.2]
    simp
  exact hface x (Erdos634.BaseSelection.tile_subset_target D p.1 hxt) hxc

/-- **The sorted chain's first entry starts exactly at `a`.** -/
theorem chain_starts_at_a {N : ℕ} (hN : 0 < N) (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hdirab : dir a ≤ dir b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hthird : ∀ p ∈ wallList D g c, g ((D.tile p.1).pts (p.2 + 2)) < c) :
    ∃ E : ℕ → Fin N × Fin 3, 0 < (wallList D g c).length ∧ edgeWest D dir (E 0) = a := by
  classical
  haveI : Inhabited (Fin N × Fin 3) := ⟨(⟨0, hN⟩, 0)⟩
  obtain ⟨E, hmono, hmem, hsurj, hinj⟩ :=
    Erdos634.ChainEnum.exists_sorted_enum (wallList D g c) (fun p => edgePos D dir p)
      (wallList_nodup D g c)
  -- `a` is covered by some wall edge
  have hacov := Erdos634.WallEdges.base_covered_by_wall_edges D g c hwall a b hab hbase hline
    (left_mem_segment ℝ a b)
  simp only [mem_iUnion, mem_setOf_eq] at hacov
  obtain ⟨p, hp, hap⟩ := hacov
  obtain ⟨i, hilt, rfl⟩ := hsurj p ((mem_wallList D g c p).mpr hp)
  have hn0 : 0 < (wallList D g c).length := lt_of_le_of_lt (Nat.zero_le i) hilt
  refine ⟨E, hn0, ?_⟩
  have hwi := (mem_wallList D g c (E i)).mp (hmem i hilt)
  have hndi : edgePos D dir (E i) < edgeEnd D dir (E i) :=
    shadow_nondegenerate D g dir c hker (E i).1 (E i).2 hwi.1 hwi.2
  -- the global lower bound: every edge's west value is `≥ dir a`
  have hlb : ∀ j < (wallList D g c).length, dir a ≤ edgePos D dir (E j) := by
    intro j hj
    have hwj := (mem_wallList D g c (E j)).mp (hmem j hj)
    have hndj : edgePos D dir (E j) < edgeEnd D dir (E j) :=
      shadow_nondegenerate D g dir c hker (E j).1 (E j).2 hwj.1 hwj.2
    have hsub := shadow_subset_Icc D g c dir hwall a b hdirab hbase hline hface (E j) hwj
    have hmemIcc : edgePos D dir (E j) ∈ dir '' ((D.tile (E j).1).edge (E j).2) := by
      rw [edge_image_eq_Icc]; exact ⟨le_refl _, hndj.le⟩
    exact (hsub hmemIcc).1
  -- `a`'s own edge has west-value exactly `dir a`
  have hap_dir : dir a ∈ dir '' ((D.tile (E i).1).edge (E i).2) := ⟨a, hap, rfl⟩
  have hsub_i := shadow_subset_Icc D g c dir hwall a b hdirab hbase hline hface (E i) hwi
  rw [edge_image_eq_Icc] at hap_dir
  have heqpos : edgePos D dir (E i) = dir a := le_antisymm hap_dir.1 (hlb i hilt)
  -- `dir` is injective on the wall, so the west endpoint of `E i` equals `a` itself
  have hwmem : (edgeWest D dir (E i)) ∈ {y : Plane | g y = c} := by
    unfold edgeWest
    split
    · exact hwi.1
    · exact hwi.2
  have hamem : a ∈ {y : Plane | g y = c} := hline a (left_mem_segment ℝ a b)
  have hdireq : dir (edgeWest D dir (E i)) = dir a := by
    rw [dir_edgeWest]; exact heqpos
  have hweq : edgeWest D dir (E i) = a :=
    dir_injOn_wall g dir c hker hwmem hamem hdireq
  -- sortedness pins the index to `0`
  have hi0 : i = 0 := by
    by_contra hine
    have h0i : edgePos D dir (E 0) ≤ edgePos D dir (E i) := hmono 0 i (Nat.zero_le i) hilt
    have h0lb := hlb 0 hn0
    rw [heqpos] at h0i
    have heq0 : edgePos D dir (E 0) = dir a := le_antisymm h0i h0lb
    have hne : E 0 ≠ E i := by
      intro heq
      exact hine (hinj 0 i hn0 hilt heq).symm
    have hw0 := (mem_wallList D g c (E 0)).mp (hmem 0 hn0)
    have ht0 := hthird (E 0) (hmem 0 hn0)
    have hti := hthird (E i) (hmem i hilt)
    have htne : (E 0).1 ≠ (E i).1 :=
      fun h => Erdos634.WallSide.wall_edges_same_tile D g c
        ⟨(D.tile (E i).1).pts ((E i).2 + 2), ne_of_lt hti⟩ (E 0) (E i) hne h hw0 hwi
    have hnd0 : edgePos D dir (E 0) < edgeEnd D dir (E 0) :=
      shadow_nondegenerate D g dir c hker (E 0).1 (E 0).2 hw0.1 hw0.2
    have hd := shadows_disjoint D g dir c hker (E 0).1 (E i).1 htne (E 0).2 (E i).2
      hw0.1 hw0.2 ht0 hwi.1 hwi.2 hti
    rcases hd with h | h
    · rw [heq0] at hnd0; rw [heqpos] at h; linarith
    · rw [heqpos] at hndi; rw [heq0] at h; linarith
  rw [hi0] at hweq
  exact hweq

/-- **The sorted chain's last entry ends exactly at `b`.**  Mirror of `chain_starts_at_a`, using
`right_mem_segment` and the global *upper* bound instead of the lower one, and pinning the index
to `n − 1` (the last valid index, `hn0.le` needed for `n - 1 < n`) instead of `0`. -/
theorem chain_ends_at_b {N : ℕ} (hN : 0 < N) (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hdirab : dir a ≤ dir b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hthird : ∀ p ∈ wallList D g c, g ((D.tile p.1).pts (p.2 + 2)) < c) :
    ∃ E : ℕ → Fin N × Fin 3, ∃ n : ℕ, n = (wallList D g c).length ∧ 0 < n ∧
      edgeEast D dir (E (n - 1)) = b := by
  classical
  haveI : Inhabited (Fin N × Fin 3) := ⟨(⟨0, hN⟩, 0)⟩
  obtain ⟨E, hmono, hmem, hsurj, hinj⟩ :=
    Erdos634.ChainEnum.exists_sorted_enum (wallList D g c) (fun p => edgePos D dir p)
      (wallList_nodup D g c)
  set n := (wallList D g c).length with hn
  have hbcov := Erdos634.WallEdges.base_covered_by_wall_edges D g c hwall a b hab hbase hline
    (right_mem_segment ℝ a b)
  simp only [mem_iUnion, mem_setOf_eq] at hbcov
  obtain ⟨p, hp, hbp⟩ := hbcov
  obtain ⟨i, hilt, rfl⟩ := hsurj p ((mem_wallList D g c p).mpr hp)
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hilt
  refine ⟨E, n, rfl, hn0, ?_⟩
  have hwi := (mem_wallList D g c (E i)).mp (hmem i hilt)
  have hndi : edgePos D dir (E i) < edgeEnd D dir (E i) :=
    shadow_nondegenerate D g dir c hker (E i).1 (E i).2 hwi.1 hwi.2
  -- the global upper bound: every edge's east value is `≤ dir b`
  have hub : ∀ j < n, edgeEnd D dir (E j) ≤ dir b := by
    intro j hj
    have hwj := (mem_wallList D g c (E j)).mp (hmem j hj)
    have hndj : edgePos D dir (E j) < edgeEnd D dir (E j) :=
      shadow_nondegenerate D g dir c hker (E j).1 (E j).2 hwj.1 hwj.2
    have hsub := shadow_subset_Icc D g c dir hwall a b hdirab hbase hline hface (E j) hwj
    have hmemIcc : edgeEnd D dir (E j) ∈ dir '' ((D.tile (E j).1).edge (E j).2) := by
      rw [edge_image_eq_Icc]; exact ⟨hndj.le, le_refl _⟩
    exact (hsub hmemIcc).2
  -- `b`'s own edge has east-value exactly `dir b`
  have hbp_dir : dir b ∈ dir '' ((D.tile (E i).1).edge (E i).2) := ⟨b, hbp, rfl⟩
  rw [edge_image_eq_Icc] at hbp_dir
  have heqend : edgeEnd D dir (E i) = dir b := le_antisymm (hub i hilt) hbp_dir.2
  -- `dir` is injective on the wall, so the east endpoint of `E i` equals `b` itself
  have hwmem : (edgeEast D dir (E i)) ∈ {y : Plane | g y = c} := by
    unfold edgeEast
    split
    · exact hwi.2
    · exact hwi.1
  have hbmem : b ∈ {y : Plane | g y = c} := hline b (right_mem_segment ℝ a b)
  have hdireq : dir (edgeEast D dir (E i)) = dir b := by
    rw [dir_edgeEast]; exact heqend
  have hbeq : edgeEast D dir (E i) = b :=
    dir_injOn_wall g dir c hker hwmem hbmem hdireq
  -- sortedness pins the index to `n − 1`: any later index would force a degenerate edge
  have hi1 : i = n - 1 := by
    by_contra hine
    have hilt' : i < n - 1 := by
      have : i ≤ n - 1 := by omega
      omega
    have hjlt : n - 1 < n := by omega
    have hij : i ≤ n - 1 := le_of_lt hilt'
    have hwj := (mem_wallList D g c (E (n - 1))).mp (hmem (n - 1) hjlt)
    have htj := hthird (E (n - 1)) (hmem (n - 1) hjlt)
    have hti := hthird (E i) (hmem i hilt)
    have hne : E i ≠ E (n - 1) := by
      intro heq
      have := hinj i (n - 1) hilt hjlt heq
      omega
    have htne : (E i).1 ≠ (E (n - 1)).1 :=
      fun h => Erdos634.WallSide.wall_edges_same_tile D g c
        ⟨(D.tile (E i).1).pts ((E i).2 + 2), ne_of_lt hti⟩ (E i) (E (n - 1)) hne h hwi hwj
    have hndj : edgePos D dir (E (n - 1)) < edgeEnd D dir (E (n - 1)) :=
      shadow_nondegenerate D g dir c hker (E (n - 1)).1 (E (n - 1)).2 hwj.1 hwj.2
    have hposj_le : edgePos D dir (E (n - 1)) ≤ dir b := hub (n - 1) hjlt |>.trans' hndj.le
    have hmonoij : edgePos D dir (E i) ≤ edgePos D dir (E (n - 1)) := hmono i (n - 1) hij hjlt
    have hd := shadows_disjoint D g dir c hker (E i).1 (E (n - 1)).1 htne (E i).2 (E (n - 1)).2
      hwi.1 hwi.2 hti hwj.1 hwj.2 htj
    rcases hd with h | h
    · -- `edgeEnd (E i) ≤ edgePos (E (n-1))`; with `edgeEnd (E i) = dir b` and the global bound
      -- this forces `edgePos (E (n-1)) = dir b = edgeEnd (E (n-1))`, contradicting nondegeneracy
      rw [heqend] at h
      have hle := hub (n - 1) hjlt
      linarith [hndj, h, hle]
    · -- `edgeEnd (E (n-1)) ≤ edgePos (E i)`; with monotonicity `edgePos (E i) ≤ edgePos (E (n-1))`
      -- and nondegeneracy `edgePos (E (n-1)) < edgeEnd (E (n-1))` this is a direct contradiction
      linarith [hmonoij, hndj]
  rw [hi1] at hbeq
  exact hbeq

/-- **Both endpoints of the chain at once**, for the same enumeration `E`. Combines
`chain_starts_at_a` and `chain_ends_at_b` — separately they each build their own choice of `E` via
`exists_sorted_enum`, which are equal in value but not syntactically the same term; this version
builds `E` once so a caller who needs both facts about *one* `E` has them. -/
theorem chain_endpoints {N : ℕ} (hN : 0 < N) (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hdirab : dir a ≤ dir b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hthird : ∀ p ∈ wallList D g c, g ((D.tile p.1).pts (p.2 + 2)) < c) :
    ∃ E : ℕ → Fin N × Fin 3, ∃ n : ℕ, n = (wallList D g c).length ∧ 0 < n ∧
      edgeWest D dir (E 0) = a ∧ edgeEast D dir (E (n - 1)) = b ∧
      (∀ m, m + 1 < n → edgeEast D dir (E m) = edgeWest D dir (E (m + 1))) ∧
      (∀ m, m < n → E m ∈ wallList D g c) ∧
      (∀ m1 m2, m1 < n → m2 < n → E m1 = E m2 → m1 = m2) ∧
      (∀ m, 0 < m → m < n → dir a < edgePos D dir (E m)) ∧
      (∀ m, m + 1 < n → edgeEnd D dir (E m) < dir b) ∧
      (∀ m, m < n → edgePos D dir (E m) < edgeEnd D dir (E m)) := by
  classical
  haveI : Inhabited (Fin N × Fin 3) := ⟨(⟨0, hN⟩, 0)⟩
  obtain ⟨E, hmono, hmem, hsurj, hinj⟩ :=
    Erdos634.ChainEnum.exists_sorted_enum (wallList D g c) (fun p => edgePos D dir p)
      (wallList_nodup D g c)
  set n := (wallList D g c).length with hn
  -- `a`'s side, exactly as in `chain_starts_at_a`
  have hacov := Erdos634.WallEdges.base_covered_by_wall_edges D g c hwall a b hab hbase hline
    (left_mem_segment ℝ a b)
  simp only [mem_iUnion, mem_setOf_eq] at hacov
  obtain ⟨pa, hpa, hap⟩ := hacov
  obtain ⟨ia, hialt, hiaeq⟩ := hsurj pa ((mem_wallList D g c pa).mpr hpa)
  subst hiaeq
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le ia) hialt
  have hwia := hpa
  have hndia : edgePos D dir (E ia) < edgeEnd D dir (E ia) :=
    shadow_nondegenerate D g dir c hker (E ia).1 (E ia).2 hwia.1 hwia.2
  have hlb : ∀ j < n, dir a ≤ edgePos D dir (E j) := by
    intro j hj
    have hwj := (mem_wallList D g c (E j)).mp (hmem j hj)
    have hndj : edgePos D dir (E j) < edgeEnd D dir (E j) :=
      shadow_nondegenerate D g dir c hker (E j).1 (E j).2 hwj.1 hwj.2
    have hsub := shadow_subset_Icc D g c dir hwall a b hdirab hbase hline hface (E j) hwj
    have hmemIcc : edgePos D dir (E j) ∈ dir '' ((D.tile (E j).1).edge (E j).2) := by
      rw [edge_image_eq_Icc]; exact ⟨le_refl _, hndj.le⟩
    exact (hsub hmemIcc).1
  have hap_dir : dir a ∈ dir '' ((D.tile (E ia).1).edge (E ia).2) := ⟨a, hap, rfl⟩
  rw [edge_image_eq_Icc] at hap_dir
  have heqpos : edgePos D dir (E ia) = dir a := le_antisymm hap_dir.1 (hlb ia hialt)
  have hwmema : edgeWest D dir (E ia) ∈ {y : Plane | g y = c} := by
    unfold edgeWest; split
    · exact hwia.1
    · exact hwia.2
  have hameme : a ∈ {y : Plane | g y = c} := hline a (left_mem_segment ℝ a b)
  have hdireqa : dir (edgeWest D dir (E ia)) = dir a := by rw [dir_edgeWest]; exact heqpos
  have hweqa : edgeWest D dir (E ia) = a := dir_injOn_wall g dir c hker hwmema hameme hdireqa
  have hia0 : ia = 0 := by
    by_contra hine
    have h0i : edgePos D dir (E 0) ≤ edgePos D dir (E ia) := hmono 0 ia (Nat.zero_le ia) hialt
    have h0lb := hlb 0 hn0
    rw [heqpos] at h0i
    have heq0 : edgePos D dir (E 0) = dir a := le_antisymm h0i h0lb
    have hne : E 0 ≠ E ia := by
      intro heq; exact hine (hinj 0 ia hn0 hialt heq).symm
    have hw0 := (mem_wallList D g c (E 0)).mp (hmem 0 hn0)
    have ht0 := hthird (E 0) (hmem 0 hn0)
    have htia := hthird (E ia) ((mem_wallList D g c (E ia)).mpr hpa)
    have htne : (E 0).1 ≠ (E ia).1 :=
      fun h => Erdos634.WallSide.wall_edges_same_tile D g c
        ⟨(D.tile (E ia).1).pts ((E ia).2 + 2), ne_of_lt htia⟩ (E 0) (E ia) hne h hw0 hwia
    have hnd0 : edgePos D dir (E 0) < edgeEnd D dir (E 0) :=
      shadow_nondegenerate D g dir c hker (E 0).1 (E 0).2 hw0.1 hw0.2
    have hd := shadows_disjoint D g dir c hker (E 0).1 (E ia).1 htne (E 0).2 (E ia).2
      hw0.1 hw0.2 ht0 hwia.1 hwia.2 htia
    rcases hd with h | h
    · rw [heq0] at hnd0; rw [heqpos] at h; linarith
    · rw [heqpos] at hndia; rw [heq0] at h; linarith
  -- `b`'s side, exactly as in `chain_ends_at_b`
  have hbcov := Erdos634.WallEdges.base_covered_by_wall_edges D g c hwall a b hab hbase hline
    (right_mem_segment ℝ a b)
  simp only [mem_iUnion, mem_setOf_eq] at hbcov
  obtain ⟨pb, hpb, hbp⟩ := hbcov
  obtain ⟨ib, hiblt, hibeq⟩ := hsurj pb ((mem_wallList D g c pb).mpr hpb)
  subst hibeq
  have hwib := hpb
  have hndib : edgePos D dir (E ib) < edgeEnd D dir (E ib) :=
    shadow_nondegenerate D g dir c hker (E ib).1 (E ib).2 hwib.1 hwib.2
  have hub : ∀ j < n, edgeEnd D dir (E j) ≤ dir b := by
    intro j hj
    have hwj := (mem_wallList D g c (E j)).mp (hmem j hj)
    have hndj : edgePos D dir (E j) < edgeEnd D dir (E j) :=
      shadow_nondegenerate D g dir c hker (E j).1 (E j).2 hwj.1 hwj.2
    have hsub := shadow_subset_Icc D g c dir hwall a b hdirab hbase hline hface (E j) hwj
    have hmemIcc : edgeEnd D dir (E j) ∈ dir '' ((D.tile (E j).1).edge (E j).2) := by
      rw [edge_image_eq_Icc]; exact ⟨hndj.le, le_refl _⟩
    exact (hsub hmemIcc).2
  have hbp_dir : dir b ∈ dir '' ((D.tile (E ib).1).edge (E ib).2) := ⟨b, hbp, rfl⟩
  rw [edge_image_eq_Icc] at hbp_dir
  have heqend : edgeEnd D dir (E ib) = dir b := le_antisymm (hub ib hiblt) hbp_dir.2
  have hwmemb : edgeEast D dir (E ib) ∈ {y : Plane | g y = c} := by
    unfold edgeEast; split
    · exact hwib.2
    · exact hwib.1
  have hbmemb : b ∈ {y : Plane | g y = c} := hline b (right_mem_segment ℝ a b)
  have hdireqb : dir (edgeEast D dir (E ib)) = dir b := by rw [dir_edgeEast]; exact heqend
  have hbeqb : edgeEast D dir (E ib) = b := dir_injOn_wall g dir c hker hwmemb hbmemb hdireqb
  have hib1 : ib = n - 1 := by
    by_contra hine
    have hilt' : ib < n - 1 := by omega
    have hjlt : n - 1 < n := by omega
    have hij : ib ≤ n - 1 := le_of_lt hilt'
    have hwj := (mem_wallList D g c (E (n - 1))).mp (hmem (n - 1) hjlt)
    have htj := hthird (E (n - 1)) (hmem (n - 1) hjlt)
    have htib := hthird (E ib) ((mem_wallList D g c (E ib)).mpr hpb)
    have hne : E ib ≠ E (n - 1) := by
      intro heq
      have := hinj ib (n - 1) hiblt hjlt heq; omega
    have htne : (E ib).1 ≠ (E (n - 1)).1 :=
      fun h => Erdos634.WallSide.wall_edges_same_tile D g c
        ⟨(D.tile (E ib).1).pts ((E ib).2 + 2), ne_of_lt htib⟩ (E ib) (E (n - 1)) hne h
        hwib hwj
    have hndj : edgePos D dir (E (n - 1)) < edgeEnd D dir (E (n - 1)) :=
      shadow_nondegenerate D g dir c hker (E (n - 1)).1 (E (n - 1)).2 hwj.1 hwj.2
    have hmonoib : edgePos D dir (E ib) ≤ edgePos D dir (E (n - 1)) := hmono ib (n - 1) hij hjlt
    have hd := shadows_disjoint D g dir c hker (E ib).1 (E (n - 1)).1 htne (E ib).2
      (E (n - 1)).2 hwib.1 hwib.2 htib hwj.1 hwj.2 htj
    rcases hd with h | h
    · rw [heqend] at h
      have hle := hub (n - 1) hjlt
      linarith [hndj, h, hle]
    · rw [heqend] at hndib
      linarith [hmonoib, hndj]
  have hlin : ∃ y, g y ≠ c := by
    refine ⟨(D.tile (E ia).1).pts ((E ia).2 + 2), ?_⟩
    have h3 := hthird (E ia) (hmem ia hialt)
    linarith
  have hnondeg : ∀ jj, jj < n → edgePos D dir (E jj) < edgeEnd D dir (E jj) := by
    intro jj hj
    have hw := (mem_wallList D g c (E jj)).mp (hmem jj hj)
    exact shadow_nondegenerate D g dir c hker (E jj).1 (E jj).2 hw.1 hw.2
  have hnoov : ∀ ii jj, ii < jj → jj < n → edgeEnd D dir (E ii) ≤ edgePos D dir (E jj) := by
    intro ii jj hiijj hj
    have hii : ii < n := lt_trans hiijj hj
    have hwii := (mem_wallList D g c (E ii)).mp (hmem ii hii)
    have hwjj := (mem_wallList D g c (E jj)).mp (hmem jj hj)
    have hne : E ii ≠ E jj := fun h => absurd (hinj ii jj hii hj h) (Nat.ne_of_lt hiijj)
    have htile : (E ii).1 ≠ (E jj).1 := by
      intro h
      exact Erdos634.WallSide.wall_edges_same_tile D g c hlin (E ii) (E jj) hne h hwii hwjj
    have hdisj := shadows_disjoint D g dir c hker (E ii).1 (E jj).1 htile (E ii).2 (E jj).2
      hwii.1 hwii.2 (hthird (E ii) (hmem ii hii)) hwjj.1 hwjj.2 (hthird (E jj) (hmem jj hj))
    rcases hdisj with h | h
    · exact h
    · exact absurd h
        (not_le.mpr (lt_of_le_of_lt (hmono ii jj (le_of_lt hiijj) hj) (hnondeg jj hj)))
  refine ⟨E, n, rfl, hn0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hia0] at hweqa
  · rwa [hib1] at hbeqb
  · intro m hm1
    have hreach := base_chain_reach D g c dir hwall a b hab hbase hline hface E hmono hmem hsurj
      m hm1
    have hcontig : edgeEnd D dir (E m) = edgePos D dir (E (m + 1)) :=
      Erdos634.Placement.contiguous_of_no_gap (fun jj => edgePos D dir (E jj))
        (fun jj => edgeEnd D dir (E jj)) n m hm1
        (fun jj _ => edgePos_le_edgeEnd D dir (E jj)) (fun ii jj hij hj => hmono ii jj hij hj)
        hnoov hreach
    have hwm := (mem_wallList D g c (E m)).mp (hmem m (by omega))
    have hwm1 := (mem_wallList D g c (E (m + 1))).mp (hmem (m + 1) hm1)
    exact Erdos634.Placement.shared_junction D dir {y : Plane | g y = c}
      (dir_injOn_wall g dir c hker) (E m) (E (m + 1))
      ((Erdos634.BridgeC.g_ends D g c dir (E m) hwm).2)
      ((Erdos634.BridgeC.g_ends D g c dir (E (m + 1)) hwm1).1) hcontig

  · exact fun m hm => hmem m hm
  · exact fun m1 m2 hm1 hm2 heq => hinj m1 m2 hm1 hm2 heq
  · -- strict lower bound away from the west end: `edgePos (E m) ≥ edgeEnd (E 0) > edgePos (E 0) = dir a`
    intro m hm0 hmn
    have h1 : edgeEnd D dir (E 0) ≤ edgePos D dir (E m) := hnoov 0 m hm0 hmn
    have hw0 := (mem_wallList D g c (E 0)).mp (hmem 0 hn0)
    have h2 : edgePos D dir (E 0) < edgeEnd D dir (E 0) :=
      shadow_nondegenerate D g dir c hker (E 0).1 (E 0).2 hw0.1 hw0.2
    have h3 : edgePos D dir (E 0) = dir a := by
      have := hweqa; rw [← this]; exact (dir_edgeWest D dir (E ia)).symm ▸ (by
        rw [hia0] at hweqa ⊢)
    linarith [h1, h2, h3.symm ▸ h2]
  · -- strict upper bound away from the east end
    intro m hm1
    have h1 : edgeEnd D dir (E m) ≤ edgePos D dir (E (n - 1)) := hnoov m (n - 1) (by omega) (by omega)
    have hwn1 := (mem_wallList D g c (E (n - 1))).mp (hmem (n - 1) (by omega))
    have h2 : edgePos D dir (E (n - 1)) < edgeEnd D dir (E (n - 1)) :=
      shadow_nondegenerate D g dir c hker (E (n - 1)).1 (E (n - 1)).2 hwn1.1 hwn1.2
    have h3 : edgeEnd D dir (E (n - 1)) = dir b := by
      rw [hib1] at hbeqb; rw [← dir_edgeEast D dir (E (n-1))]; rw [hbeqb]
    linarith [h1, h2, h3]
  · intro m hm
    have hw := (mem_wallList D g c (E m)).mp (hmem m hm)
    exact shadow_nondegenerate D g dir c hker (E m).1 (E m).2 hw.1 hw.2

end Erdos634.WallEndpoints
