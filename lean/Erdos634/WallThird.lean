import Erdos634.WallDir
import Erdos634.BaseChain

/-!
# `side_walk_of_dissection`'s last hypothesis, general for any dissection

Erdős #634. `hthird` was the one hypothesis flagged as "genuinely dissection-specific" after
`WallDir.lean` closed `hker`/`hwall`/`hbase`/`hline`/`hface`/`hiso` fully generally — every past
instantiation in this project (`Tiling44WallFinal.hthird_wall`) discharged it via a `decide` check
over one fixed target's finite tile list. It turns out not to need that at all.

The key fact: a wall edge's two endpoints already have `g = c`. If the tile's *third* vertex also
had `g = c`, all three of the tile's vertices would share the same value of a *nonconstant* affine
functional `g` — but the level set of a nonconstant affine map `Plane →ᵃ[ℝ] ℝ` is a genuine line,
and three points on a line are affinely dependent, contradicting the tile's own nondegeneracy
(`Tri.indep`). Combined with `hwall` (`g ≤ c` everywhere on the target, hence on the tile), this
forces the strict inequality `hthird` needs — for *any* dissection, *any* wall functional, *any*
tile. No decision procedure, no fixed target, no coordinates.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.SideWall Erdos634.Geometry.Dissection

/-- **`side_walk_of_dissection`'s `hthird` hypothesis, general for any `Dissection`.** A wall
edge's third vertex is never itself on the wall, hence (with `hwall`) strictly on the target's
interior side of it. -/
theorem hthird_general {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (hne : g.linear ≠ 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) :
    ∀ p ∈ Erdos634.BaseChain.wallList D g c, g ((D.tile p.1).pts (p.2 + 2)) < c := by
  rintro ⟨i, k⟩ hp
  rw [Erdos634.BaseChain.mem_wallList] at hp
  obtain ⟨h0, h1⟩ := hp
  set T := D.tile i with hTdef
  simp only at h0 h1 ⊢
  have hle : g (T.pts (k + 2)) ≤ c := by
    apply hwall
    exact tile_subset_target D i (subset_convexHull ℝ _ (Set.mem_range_self (k+2)))
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    apply hne
    have hv1 : g.linear (T.pts (k+1) -ᵥ T.pts k) = 0 := by
      rw [AffineMap.linearMap_vsub]
      show g (T.pts (k+1)) - g (T.pts k) = 0
      rw [h0, h1]; ring
    have hv2 : g.linear (T.pts (k+2) -ᵥ T.pts k) = 0 := by
      rw [AffineMap.linearMap_vsub]
      show g (T.pts (k+2)) - g (T.pts k) = 0
      rw [h0, heq]; ring
    apply (T.basis.basisOf k).ext
    intro j
    rw [AffineBasis.basisOf_apply]
    have hbT : ∀ m : Fin 3, (T.basis : Fin 3 → Plane) m = T.pts m := fun m => rfl
    rcases j with ⟨j, hj⟩
    fin_cases k <;> fin_cases j <;> simp_all [hbT]

/-- **`hne`'s hypothesis, discharged for `wallFun`.** `wallFun T k`'s linear part is nonzero, so
`hthird_general` applies directly with `g := wallFun T k` for any `Tri` and side. -/
theorem wallFun_linear_ne_zero (T : Tri) (k : Fin 3) : (wallFun T k).linear ≠ 0 := by
  intro hz
  have h1 : (wallFun T k).linear (T.pts (k+2) -ᵥ T.pts k) = 0 := by rw [hz]; rfl
  rw [AffineMap.linearMap_vsub] at h1
  have hk : wallFun T k (T.pts k) = 0 :=
    wallFun_eq_zero T k (left_mem_segment ℝ (T.pts k) (T.pts (k+1)))
  have hk2 : wallFun T k (T.pts (k+2)) ≠ 0 := by
    show -(T.basis.coord (k+2)) (T.pts (k+2)) ≠ 0
    have hbT : (T.basis : Fin 3 → Plane) (k+2) = T.pts (k+2) := rfl
    rw [← hbT, AffineBasis.coord_apply_eq]
    norm_num
  rw [hk] at h1
  simp only [vsub_eq_sub, sub_zero] at h1
  exact hk2 h1
