import Erdos634.Congruence
import Erdos634.TilePlacement
import Erdos634.Placement

/-!
# Every tile edge has one of the model's three lengths

Erdős #634. `thm:chain` and `prop:gammatrap` both need to classify a chain edge as an `a`-, `b`-
or `c`-edge (by length) before their inductive arguments can even be stated. This file is that
classifier's existence half: for a `CongruentDissection`, every edge of every tile has a length
equal to one of the model's three side lengths — `Tri.Congruent.dist_eq` already supplies the
matching permutation; this file names the consequence for a single edge.

The classifier does not by itself discharge `thm:chain` or `prop:gammatrap`: what remains is the
inductive propagation argument itself (an unbounded induction along a run, forcing the alternation
`α,γ,α,γ,...`), which is separate, substantial work not attempted here.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Geometry

open Erdos634.TilePlacement

variable {N : ℕ}

private theorem third_index (x y : Fin 3) (hxy : x ≠ y) : ∃ j, j ≠ x ∧ j ≠ y := by
  revert x y hxy; decide

private theorem opp_eq_of_ne (x y j : Fin 3) (hxj : j ≠ x) (hyj : j ≠ y) (hxy : x ≠ y) :
    j + 1 = x ∧ j + 2 = y ∨ j + 1 = y ∧ j + 2 = x := by
  revert x y j hxj hyj hxy; decide

/-- **Every tile edge has one of the model's three lengths.** -/
theorem exists_matching_side (D : CongruentDissection N) (i : Fin N) (k : Fin 3) :
    ∃ j : Fin 3, dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model j := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
  have hne : σ k ≠ σ (k + 1) := by
    intro h
    have := σ.injective h
    have hk : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact hk k this
  obtain ⟨j, hj1, hj2⟩ := third_index (σ k) (σ (k + 1)) hne
  refine ⟨j, ?_⟩
  rw [hσ k (k + 1)]
  unfold sideOpp
  rcases opp_eq_of_ne (σ k) (σ (k + 1)) j hj1 hj2 hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

/-- **A corner angle does not care which order the two flanking vertices come in.** -/
private theorem cornerAngle_swap_any (T : Tri) (m p r : Fin 3) (hp : p ≠ m) (hr : r ≠ m)
    (hpr : p ≠ r) :
    cornerAngle (T.pts p) (T.pts m) (T.pts r)
      = cornerAngle (T.pts (m + 1)) (T.pts m) (T.pts (m + 2)) := by
  rcases fin3_cases p m hp with hp1 | hp2
  · have hr2 : r = m + 2 := by
      rcases fin3_cases r m hr with hr1 | hr2
      · exact absurd (hp1.trans hr1.symm) hpr
      · exact hr2
    rw [hp1, hr2]
  · have hr1 : r = m + 1 := by
      rcases fin3_cases r m hr with hr1 | hr2
      · exact hr1
      · exact absurd (hp2.trans hr2.symm) hpr
    rw [hp2, hr1, Erdos634.Geometry.cornerAngle, Erdos634.Geometry.cornerAngle,
      EuclideanGeometry.angle_comm]

/-- **A non-`c` edge is incident to `γ` at exactly one endpoint.** Needs the model scalene
(`hscalene`) and `α ≠ γ`, `β ≠ γ`. -/
theorem gamma_at_one_endpoint (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (i : Fin N) (k : Fin 3) (j : Fin 3) (hj : j ≠ 2)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model j) :
    (TilePlacement.angleAt (D.tile i) k = γ ∧
        TilePlacement.angleAt (D.tile i) (k + 1) ≠ γ) ∨
    (TilePlacement.angleAt (D.tile i) (k + 1) = γ ∧
        TilePlacement.angleAt (D.tile i) k ≠ γ) := by
  obtain ⟨σ, hd⟩ := (D.tiles_congruent i).dist_eq
  have hpq : ∀ x y : Fin 3, x ≠ y → (D.tile i).pts x ≠ (D.tile i).pts y := by
    intro x y hxy heq; exact hxy ((D.tile i).indep.injective heq)
  have hnek1 : (k + 1 : Fin 3) ≠ k := (by decide : ∀ x : Fin 3, x + 1 ≠ x) k
  have hnek2 : (k + 2 : Fin 3) ≠ k := (by decide : ∀ x : Fin 3, x + 2 ≠ x) k
  have hnek1' : (k + 1 + 1 : Fin 3) ≠ k + 1 := (by decide : ∀ x : Fin 3, x + 1 + 1 ≠ x + 1) k
  have hangk : TilePlacement.angleAt (D.tile i) k
      = cornerAngle (D.model.pts (σ (k + 1))) (D.model.pts (σ k)) (D.model.pts (σ (k + 2))) := by
    unfold TilePlacement.angleAt
    exact angle_of_sss (hd (k + 1) k) (hd k (k + 2)) (hd (k + 1) (k + 2))
      (hpq (k + 1) k hnek1) (hpq (k + 2) k hnek2)
  have hangk1raw : TilePlacement.angleAt (D.tile i) (k + 1)
      = cornerAngle (D.model.pts (σ (k + 1 + 1))) (D.model.pts (σ (k + 1)))
          (D.model.pts (σ (k + 1 + 2))) := by
    unfold TilePlacement.angleAt
    exact angle_of_sss (hd (k + 1 + 1) (k + 1)) (hd (k + 1) (k + 1 + 2))
      (hd (k + 1 + 1) (k + 1 + 2)) (hpq (k + 1 + 1) (k + 1) hnek1') (by
        have h2 : (k + 1 + 2 : Fin 3) ≠ k + 1 := (by decide : ∀ x : Fin 3, x + 1 + 2 ≠ x + 1) k
        exact hpq (k + 1 + 2) (k + 1) h2)
  have hshift1 : (k + 1 + 1 : Fin 3) = k + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) k
  have hshift2 : (k + 1 + 2 : Fin 3) = k := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) k
  have hangk1 : TilePlacement.angleAt (D.tile i) (k + 1)
      = cornerAngle (D.model.pts (σ (k + 2))) (D.model.pts (σ (k + 1))) (D.model.pts (σ k)) := by
    rw [hangk1raw, hshift1, hshift2]
  have hne01 : σ k ≠ σ (k + 1) := fun h => hnek1 (σ.injective h.symm)
  have hne02 : σ k ≠ σ (k + 2) := fun h => hnek2 (σ.injective h.symm)
  have hne12 : σ (k + 1) ≠ σ (k + 2) := by
    intro h; exact (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k (σ.injective h)
  have hangval : ∀ m : Fin 3, cornerAngle (D.model.pts (m + 1)) (D.model.pts m)
      (D.model.pts (m + 2)) = (if m = 0 then α else if m = 1 then β else γ) := by
    intro m; fin_cases m
    · simpa using hα'
    · simpa using hβ'
    · simpa using hγ'
  have hangk' : TilePlacement.angleAt (D.tile i) k
      = (if σ k = 0 then α else if σ k = 1 then β else γ) := by
    rw [hangk, cornerAngle_swap_any D.model (σ k) (σ (k + 1)) (σ (k + 2))
      hne01.symm hne02.symm hne12, hangval]
  have hangk1' : TilePlacement.angleAt (D.tile i) (k + 1)
      = (if σ (k + 1) = 0 then α else if σ (k + 1) = 1 then β else γ) := by
    rw [hangk1, cornerAngle_swap_any D.model (σ (k + 1)) (σ (k + 2)) (σ k)
      hne12.symm hne01 hne02.symm, hangval]
  obtain ⟨j0, hj0k, hj0k1⟩ := third_index (σ k) (σ (k + 1)) hne01
  have hlen' : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1))
      = dist (D.model.pts (σ k)) (D.model.pts (σ (k + 1))) := hd k (k + 1)
  have hj0eq : sideOpp D.model j0 = dist (D.model.pts (σ k)) (D.model.pts (σ (k + 1))) := by
    unfold sideOpp
    rcases opp_eq_of_ne (σ k) (σ (k + 1)) j0 hj0k hj0k1 hne01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  have hjeq : j = j0 := by
    by_contra hne
    exact hscalene j j0 hne ((hlen.symm.trans hlen').trans hj0eq.symm)
  have hj0ne2 : j0 ≠ 2 := hjeq ▸ hj
  have htri : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hthird_is_two : ∀ x y z : Fin 3, x ≠ y → z ≠ x → z ≠ y → x ≠ 2 → y ≠ 2 → z = 2 := by decide
  rcases htri (σ k) with hk0 | hk0 | hk0
  · rcases htri (σ (k + 1)) with hk10 | hk10 | hk10
    · exact absurd (hk0.trans hk10.symm) hne01
    · exact absurd (hthird_is_two (σ k) (σ (k + 1)) j0 hne01 hj0k hj0k1
        (by rw [hk0]; decide) (by rw [hk10]; decide)) hj0ne2
    · right
      rw [hangk', hangk1', hk0, hk10]
      refine ⟨by rw [if_neg (by decide : ¬ ((2:Fin 3) = 0)), if_neg (by decide : ¬ ((2:Fin 3) = 1))],
        ?_⟩
      rw [if_pos (rfl : (0:Fin 3) = 0)]
      exact hαγ
  · rcases htri (σ (k + 1)) with hk10 | hk10 | hk10
    · exact absurd (hthird_is_two (σ k) (σ (k + 1)) j0 hne01 hj0k hj0k1
        (by rw [hk0]; decide) (by rw [hk10]; decide)) hj0ne2
    · exact absurd (hk0.trans hk10.symm) hne01
    · right
      rw [hangk', hangk1', hk0, hk10]
      refine ⟨by rw [if_neg (by decide : ¬ ((2:Fin 3) = 0)), if_neg (by decide : ¬ ((2:Fin 3) = 1))],
        ?_⟩
      rw [if_neg (by decide : ¬ ((1:Fin 3) = 0)), if_pos (rfl : (1:Fin 3) = 1)]
      exact hβγ
  · rcases htri (σ (k + 1)) with hk10 | hk10 | hk10
    · left
      rw [hangk', hangk1', hk0, hk10]
      refine ⟨?_, ?_⟩
      · rw [if_neg (by decide : ¬ ((2:Fin 3) = 0)), if_neg (by decide : ¬ ((2:Fin 3) = 1))]
      · rw [if_pos (rfl : (0:Fin 3) = 0)]; exact hαγ
    · left
      rw [hangk', hangk1', hk0, hk10]
      refine ⟨?_, ?_⟩
      · rw [if_neg (by decide : ¬ ((2:Fin 3) = 0)), if_neg (by decide : ¬ ((2:Fin 3) = 1))]
      · rw [if_neg (by decide : ¬ ((1:Fin 3) = 0)), if_pos (rfl : (1:Fin 3) = 1)]; exact hβγ
    · exact absurd (hk0.trans hk10.symm) hne01

/-- **The `angleAt`/`edgeWest`-`edgeEast` bridge.**  Whichever of a tile's edge endpoints is
geometrically west, its vertex-indexed `angleAt` matches `localAngle` there — and symmetrically
for east. -/
theorem localAngle_edgeWest_edgeEast {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (i : Fin N) (k : Fin 3) :
    ((D.tile i).localAngle (Erdos634.Placement.edgeWest D dir (i, k)) = TilePlacement.angleAt
      (D.tile i) k ∧
      (D.tile i).localAngle (Erdos634.Placement.edgeEast D dir (i, k))
        = TilePlacement.angleAt (D.tile i) (k + 1)) ∨
    ((D.tile i).localAngle (Erdos634.Placement.edgeWest D dir (i, k)) = TilePlacement.angleAt
      (D.tile i) (k + 1) ∧
      (D.tile i).localAngle (Erdos634.Placement.edgeEast D dir (i, k))
        = TilePlacement.angleAt (D.tile i) k) := by
  unfold Erdos634.Placement.edgeWest Erdos634.Placement.edgeEast TilePlacement.angleAt
  split
  · left; exact ⟨Tri.localAngle_vertex (D.tile i) k, Tri.localAngle_vertex (D.tile i) (k + 1)⟩
  · right; exact ⟨Tri.localAngle_vertex (D.tile i) (k + 1), Tri.localAngle_vertex (D.tile i) k⟩

/-- **An edge never presents its own type's angle at either endpoint.**  An `a`-edge (type `0`,
opposite `α`) is flanked by `β` and `γ`, never `α`; symmetrically for `b`/`c`. This is the general
fact behind `gamma_at_one_endpoint`'s exclusion, exposed on its own since a caller reading off a
specific edge type (not just "not `c`") needs it, e.g. for `a`-edges specifically (`prop:orientmono`
and the family of "which of its edges are `a`-edges" rows sharing this same blocker). -/
theorem edge_excludes_own_angle (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (i : Fin N) (k : Fin 3) (j : Fin 3) (own : ℝ)
    (hown : own = (if j = 0 then α else if j = 1 then β else γ))
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model j) :
    TilePlacement.angleAt (D.tile i) k ≠ own ∧ TilePlacement.angleAt (D.tile i) (k + 1) ≠ own := by
  obtain ⟨σ, hd⟩ := (D.tiles_congruent i).dist_eq
  have hpq : ∀ x y : Fin 3, x ≠ y → (D.tile i).pts x ≠ (D.tile i).pts y := by
    intro x y hxy heq; exact hxy ((D.tile i).indep.injective heq)
  have hnek1 : (k + 1 : Fin 3) ≠ k := (by decide : ∀ x : Fin 3, x + 1 ≠ x) k
  have hnek2 : (k + 2 : Fin 3) ≠ k := (by decide : ∀ x : Fin 3, x + 2 ≠ x) k
  have hnek1' : (k + 1 + 1 : Fin 3) ≠ k + 1 := (by decide : ∀ x : Fin 3, x + 1 + 1 ≠ x + 1) k
  have hangk : TilePlacement.angleAt (D.tile i) k
      = cornerAngle (D.model.pts (σ (k + 1))) (D.model.pts (σ k)) (D.model.pts (σ (k + 2))) := by
    unfold TilePlacement.angleAt
    exact angle_of_sss (hd (k + 1) k) (hd k (k + 2)) (hd (k + 1) (k + 2))
      (hpq (k + 1) k hnek1) (hpq (k + 2) k hnek2)
  have hangk1raw : TilePlacement.angleAt (D.tile i) (k + 1)
      = cornerAngle (D.model.pts (σ (k + 1 + 1))) (D.model.pts (σ (k + 1)))
          (D.model.pts (σ (k + 1 + 2))) := by
    unfold TilePlacement.angleAt
    exact angle_of_sss (hd (k + 1 + 1) (k + 1)) (hd (k + 1) (k + 1 + 2))
      (hd (k + 1 + 1) (k + 1 + 2)) (hpq (k + 1 + 1) (k + 1) hnek1') (by
        have h2 : (k + 1 + 2 : Fin 3) ≠ k + 1 := (by decide : ∀ x : Fin 3, x + 1 + 2 ≠ x + 1) k
        exact hpq (k + 1 + 2) (k + 1) h2)
  have hshift1 : (k + 1 + 1 : Fin 3) = k + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) k
  have hshift2 : (k + 1 + 2 : Fin 3) = k := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) k
  have hangk1 : TilePlacement.angleAt (D.tile i) (k + 1)
      = cornerAngle (D.model.pts (σ (k + 2))) (D.model.pts (σ (k + 1))) (D.model.pts (σ k)) := by
    rw [hangk1raw, hshift1, hshift2]
  have hne01 : σ k ≠ σ (k + 1) := fun h => hnek1 (σ.injective h.symm)
  have hne02 : σ k ≠ σ (k + 2) := fun h => hnek2 (σ.injective h.symm)
  have hne12 : σ (k + 1) ≠ σ (k + 2) := by
    intro h; exact (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k (σ.injective h)
  have hangval : ∀ m : Fin 3, cornerAngle (D.model.pts (m + 1)) (D.model.pts m)
      (D.model.pts (m + 2)) = (if m = 0 then α else if m = 1 then β else γ) := by
    intro m; fin_cases m
    · simpa using hα'
    · simpa using hβ'
    · simpa using hγ'
  have hangk' : TilePlacement.angleAt (D.tile i) k
      = (if σ k = 0 then α else if σ k = 1 then β else γ) := by
    rw [hangk, cornerAngle_swap_any D.model (σ k) (σ (k + 1)) (σ (k + 2))
      hne01.symm hne02.symm hne12, hangval]
  have hangk1' : TilePlacement.angleAt (D.tile i) (k + 1)
      = (if σ (k + 1) = 0 then α else if σ (k + 1) = 1 then β else γ) := by
    rw [hangk1, cornerAngle_swap_any D.model (σ (k + 1)) (σ (k + 2)) (σ k)
      hne12.symm hne01 hne02.symm, hangval]
  obtain ⟨j0, hj0k, hj0k1⟩ := third_index (σ k) (σ (k + 1)) hne01
  have hlen' : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1))
      = dist (D.model.pts (σ k)) (D.model.pts (σ (k + 1))) := hd k (k + 1)
  have hj0eq' : sideOpp D.model j0 = dist (D.model.pts (σ k)) (D.model.pts (σ (k + 1))) := by
    unfold sideOpp
    rcases opp_eq_of_ne (σ k) (σ (k + 1)) j0 hj0k hj0k1 hne01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  have hjeq : j = j0 := by
    by_contra hne
    exact hscalene j j0 hne ((hlen.symm.trans hlen').trans hj0eq'.symm)
  subst hjeq
  -- so `σ k ≠ j` and `σ (k+1) ≠ j`, hence neither endpoint's angle is `j`'s own value
  have htri3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hval_inj : ∀ x y : Fin 3, x ≠ y →
      (if x = 0 then α else if x = 1 then β else γ) ≠
        (if y = 0 then α else if y = 1 then β else γ) := by
    intro x y hxy
    rcases htri3 x with hx | hx | hx <;> rcases htri3 y with hy | hy | hy <;>
      subst hx <;> subst hy <;> simp at hxy ⊢ <;>
      first | (exact absurd rfl hxy) | exact hαβ | exact hαγ | exact hβγ | exact hαβ.symm | exact hαγ.symm | exact hβγ.symm
  refine ⟨?_, ?_⟩
  · rw [hangk', hown]; exact hval_inj (σ k) j (Ne.symm hj0k)
  · rw [hangk1', hown]; exact hval_inj (σ (k + 1)) j (Ne.symm hj0k1)

/-- **An `a`-edge's two ends carry `β` and `γ`, distinct.**  This is bridge (c)'s remaining
geometric input, named in `PAPER_MAP`'s `prop:orientmono` row: `edge_excludes_own_angle` at `j=0`
excludes `α` from both endpoints of an `a`-edge, and here that is packaged into exactly the form
`OrientBridge.orient_reading`/`.orient_BG_east_gamma`/`.orient_GB_west_gamma` need — `hw`, `he`,
`hne` — closing the last hypothesis those theorems previously took as given. -/
theorem a_edge_endpoints (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 0) :
    (TilePlacement.angleAt (D.tile i) k = β ∨ TilePlacement.angleAt (D.tile i) k = γ) ∧
    (TilePlacement.angleAt (D.tile i) (k + 1) = β ∨
      TilePlacement.angleAt (D.tile i) (k + 1) = γ) ∧
    TilePlacement.angleAt (D.tile i) k ≠ TilePlacement.angleAt (D.tile i) (k + 1) := by
  obtain ⟨σ, hd⟩ := (D.tiles_congruent i).dist_eq
  have hpq : ∀ x y : Fin 3, x ≠ y → (D.tile i).pts x ≠ (D.tile i).pts y := by
    intro x y hxy heq; exact hxy ((D.tile i).indep.injective heq)
  have hnek1 : (k + 1 : Fin 3) ≠ k := (by decide : ∀ x : Fin 3, x + 1 ≠ x) k
  have hnek2 : (k + 2 : Fin 3) ≠ k := (by decide : ∀ x : Fin 3, x + 2 ≠ x) k
  have hnek1' : (k + 1 + 1 : Fin 3) ≠ k + 1 := (by decide : ∀ x : Fin 3, x + 1 + 1 ≠ x + 1) k
  have hangk : TilePlacement.angleAt (D.tile i) k
      = cornerAngle (D.model.pts (σ (k + 1))) (D.model.pts (σ k)) (D.model.pts (σ (k + 2))) := by
    unfold TilePlacement.angleAt
    exact angle_of_sss (hd (k + 1) k) (hd k (k + 2)) (hd (k + 1) (k + 2))
      (hpq (k + 1) k hnek1) (hpq (k + 2) k hnek2)
  have hangk1raw : TilePlacement.angleAt (D.tile i) (k + 1)
      = cornerAngle (D.model.pts (σ (k + 1 + 1))) (D.model.pts (σ (k + 1)))
          (D.model.pts (σ (k + 1 + 2))) := by
    unfold TilePlacement.angleAt
    exact angle_of_sss (hd (k + 1 + 1) (k + 1)) (hd (k + 1) (k + 1 + 2))
      (hd (k + 1 + 1) (k + 1 + 2)) (hpq (k + 1 + 1) (k + 1) hnek1') (by
        have h2 : (k + 1 + 2 : Fin 3) ≠ k + 1 := (by decide : ∀ x : Fin 3, x + 1 + 2 ≠ x + 1) k
        exact hpq (k + 1 + 2) (k + 1) h2)
  have hshift1 : (k + 1 + 1 : Fin 3) = k + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) k
  have hshift2 : (k + 1 + 2 : Fin 3) = k := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) k
  have hangk1 : TilePlacement.angleAt (D.tile i) (k + 1)
      = cornerAngle (D.model.pts (σ (k + 2))) (D.model.pts (σ (k + 1))) (D.model.pts (σ k)) := by
    rw [hangk1raw, hshift1, hshift2]
  have hne01 : σ k ≠ σ (k + 1) := fun h => hnek1 (σ.injective h.symm)
  have hne02 : σ k ≠ σ (k + 2) := fun h => hnek2 (σ.injective h.symm)
  have hne12 : σ (k + 1) ≠ σ (k + 2) := by
    intro h; exact (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k (σ.injective h)
  have hangval : ∀ m : Fin 3, cornerAngle (D.model.pts (m + 1)) (D.model.pts m)
      (D.model.pts (m + 2)) = (if m = 0 then α else if m = 1 then β else γ) := by
    intro m; fin_cases m
    · simpa using hα'
    · simpa using hβ'
    · simpa using hγ'
  have hangk' : TilePlacement.angleAt (D.tile i) k
      = (if σ k = 0 then α else if σ k = 1 then β else γ) := by
    rw [hangk, cornerAngle_swap_any D.model (σ k) (σ (k + 1)) (σ (k + 2))
      hne01.symm hne02.symm hne12, hangval]
  have hangk1' : TilePlacement.angleAt (D.tile i) (k + 1)
      = (if σ (k + 1) = 0 then α else if σ (k + 1) = 1 then β else γ) := by
    rw [hangk1, cornerAngle_swap_any D.model (σ (k + 1)) (σ (k + 2)) (σ k)
      hne12.symm hne01 hne02.symm, hangval]
  obtain ⟨j0, hj0k, hj0k1⟩ := third_index (σ k) (σ (k + 1)) hne01
  have hlen' : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1))
      = dist (D.model.pts (σ k)) (D.model.pts (σ (k + 1))) := hd k (k + 1)
  have hj0eq' : sideOpp D.model j0 = dist (D.model.pts (σ k)) (D.model.pts (σ (k + 1))) := by
    unfold sideOpp
    rcases opp_eq_of_ne (σ k) (σ (k + 1)) j0 hj0k hj0k1 hne01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  have hjeq : (0 : Fin 3) = j0 := by
    by_contra hne
    exact hscalene 0 j0 hne ((hlen.symm.trans hlen').trans hj0eq'.symm)
  rw [← hjeq] at hj0k hj0k1
  have htri3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hval_inj : ∀ x y : Fin 3, x ≠ y →
      (if x = 0 then α else if x = 1 then β else γ) ≠
        (if y = 0 then α else if y = 1 then β else γ) := by
    intro x y hxy
    rcases htri3 x with hx | hx | hx <;> rcases htri3 y with hy | hy | hy <;>
      subst hx <;> subst hy <;> simp at hxy ⊢ <;>
      first | (exact absurd rfl hxy) | exact hαβ | exact hαγ | exact hβγ | exact hαβ.symm | exact hαγ.symm | exact hβγ.symm
  have hkne : TilePlacement.angleAt (D.tile i) k ≠ α := by
    rw [hangk']; exact hval_inj (σ k) 0 (Ne.symm hj0k)
  have hk1ne : TilePlacement.angleAt (D.tile i) (k + 1) ≠ α := by
    rw [hangk1']; exact hval_inj (σ (k + 1)) 0 (Ne.symm hj0k1)
  have hktri : TilePlacement.angleAt (D.tile i) k = α ∨ TilePlacement.angleAt (D.tile i) k = β ∨
      TilePlacement.angleAt (D.tile i) k = γ := by
    rw [hangk']; rcases htri3 (σ k) with h | h | h <;> rw [h] <;> simp
  have hk1tri : TilePlacement.angleAt (D.tile i) (k + 1) = α ∨
      TilePlacement.angleAt (D.tile i) (k + 1) = β ∨
      TilePlacement.angleAt (D.tile i) (k + 1) = γ := by
    rw [hangk1']; rcases htri3 (σ (k + 1)) with h | h | h <;> rw [h] <;> simp
  refine ⟨hktri.resolve_left hkne, hk1tri.resolve_left hk1ne, ?_⟩
  rw [hangk', hangk1']
  exact hval_inj (σ k) (σ (k + 1)) hne01

theorem b_edge_endpoints (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hscalene : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = sideOpp D.model 1) :
    (TilePlacement.angleAt (D.tile i) k = α ∨ TilePlacement.angleAt (D.tile i) k = γ) ∧
    (TilePlacement.angleAt (D.tile i) (k + 1) = α ∨
      TilePlacement.angleAt (D.tile i) (k + 1) = γ) ∧
    TilePlacement.angleAt (D.tile i) k ≠ TilePlacement.angleAt (D.tile i) (k + 1) := by
  obtain ⟨σ, hd⟩ := (D.tiles_congruent i).dist_eq
  have hpq : ∀ x y : Fin 3, x ≠ y → (D.tile i).pts x ≠ (D.tile i).pts y := by
    intro x y hxy heq; exact hxy ((D.tile i).indep.injective heq)
  have hnek1 : (k + 1 : Fin 3) ≠ k := (by decide : ∀ x : Fin 3, x + 1 ≠ x) k
  have hnek2 : (k + 2 : Fin 3) ≠ k := (by decide : ∀ x : Fin 3, x + 2 ≠ x) k
  have hnek1' : (k + 1 + 1 : Fin 3) ≠ k + 1 := (by decide : ∀ x : Fin 3, x + 1 + 1 ≠ x + 1) k
  have hangk : TilePlacement.angleAt (D.tile i) k
      = cornerAngle (D.model.pts (σ (k + 1))) (D.model.pts (σ k)) (D.model.pts (σ (k + 2))) := by
    unfold TilePlacement.angleAt
    exact angle_of_sss (hd (k + 1) k) (hd k (k + 2)) (hd (k + 1) (k + 2))
      (hpq (k + 1) k hnek1) (hpq (k + 2) k hnek2)
  have hangk1raw : TilePlacement.angleAt (D.tile i) (k + 1)
      = cornerAngle (D.model.pts (σ (k + 1 + 1))) (D.model.pts (σ (k + 1)))
          (D.model.pts (σ (k + 1 + 2))) := by
    unfold TilePlacement.angleAt
    exact angle_of_sss (hd (k + 1 + 1) (k + 1)) (hd (k + 1) (k + 1 + 2))
      (hd (k + 1 + 1) (k + 1 + 2)) (hpq (k + 1 + 1) (k + 1) hnek1') (by
        have h2 : (k + 1 + 2 : Fin 3) ≠ k + 1 := (by decide : ∀ x : Fin 3, x + 1 + 2 ≠ x + 1) k
        exact hpq (k + 1 + 2) (k + 1) h2)
  have hshift1 : (k + 1 + 1 : Fin 3) = k + 2 := (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) k
  have hshift2 : (k + 1 + 2 : Fin 3) = k := (by decide : ∀ x : Fin 3, x + 1 + 2 = x) k
  have hangk1 : TilePlacement.angleAt (D.tile i) (k + 1)
      = cornerAngle (D.model.pts (σ (k + 2))) (D.model.pts (σ (k + 1))) (D.model.pts (σ k)) := by
    rw [hangk1raw, hshift1, hshift2]
  have hne01 : σ k ≠ σ (k + 1) := fun h => hnek1 (σ.injective h.symm)
  have hne02 : σ k ≠ σ (k + 2) := fun h => hnek2 (σ.injective h.symm)
  have hne12 : σ (k + 1) ≠ σ (k + 2) := by
    intro h; exact (by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k (σ.injective h)
  have hangval : ∀ m : Fin 3, cornerAngle (D.model.pts (m + 1)) (D.model.pts m)
      (D.model.pts (m + 2)) = (if m = 0 then α else if m = 1 then β else γ) := by
    intro m; fin_cases m
    · simpa using hα'
    · simpa using hβ'
    · simpa using hγ'
  have hangk' : TilePlacement.angleAt (D.tile i) k
      = (if σ k = 0 then α else if σ k = 1 then β else γ) := by
    rw [hangk, cornerAngle_swap_any D.model (σ k) (σ (k + 1)) (σ (k + 2))
      hne01.symm hne02.symm hne12, hangval]
  have hangk1' : TilePlacement.angleAt (D.tile i) (k + 1)
      = (if σ (k + 1) = 0 then α else if σ (k + 1) = 1 then β else γ) := by
    rw [hangk1, cornerAngle_swap_any D.model (σ (k + 1)) (σ (k + 2)) (σ k)
      hne12.symm hne01 hne02.symm, hangval]
  obtain ⟨j0, hj0k, hj0k1⟩ := third_index (σ k) (σ (k + 1)) hne01
  have hlen' : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1))
      = dist (D.model.pts (σ k)) (D.model.pts (σ (k + 1))) := hd k (k + 1)
  have hj0eq' : sideOpp D.model j0 = dist (D.model.pts (σ k)) (D.model.pts (σ (k + 1))) := by
    unfold sideOpp
    rcases opp_eq_of_ne (σ k) (σ (k + 1)) j0 hj0k hj0k1 hne01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  have hjeq : (1 : Fin 3) = j0 := by
    by_contra hne
    exact hscalene 1 j0 hne ((hlen.symm.trans hlen').trans hj0eq'.symm)
  rw [← hjeq] at hj0k hj0k1
  have htri3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hval_inj : ∀ x y : Fin 3, x ≠ y →
      (if x = 0 then α else if x = 1 then β else γ) ≠
        (if y = 0 then α else if y = 1 then β else γ) := by
    intro x y hxy
    rcases htri3 x with hx | hx | hx <;> rcases htri3 y with hy | hy | hy <;>
      subst hx <;> subst hy <;> simp at hxy ⊢ <;>
      first | (exact absurd rfl hxy) | exact hαβ | exact hαγ | exact hβγ | exact hαβ.symm | exact hαγ.symm | exact hβγ.symm
  have hkne : TilePlacement.angleAt (D.tile i) k ≠ β := by
    rw [hangk']; exact hval_inj (σ k) 1 (Ne.symm hj0k)
  have hk1ne : TilePlacement.angleAt (D.tile i) (k + 1) ≠ β := by
    rw [hangk1']; exact hval_inj (σ (k + 1)) 1 (Ne.symm hj0k1)
  have hktri : TilePlacement.angleAt (D.tile i) k = α ∨ TilePlacement.angleAt (D.tile i) k = β ∨
      TilePlacement.angleAt (D.tile i) k = γ := by
    rw [hangk']; rcases htri3 (σ k) with h | h | h <;> rw [h] <;> simp
  have hk1tri : TilePlacement.angleAt (D.tile i) (k + 1) = α ∨
      TilePlacement.angleAt (D.tile i) (k + 1) = β ∨
      TilePlacement.angleAt (D.tile i) (k + 1) = γ := by
    rw [hangk1']; rcases htri3 (σ (k + 1)) with h | h | h <;> rw [h] <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rcases hktri with h | h | h
    · exact Or.inl h
    · exact absurd h hkne
    · exact Or.inr h
  · rcases hk1tri with h | h | h
    · exact Or.inl h
    · exact absurd h hk1ne
    · exact Or.inr h
  · rw [hangk', hangk1']
    exact hval_inj (σ k) (σ (k + 1)) hne01


end Erdos634.Geometry
