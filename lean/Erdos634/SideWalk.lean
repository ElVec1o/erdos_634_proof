import Erdos634.ChainWalk
import Erdos634.EdgeType
import Erdos634.WallEndpoints
import Erdos634.BridgeC

/-!
# A real side's walk equation

Erdős #634. `ChainWalk.chain_walk` proves the walk equation `P'a + Q'b + R'c = L` abstractly, for
any `L R : ℕ → ℝ` satisfying a contiguity hypothesis and a per-edge length classification. It was
never connected to a real dissection's boundary chain. `thm:walks`, `thm:walkstruct` and
`cor:wallsf2e` all stop at exactly that connection (their `PAPER_MAP` rows: "identifying a real
side's edges with a walk").

This file makes the connection: `WallEndpoints.chain_endpoints` supplies the real, ordered edge
chain along a wall (contiguity is its own theorem, not a hypothesis here), `EdgeType
.exists_matching_side` classifies each edge's length, and `dist_eq_abs_dir_sub` (new) is the one
extra geometric fact needed — that two points on the same wall line have their (real) distance
equal to the absolute difference of `dir`, given `dir` is calibrated to the line — after which
`ChainWalk.chain_walk` applies directly.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SideWalk

open Erdos634.Geometry Erdos634.Placement Erdos634.TilePlacement Erdos634.WallEndpoints
  Erdos634.BridgeC

variable {N : ℕ}

/-- **A real side's walk equation.** Given the standard wall/line setup (as `chain_endpoints`
needs) and `hiso` (the one calibration fact: `dir` measures real distance along the wall line —
true for the natural choice of `dir`, e.g. the unit vector along `a → b`, but not for an arbitrary
linear functional, hence a hypothesis here rather than derived from `hker` alone), the wall's total
span `dist a b` is exactly `P'·(sideOpp 0) + Q'·(sideOpp 1) + R'·(sideOpp 2)`, with `P'`, `Q'`, `R'`
the counts of `a`-, `b`-, `c`-type edges among the wall's tile edges. -/
theorem side_walk_of_dissection (D : CongruentDissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b) (hdirab : dir a ≤ dir b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hthird : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection g c,
      g ((D.tile p.1).pts (p.2 + 2)) < c)
    (hiso : ∀ p q : Plane, g p = c → g q = c → dist p q = |dir p - dir q|)
    (hscalene : sideOpp D.model 0 ≠ sideOpp D.model 1 ∧ sideOpp D.model 0 ≠ sideOpp D.model 2 ∧
      sideOpp D.model 1 ≠ sideOpp D.model 2)
    (hN : 0 < N) :
    ∃ Pc Qc Rc : ℕ,
      dist a b = Pc * sideOpp D.model 0 + Qc * sideOpp D.model 1 + Rc * sideOpp D.model 2 := by
  classical
  obtain ⟨E, n, hneq, hn0, hwest0, heastlast, hjunc, hmem, hinj, hlba, hlbend, hnondeg⟩ :=
    chain_endpoints hN D.toDissection g c dir hker hwall a b hab hdirab hbase hline hface hthird
  set L : ℕ → ℝ := fun m => Erdos634.OrientBridge.edgePos D.toDissection dir (E m) with hLdef
  set R : ℕ → ℝ := fun m => Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m) with hRdef
  have hcontig : ∀ j, j + 1 < n → R j = L (j + 1) := by
    intro j hj
    show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E j)
      = Erdos634.OrientBridge.edgePos D.toDissection dir (E (j + 1))
    rw [← dir_edgeEast, ← dir_edgeWest, hjunc j hj]
  have hRL : ∀ m, m < n → R m - L m = sideOpp D.model 0 ∨ R m - L m = sideOpp D.model 1 ∨
      R m - L m = sideOpp D.model 2 := by
    intro m hm
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g c (E m)).mp (hmem m hm)
    obtain ⟨j, hj⟩ := exists_matching_side D (E m).1 (E m).2
    have hdist : dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1))
        = R m - L m := by
      rw [hiso _ _ hwm.1 hwm.2]
      show |dir ((D.tile (E m).1).pts (E m).2) - dir ((D.tile (E m).1).pts ((E m).2 + 1))|
        = Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m)
          - Erdos634.OrientBridge.edgePos D.toDissection dir (E m)
      rw [show Erdos634.OrientBridge.edgePos D.toDissection dir (E m)
            = min (dir ((D.tile (E m).1).pts (E m).2)) (dir ((D.tile (E m).1).pts ((E m).2 + 1)))
          from rfl,
        show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m)
            = max (dir ((D.tile (E m).1).pts (E m).2)) (dir ((D.tile (E m).1).pts ((E m).2 + 1)))
          from rfl]
      rcases le_total (dir ((D.tile (E m).1).pts (E m).2))
          (dir ((D.tile (E m).1).pts ((E m).2 + 1))) with h | h
      · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
    rw [← hdist, hj]
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hchain := Erdos634.ChainWalk.chain_walk n hn0 L R (sideOpp D.model 0) (sideOpp D.model 1)
    (sideOpp D.model 2) hscalene.1 hscalene.2.1 hscalene.2.2 hcontig
    (fun m hm => by
      rw [Finset.mem_range] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hRL m hm)
  refine ⟨((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 0)).card,
    ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 1)).card,
    ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 2)).card, ?_⟩
  have hRb : R (n - 1) = dir b := by
    show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E (n - 1)) = dir b
    rw [← dir_edgeEast, heastlast]
  have hL0 : L 0 = dir a := by
    show Erdos634.OrientBridge.edgePos D.toDissection dir (E 0) = dir a
    rw [← dir_edgeWest, hwest0]
  rw [hiso a b (hline a (left_mem_segment ℝ a b)) (hline b (right_mem_segment ℝ a b))]
  rw [abs_of_nonpos (by linarith)]
  rw [← hchain, hRb, hL0]
  ring

end Erdos634.SideWalk
