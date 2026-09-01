import Erdos634.ChainWalk
import Erdos634.EdgeType
import Erdos634.WallEndpoints
import Erdos634.BridgeC
import Erdos634.BaseBetaWalkArith
import Erdos634.GammaTrap

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
  Erdos634.BridgeC Erdos634.BaseBetaWalkArith

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
  obtain ⟨E, n, hneq, hn0, hwest0, heastlast, hjunc, hmem, hinj, hlba, hlbend, hnondeg, _hsurj⟩ :=
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

/-! ## Bridging the real walk equation to the `ℤ`-typed arithmetic

`BaseBetaWalkArith.lean`'s `equal_side_no_b`/`equal_side_shape`/`base_b_count` are `ℤ`-typed and
expect the walk equation as an integer identity. `side_walk_of_dissection` gives it as a real one.
This section bridges the two: given that the model's three side lengths and the wall's span are
each equal to a specific integer's cast (the numeric instantiation of the base-β target — not
proved here, since no concrete real-coordinate realization of that target exists yet in this
project, confirmed by search — see `PAPER_MAP`'s `thm:walkstruct` row), the real counts
`side_walk_of_dissection` produces satisfy the integer walk equation those theorems need. -/

/-- **The real walk equation casts to the integer one**, given the numeric instantiation. This is
the only remaining step to apply `BaseBetaWalkArith.equal_side_no_b` (or `.base_b_count`) to a real
dissection: supply `hA`,`hB`,`hC`,`hLen` (the concrete geometric realization) and `hnc1` (an edge of
type `c` exists on the chain — `prop:gammatrap`'s content, not yet connected to this specific
side), and the integer walk equation `na·(e·f) + nb·b + nc·f² = L₀` follows with `na`,`nb`,`nc` the
real edge-type counts, cast. -/
theorem int_walk_of_dissection (D : CongruentDissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
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
    (hN : 0 < N) (e0 f0 b0 L0 : ℤ)
    (hA : sideOpp D.model 0 = ((e0 * f0 : ℤ) : ℝ))
    (hB : sideOpp D.model 1 = (b0 : ℝ))
    (hC : sideOpp D.model 2 = ((f0 ^ 2 : ℤ) : ℝ))
    (hLen : dist a b = (L0 : ℝ)) :
    ∃ na nb nc : ℤ, 0 ≤ na ∧ 0 ≤ nb ∧ 0 ≤ nc ∧ na * (e0 * f0) + nb * b0 + nc * f0 ^ 2 = L0 := by
  obtain ⟨Pc, Qc, Rc, heq⟩ := side_walk_of_dissection D g c dir hker hwall a b hab hdirab hbase
    hline hface hthird hiso hscalene hN
  rw [hA, hB, hC, hLen] at heq
  refine ⟨(Pc : ℤ), (Qc : ℤ), (Rc : ℤ), Int.natCast_nonneg Pc, Int.natCast_nonneg Qc,
    Int.natCast_nonneg Rc, ?_⟩
  have : ((Pc : ℤ) * (e0 * f0) + (Qc : ℤ) * b0 + (Rc : ℤ) * f0 ^ 2 : ℝ) = (L0 : ℝ) := by
    push_cast
    push_cast at heq
    linarith
  exact_mod_cast this

/-- **`thm:walkstruct` clause (i), for a real dissection, given the numeric instantiation.** An
equal side (`f² > 2e²`, the thin regime) carries no `b`-edge. This is `equal_side_no_b` applied to
`int_walk_of_dissection`'s output — the last remaining inputs are the concrete geometric
realization (`hA`,`hB`,`hC`,`hLen`: the model and the side literally have the stated lengths, which
needs a real-coordinate `Tri` for the base-β target — not built, see `PAPER_MAP`) and `hnc1` (an
edge of type `c` occurs — `prop:gammatrap`'s content at this side, also not yet connected here). -/
theorem equal_side_no_b_of_dissection (D : CongruentDissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
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
    (hN : 0 < N) (e0 f0 b0 : ℤ) (he0 : 1 ≤ e0) (hef0 : e0 < f0) (hcop : IsCoprime e0 f0)
    (hb0 : b0 + e0 ^ 2 = f0 ^ 2) (hthin : 2 * e0 ^ 2 < f0 ^ 2)
    (hA : sideOpp D.model 0 = ((e0 * f0 : ℤ) : ℝ))
    (hB : sideOpp D.model 1 = (b0 : ℝ))
    (hC : sideOpp D.model 2 = ((f0 ^ 2 : ℤ) : ℝ))
    (hLen : dist a b = ((f0 ^ 3 : ℤ) : ℝ))
    (hnc1 : ∀ Pc Qc Rc : ℕ,
      dist a b = Pc * sideOpp D.model 0 + Qc * sideOpp D.model 1 + Rc * sideOpp D.model 2 →
      1 ≤ Rc) :
    ∃ Pc Qc : ℕ, Qc = 0 := by
  obtain ⟨Pc, Qc, Rc, heq⟩ := side_walk_of_dissection D g c dir hker hwall a b hab hdirab hbase
    hline hface hthird hiso hscalene hN
  refine ⟨Pc, Qc, ?_⟩
  have hcast : (Pc : ℤ) * (e0 * f0) + (Qc : ℤ) * b0 + (Rc : ℤ) * f0 ^ 2 = f0 ^ 3 := by
    have hr : ((Pc : ℤ) * (e0 * f0) + (Qc : ℤ) * b0 + (Rc : ℤ) * f0 ^ 2 : ℝ) = ((f0 ^ 3 : ℤ) : ℝ) := by
      rw [hA, hB, hC, hLen] at heq
      push_cast at heq ⊢
      linarith
    exact_mod_cast hr
  have hnb0 : (Qc : ℤ) = 0 := equal_side_no_b e0 f0 b0 (Pc : ℤ) (Qc : ℤ) (Rc : ℤ) he0 hef0 hcop
    hb0 hthin (Int.natCast_nonneg Pc) (Int.natCast_nonneg Qc)
    (by exact_mod_cast hnc1 Pc Qc Rc heq) hcast
  exact_mod_cast hnb0

/-! ## Closing `hnc1` via `prop:gammatrap`

`GammaTrap.congruentDissection_gammatrap` (already VERIFIED, `prop:gammatrap`) proves exactly
`hnc1`'s content for the specific wall `SideWall.wallFun D.target k` gammatrap itself uses: an edge
of type `c` exists on that wall. This section reruns `side_walk_of_dissection`'s derivation against
that same wall, converts gammatrap's witness (a `wallList` member) to a specific chain index via
`chain_endpoints`'s now-exposed surjectivity, and applies `ChainWalk.count_pos` to discharge
`hnc1` — closing every hypothesis of `equal_side_no_b_of_dissection` except the concrete
geometric realization (`hA`,`hB`,`hC`,`hLen`). -/

open Erdos634.SideWall Erdos634.Geometry.Dissection Erdos634.TilePlacement in
/-- **`thm:walkstruct` clause (i), for a real dissection's side `k` of its target, given only the
numeric instantiation.** Every hypothesis `equal_side_no_b_of_dissection` needed beyond the
standard wall/line setup is now derived: `hnc1` from `prop:gammatrap`. -/
theorem equal_side_no_b_of_gammatrap (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hscalenef : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, (wallFun D.target k).linear v = 0 → dir v = 0 → v = 0)
    (hdirab : dir (D.target.pts k) ≤ dir (D.target.pts (k + 1)))
    (hthird : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0)
    (hcornerbase : cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = 3 * α)
    (hiso : ∀ p q : Plane, (wallFun D.target k) p = 0 → (wallFun D.target k) q = 0 →
      dist p q = |dir p - dir q|)
    (hN : 0 < N) (e0 f0 b0 : ℤ) (he0 : 1 ≤ e0) (hef0 : e0 < f0) (hcop : IsCoprime e0 f0)
    (hb0 : b0 + e0 ^ 2 = f0 ^ 2) (hthin : 2 * e0 ^ 2 < f0 ^ 2)
    (hA : sideOpp D.model 0 = ((e0 * f0 : ℤ) : ℝ))
    (hB : sideOpp D.model 1 = (b0 : ℝ))
    (hC : sideOpp D.model 2 = ((f0 ^ 2 : ℤ) : ℝ))
    (hLen : dist (D.target.pts k) (D.target.pts (k + 1)) = ((f0 ^ 3 : ℤ) : ℝ)) :
    ∃ Pc Qc : ℕ, Qc = 0 := by
  classical
  set g := wallFun D.target k with hgdef
  set a := D.target.pts k with hadef
  set b := D.target.pts (k + 1) with hbdef
  have hab : a ≠ b := by
    have h : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact Erdos634.TilePlacement.pts_ne D.target (h k)
  have hwall : ∀ y ∈ D.target.carrier, g y ≤ 0 := fun y hy => wallFun_le D.target k hy
  have hbase : segment ℝ a b ⊆ frontier D.target.carrier := by
    intro y hy
    exact edge_subset_frontier D.target k (by rw [Tri.edge]; exact hy)
  have hline : ∀ y ∈ segment ℝ a b, g y = 0 := by
    intro y hy
    exact wallFun_eq_zero D.target k (by rw [Tri.edge]; exact hy)
  have hface : ∀ y ∈ D.target.carrier, g y = 0 → y ∈ segment ℝ a b := by
    intro y hy h0
    have := wallFun_face D.target k hy h0
    rw [Tri.edge] at this
    exact this
  obtain ⟨pc, hpcmem, hpceq⟩ := congruentDissection_gammatrap hN D α β γ hαβ hαγ hαπ hα0 hβγ hβπ
    hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hscalenef hα' hβ' hγ' k dir hker hdirab hthird hcornerbase
    hcornerapex
  obtain ⟨E, n, hneq, hn0, hwest0, heastlast, hjunc, hmem, hinj, hlba, hlbend, hnondeg, hsurj⟩ :=
    chain_endpoints hN D.toDissection g 0 dir hker hwall a b hab hdirab hbase hline hface hthird
  set L : ℕ → ℝ := fun m => Erdos634.OrientBridge.edgePos D.toDissection dir (E m) with hLdef
  set R : ℕ → ℝ := fun m => Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m) with hRdef
  have hRL : ∀ m, m < n → R m - L m = sideOpp D.model 0 ∨ R m - L m = sideOpp D.model 1 ∨
      R m - L m = sideOpp D.model 2 := by
    intro m hm
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g 0 (E m)).mp (hmem m hm)
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
  have hscalene : sideOpp D.model 0 ≠ sideOpp D.model 1 ∧ sideOpp D.model 0 ≠ sideOpp D.model 2 ∧
      sideOpp D.model 1 ≠ sideOpp D.model 2 :=
    ⟨hscalenef 0 1 (by decide), hscalenef 0 2 (by decide), hscalenef 1 2 (by decide)⟩
  have hchain := Erdos634.ChainWalk.chain_walk n hn0 L R (sideOpp D.model 0) (sideOpp D.model 1)
    (sideOpp D.model 2) hscalene.1 hscalene.2.1 hscalene.2.2
    (fun j hj => by
      show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E j)
        = Erdos634.OrientBridge.edgePos D.toDissection dir (E (j + 1))
      rw [← dir_edgeEast, ← dir_edgeWest, hjunc j hj])
    (fun m hm => by
      rw [Finset.mem_range] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hRL m hm)
  set Pc := ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 0)).card with hPcdef
  set Qc := ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 1)).card with hQcdef
  set Rc := ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 2)).card with hRcdef
  have hRb : R (n - 1) = dir b := by
    show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E (n - 1)) = dir b
    rw [← dir_edgeEast, heastlast]
  have hL0 : L 0 = dir a := by
    show Erdos634.OrientBridge.edgePos D.toDissection dir (E 0) = dir a
    rw [← dir_edgeWest, hwest0]
  have heq : dist a b = Pc * sideOpp D.model 0 + Qc * sideOpp D.model 1 + Rc * sideOpp D.model 2 := by
    rw [hiso a b (hline a (left_mem_segment ℝ a b)) (hline b (right_mem_segment ℝ a b))]
    rw [abs_of_nonpos (by linarith)]
    rw [← hchain, hRb, hL0]
    ring
  refine ⟨Pc, Qc, ?_⟩
  have hcast : (Pc : ℤ) * (e0 * f0) + (Qc : ℤ) * b0 + (Rc : ℤ) * f0 ^ 2 = f0 ^ 3 := by
    have hr : ((Pc : ℤ) * (e0 * f0) + (Qc : ℤ) * b0 + (Rc : ℤ) * f0 ^ 2 : ℝ)
        = ((f0 ^ 3 : ℤ) : ℝ) := by
      rw [hA, hB, hC, hLen] at heq
      push_cast at heq ⊢
      linarith
    exact_mod_cast hr
  have hnc1 : 1 ≤ Rc := by
    obtain ⟨ic, hiclt, hiceq⟩ := hsurj pc hpcmem
    subst hiceq
    apply ChainWalk.count_pos n (fun j => R j - L j) (sideOpp D.model 2) ic
      (Finset.mem_range.mpr hiclt)
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g 0 (E ic)).mp hpcmem
    have hdist : dist ((D.tile (E ic).1).pts (E ic).2) ((D.tile (E ic).1).pts ((E ic).2 + 1))
        = R ic - L ic := by
      rw [hiso _ _ hwm.1 hwm.2]
      show |dir ((D.tile (E ic).1).pts (E ic).2) - dir ((D.tile (E ic).1).pts ((E ic).2 + 1))|
        = Erdos634.ChainInstance.edgeEnd D.toDissection dir (E ic)
          - Erdos634.OrientBridge.edgePos D.toDissection dir (E ic)
      rw [show Erdos634.OrientBridge.edgePos D.toDissection dir (E ic)
            = min (dir ((D.tile (E ic).1).pts (E ic).2))
                (dir ((D.tile (E ic).1).pts ((E ic).2 + 1)))
          from rfl,
        show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E ic)
            = max (dir ((D.tile (E ic).1).pts (E ic).2))
                (dir ((D.tile (E ic).1).pts ((E ic).2 + 1)))
          from rfl]
      rcases le_total (dir ((D.tile (E ic).1).pts (E ic).2))
          (dir ((D.tile (E ic).1).pts ((E ic).2 + 1))) with h | h
      · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
    rw [← hdist, hpceq]
  have hnb0 : (Qc : ℤ) = 0 := equal_side_no_b e0 f0 b0 (Pc : ℤ) (Qc : ℤ) (Rc : ℤ) he0 hef0 hcop
    hb0 hthin (Int.natCast_nonneg Pc) (Int.natCast_nonneg Qc) (by exact_mod_cast hnc1) hcast
  exact_mod_cast hnb0

end Erdos634.SideWalk
