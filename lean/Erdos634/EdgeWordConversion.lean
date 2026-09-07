import Mathlib.Tactic
import Erdos634.TP_erdos
import Erdos634.CongruentAngles
import Erdos634.SssCongruent

/-!
# The ℕ-length-word conversion (outcome-2 debt)

Erdős #634. Room `tileplace`'s moderator verdict (2026-09-07) named this the single highest-value
target left standing: the shared node of `prop:cornerpara`, `DoubleC.hcov`, `rem:pingaps` bridge
(c), and `prop:chorddecomp`. `TP_erdos.chain_edge_lengths_sum` gives the length equation as a real
`ENNReal` sum over the chain; every dissection's tiles are congruent to one model, so each chain
edge's length is one of the model's three side lengths. What was missing is turning that into the
word equation `n_a·a + n_b·b + n_c·c = L` the corpus's walk machinery actually consumes
(`side_walk_abc`, `DoubleC.Config.hcov`, `partition_jb_gen`).

## Scope, stated exactly

**Formalized here:** for a `CongruentDissection`, `chain_edge_lengths_sum` converted to the
`n_a·a + n_b·b + n_c·c = L` form, by categorizing each chain edge (via `Finset.sum_fiberwise`
over `Fin 3`) by which of the model's three sides it matches.

**NOT formalized:** which of the three counts is nonzero, or any bound beyond their existence —
that is content-specific to each consumer and stays with them.
-/

namespace Erdos634.EdgeWordConversion

open Erdos634.Geometry Erdos634.TPErdos

variable {N : ℕ}

/-- **Every chain edge's length is one of the model's three side lengths**, indexed by which
side. `sideLen D 0 = dist(model 0)(model 1) =: a`, `sideLen D 1 =: b`, `sideLen D 2 =: c`. -/
noncomputable def sideLen (D : CongruentDissection N) : Fin 3 → ℝ :=
  fun i => dist (D.model.pts i) (D.model.pts (i + 1))

/-- The length of a chain edge: the tile's own side, by index. -/
noncomputable def len (D : CongruentDissection N) : Fin N × Fin 3 → ℝ :=
  fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))

theorem len_eq (D : CongruentDissection N) (e : Fin N × Fin 3) :
    len D e = dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := rfl

theorem dist_pair_mem_sideLen (T : Erdos634.Geometry.Tri) (i i' : Fin 3) (hii' : i ≠ i') :
    ∃ k : Fin 3, dist (T.pts i) (T.pts i') = dist (T.pts k) (T.pts (k + 1)) := by
  fin_cases i <;> fin_cases i' <;> simp_all
  · exact ⟨0, rfl⟩
  · exact ⟨2, dist_comm _ _⟩
  · exact ⟨0, dist_comm _ _⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨1, dist_comm _ _⟩

theorem edge_succ_ne (j : Fin 3) : j ≠ j + 1 := by
  fin_cases j <;> decide

theorem chain_edge_length_mem_model (D : CongruentDissection N) (e : Fin N × Fin 3) :
    ∃ i : Fin 3, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = sideLen D i := by
  have hne : e.2 ≠ e.2 + 1 := edge_succ_ne e.2
  obtain ⟨i, i', hii', hdist⟩ :=
    congruent_edge_lengths (D.tiles_congruent e.1).symm e.2 (e.2 + 1) hne
  obtain ⟨k, hk⟩ := dist_pair_mem_sideLen D.model i i' hii'
  exact ⟨k, hdist.trans hk⟩

/-- **The ℕ-length-word conversion.** Given a `CongruentDissection` and a wall chord satisfying
`chain_edge_lengths_sum`'s hypotheses: there are naturals `n_0, n_1, n_2` — the counts of chain
edges matching each of the model's three sides — with `n_0·a + n_1·b + n_2·c = dist P Q`. -/
theorem word_of_chain_sum (D : CongruentDissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c0 : ℝ) {P Q : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c0) (hfQ : f Q = c0)
    (g : Plane →ₗ[ℝ] ℝ) (cg : ℝ) (hg : ∀ y ∈ D.target.carrier, g y ≤ cg)
    (hgP : g P = cg) (hgQ : g Q < cg)
    (h : Plane →ₗ[ℝ] ℝ) (ch : ℝ) (hh : ∀ y ∈ D.target.carrier, h y ≤ ch)
    (hhQ : h Q = ch) (hhP : h P < ch)
    (hS : segment ℝ P Q ⊆ {y | f y = c0})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∃ n : Fin 3 → ℕ,
      ∑ i : Fin 3, (n i : ℝ) * sideLen D i = dist P Q := by
  classical
  choose cat hcat using chain_edge_length_mem_model D
  refine ⟨fun i => (D.lineChain f c0).filter (fun e => cat e = i) |>.card, ?_⟩
  have hsum := TPErdos.chain_edge_lengths_sum D.toDissection f hf c0 hPQ hfP hfQ
    g cg hg hgP hgQ h ch hh hhQ hhP hS hint hwall
  have hreal : ∑ e ∈ D.lineChain f c0, len D e = dist P Q := by
    have hcongr : ∀ e ∈ D.lineChain f c0,
        (ENNReal.ofReal (len D e)).toReal = len D e :=
      fun e _ => ENNReal.toReal_ofReal dist_nonneg
    have heq : ∑ e ∈ D.lineChain f c0, ENNReal.ofReal (len D e)
        = ENNReal.ofReal (dist P Q) := hsum
    have := congrArg ENNReal.toReal heq
    rwa [ENNReal.toReal_sum (fun e _ => ENNReal.ofReal_ne_top),
      Finset.sum_congr rfl hcongr, ENNReal.toReal_ofReal dist_nonneg] at this
  have hfiber : ∑ i : Fin 3, ∑ e ∈ (D.lineChain f c0).filter (fun e => cat e = i), len D e
      = ∑ e ∈ D.lineChain f c0, len D e :=
    Finset.sum_fiberwise (D.lineChain f c0) cat (len D)
  have hconst : ∀ i : Fin 3,
      ∑ e ∈ (D.lineChain f c0).filter (fun e => cat e = i), len D e
        = ((D.lineChain f c0).filter (fun e => cat e = i)).card * sideLen D i := by
    intro i
    have hval : ∀ e ∈ (D.lineChain f c0).filter (fun e => cat e = i), len D e = sideLen D i := by
      intro e he
      rw [len_eq, hcat e, (Finset.mem_filter.mp he).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hgoal : ∑ i : Fin 3, (((D.lineChain f c0).filter (fun e => cat e = i)).card : ℝ) * sideLen D i
      = ∑ i : Fin 3, ∑ e ∈ (D.lineChain f c0).filter (fun e => cat e = i), len D e :=
    Finset.sum_congr rfl (fun i _ => (hconst i).symm)
  rw [hgoal, hfiber, hreal]


#print axioms Erdos634.EdgeWordConversion.chain_edge_length_mem_model
#print axioms Erdos634.EdgeWordConversion.word_of_chain_sum

/-! ## Non-vacuity: a real `CongruentDissection` instantiating `word_of_chain_sum`'s hypotheses

`TP_erdos.wallDissection : Dissection 2` (median cut of `(0,0),(2,0),(0,2)`) is a bare `Dissection`;
`word_of_chain_sum` needs a `CongruentDissection`.  The two tiles `wallTileA = (0,0),(1,1),(2,0)`
and `wallTileB = (0,0),(0,2),(1,1)` are congruent (reflection across the tile's own median, i.e.
the SSS witness swapping vertices `1,2`), so `wallDissection` extends to one, with model
`wallTileA`.  Wired in below and typechecked against `word_of_chain_sum` directly. -/

open Erdos634.SssCongruent Erdos634.CertCoord Erdos634.TPErdos in
theorem wallTileB_congruent_wallTileA : wallTileB.Congruent wallTileA := by
  apply congruent_of_sq_dist_perm (Equiv.swap (1 : Fin 3) 2)
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [wallTileA, wallTileB, dist_sq_mkPt, Equiv.swap_apply_def] <;> norm_num

open Erdos634.TPErdos in
noncomputable def wallCongruentDissection : CongruentDissection 2 where
  toDissection := wallDissection
  model := wallTileA
  tiles_congruent := by
    intro i
    fin_cases i
    · show wallTileA.Congruent wallTileA; exact Erdos634.Geometry.Tri.Congruent.refl _
    · show wallTileB.Congruent wallTileA; exact wallTileB_congruent_wallTileA

open Erdos634.TPErdos in
/-- **`word_of_chain_sum` is not vacuous.**  Applied in full to `wallCongruentDissection`, with
the Erdős seat's own separating data (`gBase`, `hHyp`) reused verbatim from
`chain_edge_lengths_sum_witness` — every one of `word_of_chain_sum`'s twelve hypotheses is
discharged by an existing, previously-verified lemma; nothing new is assumed here. -/
theorem word_of_chain_sum_witness :
    ∃ n : Fin 3 → ℕ,
      ∑ i : Fin 3, (n i : ℝ) * sideLen wallCongruentDissection i = dist wallU wallV :=
  word_of_chain_sum wallCongruentDissection wallF wallF_ne 0 wallU_ne_wallV wallF_u wallF_v
    gBase 0 gBase_bound_target (by rw [wallU, gBase_pt]; norm_num)
    (by rw [wallV, gBase_pt]; norm_num)
    hHyp 2 hHyp_bound (by rw [wallV, hHyp_pt]; norm_num)
    (by rw [wallU, hHyp_pt]; norm_num)
    wall_hS wall_hint wall_hwall

#print axioms Erdos634.EdgeWordConversion.word_of_chain_sum_witness

#print axioms Erdos634.EdgeWordConversion.wallTileB_congruent_wallTileA
#print axioms Erdos634.EdgeWordConversion.wallCongruentDissection


end Erdos634.EdgeWordConversion