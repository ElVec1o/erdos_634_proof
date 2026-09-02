import Erdos634.Tiling44
import Erdos634.Z15Real
import Erdos634.CertGeom
import Erdos634.SssCongruent

/-!
# Instantiating `Tiling44`'s target and first piece as real `Tri` objects

Erdős #634. The per-tiling data-entry work `private/VERIFY_PLAN.md` records: `Tiling44`'s
certificate checks (C1)–(C4) over `ℤ[√15]`, and `Z15Real.toPlanePt`/`zcross`/`toR_zcross` are the
bridge from those checks to `CertCoord`/`CertGeom`. This file is the first end-to-end test of that
bridge — the target triangle and the certificate's first piece, both built as genuine `Tri`
objects with their determinant-positivity hypothesis discharged by `decide` + `toR_zcross`, before
scaling the same pattern to all 44 pieces.

Not a paper-row flip: this is one target and one of 44 pieces, not the whole certificate.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Tiling44Bridge

open Erdos634.Z15Real Erdos634.Geometry

/-- A `Tiling44.Pt` read as a `Z15Real.ZPt` — the same underlying type. -/
def toZPt (p : Tiling44.Pt) : ZPt := p

/-- **The real determinant of a `Tiling44.Tri`'s three vertices**, transferred from its `ℤ[√15]`
cross product. -/
theorem det3_eq_toR_cross (t : Tiling44.Tri) :
    Erdos634.CertCoord.det3
      (toR (zx (toZPt (Tiling44.t1 t)))) (toR (zy (toZPt (Tiling44.t1 t))))
      (toR (zx (toZPt (Tiling44.t2 t)))) (toR (zy (toZPt (Tiling44.t2 t))))
      (toR (zx (toZPt (Tiling44.t3 t)))) (toR (zy (toZPt (Tiling44.t3 t))))
    = toR (zcross (toZPt (Tiling44.t1 t)) (toZPt (Tiling44.t2 t)) (toZPt (Tiling44.t3 t))) :=
  toR_zcross _ _ _

/-- **The target's determinant is `4224√15`**, positive. -/
theorem target_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (Tiling44.t1 Tiling44.target))))
      (toR (zy (toZPt (Tiling44.t1 Tiling44.target))))
      (toR (zx (toZPt (Tiling44.t2 Tiling44.target))))
      (toR (zy (toZPt (Tiling44.t2 Tiling44.target))))
      (toR (zx (toZPt (Tiling44.t3 Tiling44.target))))
      (toR (zy (toZPt (Tiling44.t3 Tiling44.target)))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (Tiling44.t1 Tiling44.target))
    (toZPt (Tiling44.t2 Tiling44.target)) (toZPt (Tiling44.t3 Tiling44.target))) (by decide)

/-- **The target, as a real `Tri`.** -/
noncomputable def targetTri : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (Tiling44.t1 Tiling44.target))))
    (toR (zy (toZPt (Tiling44.t1 Tiling44.target))))
    (toR (zx (toZPt (Tiling44.t2 Tiling44.target))))
    (toR (zy (toZPt (Tiling44.t2 Tiling44.target))))
    (toR (zx (toZPt (Tiling44.t3 Tiling44.target))))
    (toR (zy (toZPt (Tiling44.t3 Tiling44.target))))
    target_det_pos.ne'

/-- **The first piece's determinant is `48√15`**, positive — a smaller instance of the same
computation, confirming the pattern generalizes piece-by-piece. -/
theorem piece0_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (Tiling44.t1 (Tiling44.tiles.headI)))))
      (toR (zy (toZPt (Tiling44.t1 (Tiling44.tiles.headI)))))
      (toR (zx (toZPt (Tiling44.t2 (Tiling44.tiles.headI)))))
      (toR (zy (toZPt (Tiling44.t2 (Tiling44.tiles.headI)))))
      (toR (zx (toZPt (Tiling44.t3 (Tiling44.tiles.headI)))))
      (toR (zy (toZPt (Tiling44.t3 (Tiling44.tiles.headI))))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (Tiling44.t1 (Tiling44.tiles.headI)))
    (toZPt (Tiling44.t2 (Tiling44.tiles.headI))) (toZPt (Tiling44.t3 (Tiling44.tiles.headI))))
    (by decide)

/-- **Every one of the 44 pieces is positively oriented** — `decide` on the whole list, ~15s to
build, not per-piece: this is the scaling probe `private/VERIFY_PLAN.md` asked for, answered. It
means the indexed-`∀`-over-`Fin 44` shape (rather than 44 separate named theorems) is the right
approach for (C1)/(C2), and there is no elaboration-cost obstruction at this level. -/
theorem all_pieces_pos :
    ∀ t ∈ Tiling44.tiles,
      zpos (zcross (toZPt (Tiling44.t1 t)) (toZPt (Tiling44.t2 t)) (toZPt (Tiling44.t3 t)))
        = true := by
  decide

/-- **Every piece, as a real `Tri`**, uniformly — the general form `thm:44`'s data entry needs,
combining `all_pieces_pos` with `det3_eq_toR_cross` instead of writing 44 separate constructions. -/
noncomputable def pieceTri {t : Tiling44.Tri} (ht : t ∈ Tiling44.tiles) : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (Tiling44.t1 t)))) (toR (zy (toZPt (Tiling44.t1 t))))
    (toR (zx (toZPt (Tiling44.t2 t)))) (toR (zy (toZPt (Tiling44.t2 t))))
    (toR (zx (toZPt (Tiling44.t3 t)))) (toR (zy (toZPt (Tiling44.t3 t))))
    (by
      rw [det3_eq_toR_cross]
      exact (toR_pos (all_pieces_pos t ht)).ne')

/-- **The `lineFun` of a certificate edge is nonconstant**, for two *concrete* endpoints `P ≠ Q`
whose real coordinates differ — resolved via `Z15Real.toR_ne_zero_of_sq_ne` rather than injectivity
of `toR` (which this project deliberately never proves). `hx`/`hy` are the decidable `ℤ[√15]`
side conditions (`zx Q - zx P` resp. `zy Q - zy P` squared-nonequal to `15 * (other coord)²`); one
of the two always holds for a genuine edge, matching whichever coordinate actually differs. -/
theorem lineFun_ne_zero_of_sq_ne {P Q : ZPt}
    (h : (zsub (zx P) (zx Q)).1 ^ 2 ≠ 15 * (zsub (zx P) (zx Q)).2 ^ 2
       ∨ (zsub (zy P) (zy Q)).1 ^ 2 ≠ 15 * (zsub (zy P) (zy Q)).2 ^ 2) :
    (Erdos634.CertGeom.lineFun (toR (zx P)) (toR (zy P)) (toR (zx Q)) (toR (zy Q))).linear ≠ 0 := by
  apply Erdos634.CertGeom.lineFun_linear_ne_zero
  rcases h with h | h
  · exact Or.inl (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))
  · exact Or.inr (sub_ne_zero.mp (by rw [← toR_sub]; exact toR_ne_zero_of_sq_ne h))

/-- Pointwise negation of an affine map into `ℝ`. -/
theorem affNeg_apply (g : Plane →ᵃ[ℝ] ℝ) (p : Plane) : (-g) p = -(g p) := by
  have := congrFun (AffineMap.coe_neg g) p
  simpa using this

/-- `Tiling44.cross` is literally `Z15Real.zcross` read through `toZPt` — the two files define the
same operations on the same underlying type, so this is `rfl`. -/
theorem cross_eq_zcross (o a b : Tiling44.Pt) :
    Tiling44.cross o a b = zcross (toZPt o) (toZPt a) (toZPt b) := rfl

/-- `Tiling44.dist2` is literally `Z15Real.zdist2` read through `toZPt` — again `rfl`. -/
theorem dist2_eq_zdist2 (p q : Tiling44.Pt) :
    Tiling44.dist2 p q = zdist2 (toZPt p) (toZPt q) := rfl

/-- **A piece's vertex, named by index.** -/
def vertexOf (t : Tiling44.Tri) (i : Fin 3) : Tiling44.Pt :=
  ![Tiling44.t1 t, Tiling44.t2 t, Tiling44.t3 t] i

/-- **`pieceTri`'s vertices are exactly `vertexOf`, read as real points.** -/
theorem pieceTri_pts (t : Tiling44.Tri) (ht : t ∈ Tiling44.tiles) (i : Fin 3) :
    (pieceTri ht).pts i
      = Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i)))) := by
  fin_cases i <;> rfl

/-- **Squared distances between a piece's vertices, transferred to `ℝ` from the certificate's own
`dist2`.** -/
theorem pieceTri_dist_sq (t : Tiling44.Tri) (ht : t ∈ Tiling44.tiles) (i j : Fin 3) :
    dist ((pieceTri ht).pts i) ((pieceTri ht).pts j) ^ 2 = toR (Tiling44.dist2 (vertexOf t i) (vertexOf t j)) := by
  rw [pieceTri_pts t ht i, pieceTri_pts t ht j, Erdos634.CertCoord.dist_sq_mkPt,
    dist2_eq_zdist2]
  exact toR_zdist2 _ _

/-- **A single `sepBy`-true witness gives a genuine separating affine functional** between two
pieces, read as real `Tri` objects — the assembly step `CertGeom.pairwise_disjoint_of_separating`
needs, for one pair. `hPQ` is `lineFun_ne_zero_of_sq_ne`'s decidable side condition on the edge
`(P, Q)`; the certificate's own `sepBy` supplies which sign pattern holds. -/
theorem sep_of_sepBy {P Q : Tiling44.Pt} {A B : Tiling44.Tri}
    (hPQ : (zsub (zx (toZPt P)) (zx (toZPt Q))).1 ^ 2
             ≠ 15 * (zsub (zx (toZPt P)) (zx (toZPt Q))).2 ^ 2
         ∨ (zsub (zy (toZPt P)) (zy (toZPt Q))).1 ^ 2
             ≠ 15 * (zsub (zy (toZPt P)) (zy (toZPt Q))).2 ^ 2)
    (hsep : Tiling44.sepBy P Q A B = true) (hA : A ∈ Tiling44.tiles) (hB : B ∈ Tiling44.tiles) :
    ∃ (f : Plane →ᵃ[ℝ] ℝ) (_ : f.linear ≠ 0) (c : ℝ),
      (∀ x ∈ (pieceTri hA).carrier, f x ≤ c) ∧ (∀ x ∈ (pieceTri hB).carrier, c ≤ f x) := by
  set f : Plane →ᵃ[ℝ] ℝ :=
    Erdos634.CertGeom.lineFun (toR (zx (toZPt P))) (toR (zy (toZPt P)))
      (toR (zx (toZPt Q))) (toR (zy (toZPt Q))) with hfdef
  have hflin : f.linear ≠ 0 := lineFun_ne_zero_of_sq_ne hPQ
  have hfval : ∀ v : Tiling44.Pt,
      f (Erdos634.CertCoord.mkPt (toR (zx (toZPt v))) (toR (zy (toZPt v))))
        = toR (Tiling44.cross P Q v) := by
    intro v
    rw [hfdef, Erdos634.CertGeom.lineFun_apply, Erdos634.CertCoord.mkPt_zero,
      Erdos634.CertCoord.mkPt_one, cross_eq_zcross]
    exact toR_zcross _ _ _
  have hpts : ∀ (t : Tiling44.Tri) (ht : t ∈ Tiling44.tiles) (k : Fin 3),
      (pieceTri ht).pts k
        = Erdos634.CertCoord.mkPt (toR (zx (toZPt (![Tiling44.t1 t, Tiling44.t2 t, Tiling44.t3 t] k))))
            (toR (zy (toZPt (![Tiling44.t1 t, Tiling44.t2 t, Tiling44.t3 t] k)))) := by
    intro t ht k; fin_cases k <;> rfl
  simp only [Tiling44.sepBy, List.all_eq_true, List.mem_cons, Bool.and_eq_true,
    Bool.or_eq_true, List.map, forall_eq_or_imp] at hsep
  rcases hsep with ⟨hsA, hsB⟩ | ⟨hsA, hsB⟩
  · -- A's vertices have cross ≥ 0, B's have cross ≤ 0 (znonpos)
    refine ⟨-f, neg_ne_zero.mpr hflin, 0, ?_, ?_⟩
    · exact Erdos634.CertGeom.le_of_forall_pts_le (-f) (t := pieceTri hA) (c := 0)
        (fun k => by
          rw [affNeg_apply, hpts A hA k, hfval, neg_le, neg_zero]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonneg hsA.1 | exact Erdos634.Z15Real.toR_nonneg hsA.2.1 | exact Erdos634.Z15Real.toR_nonneg hsA.2.2.1)
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le f (t := pieceTri hB) (c := 0)
        (fun k => by
          rw [hpts B hB k, hfval]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonpos hsB.1 | exact Erdos634.Z15Real.toR_nonpos hsB.2.1 | exact Erdos634.Z15Real.toR_nonpos hsB.2.2.1)
      have := hb x hx
      rw [affNeg_apply]
      linarith
  · -- A's vertices have cross ≤ 0 (znonpos), B's have cross ≥ 0
    refine ⟨f, hflin, 0, ?_, ?_⟩
    · exact Erdos634.CertGeom.le_of_forall_pts_le f (t := pieceTri hA) (c := 0)
        (fun k => by
          rw [hpts A hA k, hfval]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonpos hsA.1 | exact Erdos634.Z15Real.toR_nonpos hsA.2.1 | exact Erdos634.Z15Real.toR_nonpos hsA.2.2.1)
    · intro x hx
      have hb := Erdos634.CertGeom.le_of_forall_pts_le (-f) (t := pieceTri hB) (c := 0)
        (fun k => by
          rw [affNeg_apply, hpts B hB k, hfval, neg_le, neg_zero]
          fin_cases k <;> first | exact Erdos634.Z15Real.toR_nonneg hsB.1 | exact Erdos634.Z15Real.toR_nonneg hsB.2.1 | exact Erdos634.Z15Real.toR_nonneg hsB.2.2.1)
      have := hb x hx
      rw [affNeg_apply] at this
      linarith

/-! ## Every pair of distinct pieces is separated — the 946-pair assembly, decided at once

Rather than unpacking `Tiling44.wit`/`checkPairs`'s exact witness list (946 individual
extractions), it is far cheaper to `decide` the *existence* of a separating edge candidate per
pair directly: for each of the 44×44 ordered pairs, some one of the 6 candidate edges (3 from each
triangle) both separates them (`sepBy`) and satisfies `sep_of_sepBy`'s decidable side condition
(`sqCond`). This one `decide` (~12s) replaces per-pair data entry entirely. -/

/-- The 6 candidate separating edges for a pair: each triangle's own 3 edges. -/
def edgeCands (A B : Tiling44.Tri) : List (Tiling44.Pt × Tiling44.Pt) :=
  [Tiling44.edgeOf A 0, Tiling44.edgeOf A 1, Tiling44.edgeOf A 2,
   Tiling44.edgeOf B 0, Tiling44.edgeOf B 1, Tiling44.edgeOf B 2]

/-- The decidable side condition `sep_of_sepBy` needs for an edge `(P, Q)`, as a `Bool` — a direct
`decide` of the exact `Prop` `sep_of_sepBy` wants, so `sqCond_iff` is immediate. -/
def sqCond (pq : Tiling44.Pt × Tiling44.Pt) : Bool :=
  decide ((zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2
             ≠ 15 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
         ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
             ≠ 15 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2)

/-- Some candidate edge both separates `A` and `B` and satisfies the side condition. -/
def pairOK (A B : Tiling44.Tri) : Bool :=
  (edgeCands A B).any (fun pq => Tiling44.sepBy pq.1 pq.2 A B && sqCond pq)

/-- **Every one of the 44×44 ordered pairs of distinct pieces has a working separating edge** —
one `decide`, ~12s, no per-pair data entry. -/
theorem all_pairs_ok : ∀ A ∈ Tiling44.tiles, ∀ B ∈ Tiling44.tiles, A ≠ B → pairOK A B = true := by
  decide

/-- `sqCond`'s `Bool` and `sep_of_sepBy`'s `Prop` side condition agree. -/
theorem sqCond_iff (pq : Tiling44.Pt × Tiling44.Pt) :
    sqCond pq = true ↔
      (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2 ≠ 15 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
        ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
            ≠ 15 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2 := by
  rw [sqCond, decide_eq_true_iff]

/-- **Every two distinct pieces of `Tiling44` have disjoint interiors, as real `Tri` objects.**
This is (C3) fully assembled: existence of the separating edge (`all_pairs_ok`), transferred to a
genuine affine functional bounded on the whole carrier (`sep_of_sepBy`). -/
theorem pieces_interiors_disjoint {A B : Tiling44.Tri} (hA : A ∈ Tiling44.tiles)
    (hB : B ∈ Tiling44.tiles) (hne : A ≠ B) :
    Disjoint (interior (pieceTri hA).carrier) (interior (pieceTri hB).carrier) := by
  have hok := all_pairs_ok A hA B hB hne
  simp only [pairOK, List.any_eq_true] at hok
  obtain ⟨pq, hmem, hsep⟩ := hok
  rw [Bool.and_eq_true] at hsep
  obtain ⟨hsepBy, hsq⟩ := hsep
  obtain ⟨f, hf, c, h1, h2⟩ := sep_of_sepBy ((sqCond_iff pq).mp hsq) hsepBy hA hB
  exact Erdos634.CertGeom.interiors_disjoint_of_separating f hf c h1 h2

/-! ## (C1): every piece is congruent to a fixed model — the first piece, decided at once -/

/-- **The model tile**: `Tiling44`'s first certificate piece. Any piece works as the model since
all are mutually congruent; picking one already in `tiles` avoids naming new coordinates. -/
theorem headI_mem_tiles : Tiling44.tiles.headI ∈ Tiling44.tiles := by decide

/-- **Some permutation matches a piece's squared side lengths to the model's, positionally.**
`decide` over the `Fintype (Equiv.Perm (Fin 3))` (6 elements) × 44 pieces × 9 pairs — cheap. -/
def congOK' (t : Tiling44.Tri) : Bool :=
  decide (∃ σ : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
    Tiling44.dist2 (vertexOf t i) (vertexOf t j)
      = Tiling44.dist2 (vertexOf Tiling44.tiles.headI (σ i)) (vertexOf Tiling44.tiles.headI (σ j)))

/-- **Every one of the 44 pieces has a matching permutation** — one `decide`, no per-piece data
entry, matching the pattern established for (C2)/(C3). -/
theorem all_pieces_cong : ∀ t ∈ Tiling44.tiles, congOK' t = true := by decide

/-- **(C1) fully assembled**: every piece of `Tiling44`, as a real `Tri`, is congruent to the
model tile. -/
theorem pieceTri_congruent {t : Tiling44.Tri} (ht : t ∈ Tiling44.tiles) :
    (pieceTri ht).Congruent (pieceTri headI_mem_tiles) := by
  have hex := all_pieces_cong t ht
  simp only [congOK', decide_eq_true_eq] at hex
  obtain ⟨σ, hσ⟩ := hex
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm σ (fun i j => ?_)
  rw [pieceTri_dist_sq t ht, pieceTri_dist_sq Tiling44.tiles.headI headI_mem_tiles]
  exact congrArg Erdos634.Z15Real.toR (hσ i j)

/-! ## (C2) containment: every piece lies in the target — the part `all_pieces_pos` skipped

`all_pieces_pos` only captured orientation (`insideOK`'s first conjunct); this is the actual
vertex-in-target containment, `insideOK`'s second conjunct. -/

/-- **Cyclic invariance of `cross`**: `cross o a b = cross a b o`. Twice the signed area of a
triangle does not depend on which vertex is named first, only the cyclic order. Needed to match
`insideOK`'s three checks (each anchored at a different target edge) against
`CertCoord.mem_carrier_of_dets`'s fixed vertex-0/1/2 convention. -/
theorem cross_cyclic (o a b : Tiling44.Pt) : Tiling44.cross o a b = Tiling44.cross a b o := by
  simp only [Tiling44.cross, Tiling44.zsub, Tiling44.zmul, Tiling44.px, Tiling44.py, Prod.ext_iff]
  constructor <;> ring

/-- **Every one of the 44 pieces' vertices lies in the closed target** — one `decide`. -/
theorem all_pieces_inside : ∀ t ∈ Tiling44.tiles, Tiling44.insideOK t = true := by decide

/-- Abbreviations for the target's three vertices. -/
theorem insideOK_vertex {t : Tiling44.Tri} (ht : t ∈ Tiling44.tiles) (i : Fin 3) :
    Tiling44.znonneg (Tiling44.cross (Tiling44.t1 Tiling44.target) (Tiling44.t2 Tiling44.target)
        (vertexOf t i)) = true
    ∧ Tiling44.znonneg (Tiling44.cross (Tiling44.t2 Tiling44.target) (Tiling44.t3 Tiling44.target)
        (vertexOf t i)) = true
    ∧ Tiling44.znonneg (Tiling44.cross (Tiling44.t3 Tiling44.target) (Tiling44.t1 Tiling44.target)
        (vertexOf t i)) = true := by
  have hins := all_pieces_inside t ht
  simp only [Tiling44.insideOK, Bool.and_eq_true, List.all_eq_true] at hins
  have hv : vertexOf t i ∈ ([Tiling44.t1 t, Tiling44.t2 t, Tiling44.t3 t] : List Tiling44.Pt) := by
    fin_cases i <;> simp [vertexOf]
  have h3 := hins.2 (vertexOf t i) hv
  simp only [Bool.and_eq_true] at h3
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

/-- **The target, real vertex-by-vertex, matches `mem_carrier_of_dets`'s convention.** -/
theorem vertexOf_mem_targetTri {t : Tiling44.Tri} (ht : t ∈ Tiling44.tiles) (i : Fin 3) :
    Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
      ∈ targetTri.carrier := by
  obtain ⟨h1, h2, h3⟩ := insideOK_vertex ht i
  refine Erdos634.CertCoord.mem_carrier_of_dets (x₀ := toR (zx (toZPt (Tiling44.t1 Tiling44.target))))
    (y₀ := toR (zy (toZPt (Tiling44.t1 Tiling44.target))))
    (x₁ := toR (zx (toZPt (Tiling44.t2 Tiling44.target))))
    (y₁ := toR (zy (toZPt (Tiling44.t2 Tiling44.target))))
    (x₂ := toR (zx (toZPt (Tiling44.t3 Tiling44.target))))
    (y₂ := toR (zy (toZPt (Tiling44.t3 Tiling44.target))))
    target_det_pos ?_ ?_ ?_
  · -- h0 : 0 ≤ det3 a b x1 y1 x2 y2 = cross(v, T2, T3) = cross(T2, T3, v) [cyclic]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
        (toR (zx (toZPt (Tiling44.t2 Tiling44.target)))) (toR (zy (toZPt (Tiling44.t2 Tiling44.target))))
        (toR (zx (toZPt (Tiling44.t3 Tiling44.target)))) (toR (zy (toZPt (Tiling44.t3 Tiling44.target))))
      = toR (zcross (toZPt (vertexOf t i)) (toZPt (Tiling44.t2 Tiling44.target))
          (toZPt (Tiling44.t3 Tiling44.target))) from toR_zcross _ _ _,
      ← cross_eq_zcross, cross_cyclic (vertexOf t i) (Tiling44.t2 Tiling44.target) (Tiling44.t3 Tiling44.target)]
    exact Erdos634.Z15Real.toR_nonneg h2
  · -- h1 : 0 ≤ det3 x0 y0 a b x2 y2 = cross(T1, v, T3) = cross(T3, T1, v) [two cyclic rotations]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (Tiling44.t1 Tiling44.target))))
        (toR (zy (toZPt (Tiling44.t1 Tiling44.target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i)))) (toR (zx (toZPt (Tiling44.t3 Tiling44.target))))
        (toR (zy (toZPt (Tiling44.t3 Tiling44.target))))
      = toR (zcross (toZPt (Tiling44.t1 Tiling44.target)) (toZPt (vertexOf t i))
          (toZPt (Tiling44.t3 Tiling44.target))) from toR_zcross _ _ _,
      ← cross_eq_zcross,
      cross_cyclic (Tiling44.t1 Tiling44.target) (vertexOf t i) (Tiling44.t3 Tiling44.target),
      cross_cyclic (vertexOf t i) (Tiling44.t3 Tiling44.target) (Tiling44.t1 Tiling44.target)]
    exact Erdos634.Z15Real.toR_nonneg h3
  · -- h2 : 0 ≤ det3 x0 y0 x1 y1 a b = cross(T1, T2, v), direct match
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (Tiling44.t1 Tiling44.target))))
        (toR (zy (toZPt (Tiling44.t1 Tiling44.target)))) (toR (zx (toZPt (Tiling44.t2 Tiling44.target))))
        (toR (zy (toZPt (Tiling44.t2 Tiling44.target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i))))
      = toR (zcross (toZPt (Tiling44.t1 Tiling44.target)) (toZPt (Tiling44.t2 Tiling44.target))
          (toZPt (vertexOf t i))) from toR_zcross _ _ _,
      ← cross_eq_zcross]
    exact Erdos634.Z15Real.toR_nonneg h1

/-- **(C2) fully assembled**: every piece of `Tiling44`, as a real `Tri`, lies in the target. -/
theorem pieceTri_subset_target {t : Tiling44.Tri} (ht : t ∈ Tiling44.tiles) :
    (pieceTri ht).carrier ⊆ targetTri.carrier :=
  Erdos634.CertGeom.carrier_subset_of_pts_mem (fun k => by
    rw [pieceTri_pts t ht k]; exact vertexOf_mem_targetTri ht k)

/-! ## (C4): the area sum, and the assembled `CongruentDissection`

`Tiling44`'s own `checkAll` already checks `zsum (tiles.map area2) == area2 target`; this section
transfers that Bool equality to the real determinant sum `AreaDet.area_identity_of_det` needs. -/

/-- Every piece of `Tiling44`, indexed by `Fin Tiling44.tiles.length` (rather than a fixed literal
`44`, so no length-cast bookkeeping is needed anywhere in this section). -/
noncomputable def pieceAt (i : Fin Tiling44.tiles.length) : Tri :=
  pieceTri (t := Tiling44.tiles[i.val]) (List.getElem_mem i.isLt)

theorem detTri_pieceAt (i : Fin Tiling44.tiles.length) :
    Erdos634.AreaDet.detTri (pieceAt i) = toR (Tiling44.area2 (Tiling44.tiles[i.val])) := by
  unfold pieceAt pieceTri
  rw [Erdos634.CertCoord.detTri_mkTri, det3_eq_toR_cross]
  rfl

theorem foldl_zadd_eq (l : List Tiling44.Z15) (acc : Tiling44.Z15) :
    l.foldl Tiling44.zadd acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih]; apply Prod.ext <;> simp [Tiling44.zadd] <;> ring

theorem zsum_eq_sum (l : List Tiling44.Z15) : Tiling44.zsum l = l.sum := by
  simp only [Tiling44.zsum]; rw [foldl_zadd_eq]; simp

theorem tiling44_zadd_eq_zreal (u v : Tiling44.Z15) : Tiling44.zadd u v = zadd u v := rfl

theorem toR_list_sum (l : List Tiling44.Z15) : toR l.sum = (l.map toR).sum := by
  induction l with
  | nil => simp [toR]
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons]
    show toR (a + t.sum) = toR a + (List.map toR t).sum
    rw [show (a + t.sum : Tiling44.Z15) = Tiling44.zadd a t.sum from rfl,
      tiling44_zadd_eq_zreal, toR_add, ih]

theorem area_sum_transfer :
    ∑ i : Fin Tiling44.tiles.length, toR (Tiling44.area2 (Tiling44.tiles[i.val]))
      = toR (Tiling44.zsum (Tiling44.tiles.map Tiling44.area2)) := by
  rw [zsum_eq_sum, toR_list_sum, List.map_map,
    ← List.ofFn_getElem_eq_map Tiling44.tiles (toR ∘ Tiling44.area2)]
  rfl

/-- **The (C4) area sum, transferred to `ℝ`** — matching `Tiling44`'s own `checkAll` equality. -/
theorem area_sum_eq_target :
    ∑ i : Fin Tiling44.tiles.length, toR (Tiling44.area2 (Tiling44.tiles[i.val]))
      = toR (Tiling44.area2 Tiling44.target) := by
  rw [area_sum_transfer]
  apply congrArg toR
  have h := Tiling44.tiling44_certificate
  simp only [Tiling44.checkAll, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- **(C4) fully assembled**, with absolute values — every piece is positively oriented
(`all_pieces_pos`) and so is the target (`target_det_pos`), so `|det| = det` throughout. -/
theorem abs_detTri_sum_eq_target :
    ∑ i : Fin Tiling44.tiles.length, |Erdos634.AreaDet.detTri (pieceAt i)|
      = |Erdos634.AreaDet.detTri targetTri| := by
  have htarget : Erdos634.AreaDet.detTri targetTri = toR (Tiling44.area2 Tiling44.target) := by
    unfold targetTri
    rw [Erdos634.CertCoord.detTri_mkTri, det3_eq_toR_cross]
    rfl
  have htpos : (0:ℝ) < Erdos634.AreaDet.detTri targetTri := by
    unfold targetTri; rw [Erdos634.CertCoord.detTri_mkTri]; exact target_det_pos
  rw [htarget, abs_of_pos (htarget ▸ htpos)]
  rw [← area_sum_eq_target]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [detTri_pieceAt]
  exact abs_of_pos (toR_pos (all_pieces_pos _ (List.getElem_mem i.isLt)))

/-- **`Tiling44`'s certificate, assembled into a genuine `CongruentDissection`.** All four
certificate checks (C1)–(C4) are discharged: (C1) `pieceTri_congruent`, (C2)
`pieceTri_subset_target`, (C3) `pieces_interiors_disjoint`, (C4) `abs_detTri_sum_eq_target`. -/
theorem tiles_getElem_inj : ∀ i j : Fin Tiling44.tiles.length, i ≠ j →
    Tiling44.tiles[i.val] ≠ Tiling44.tiles[j.val] := by decide

noncomputable def dissection : CongruentDissection Tiling44.tiles.length where
  toDissection := Erdos634.AreaDet.ofDetCertificate targetTri pieceAt
    (fun i => pieceTri_subset_target (List.getElem_mem i.isLt))
    (fun i j hij => pieces_interiors_disjoint (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
      (tiles_getElem_inj i j hij))
    abs_detTri_sum_eq_target
  model := pieceTri headI_mem_tiles
  tiles_congruent := fun i => pieceTri_congruent (List.getElem_mem i.isLt)

end Erdos634.Tiling44Bridge
