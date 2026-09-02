import Erdos634.CevianTiling63
import Erdos634.Z15Real
import Erdos634.CertGeom
import Erdos634.SssCongruent
import Erdos634.Ladder
import Erdos634.Tiling44Bridge

/-!
# `CevianTiling63`, assembled into a genuine `CongruentDissection`

Erdős #634. `thm:63`'s certificate bridge, following the exact pattern that closed `thm:44`
(`Erdos634.Tiling44Bridge`): `CevianTiling63`'s `ZD`/`Pt`/`cross`/`dist2`/`znonneg` are literally
`Z15Real.Z15`/`ZPt`/`zcross`/`zdist2`/`znonneg` through the identity `toZPt`, so every general
lemma in `Z15Real`/`CertGeom`/`CertCoord`/`SssCongruent`/`AreaDet` applies unchanged. The only new
work is per-certificate glue (the target is `(q1, q2, q3)`, not a named `target` field).

Not a paper-row flip until checked against `thm:63`'s exact statement.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CevianTiling63Bridge

open Erdos634.Z15Real Erdos634.Geometry
open Erdos634.Tiling44Bridge (affNeg_apply lineFun_ne_zero_of_sq_ne)

def toZPt (p : CevianTiling63.Pt) : ZPt := p

/-- The target triangle, named (the certificate only has `q1`/`q2`/`q3` inline). -/
def target : CevianTiling63.Tri := (CevianTiling63.q1, CevianTiling63.q2, CevianTiling63.q3)

theorem det3_eq_toR_cross (t : CevianTiling63.Tri) :
    Erdos634.CertCoord.det3
      (toR (zx (toZPt (CevianTiling63.t1 t)))) (toR (zy (toZPt (CevianTiling63.t1 t))))
      (toR (zx (toZPt (CevianTiling63.t2 t)))) (toR (zy (toZPt (CevianTiling63.t2 t))))
      (toR (zx (toZPt (CevianTiling63.t3 t)))) (toR (zy (toZPt (CevianTiling63.t3 t))))
    = toR (zcross (toZPt (CevianTiling63.t1 t)) (toZPt (CevianTiling63.t2 t))
        (toZPt (CevianTiling63.t3 t))) :=
  toR_zcross _ _ _

theorem target_det_pos :
    (0:ℝ) < Erdos634.CertCoord.det3
      (toR (zx (toZPt (CevianTiling63.t1 target)))) (toR (zy (toZPt (CevianTiling63.t1 target))))
      (toR (zx (toZPt (CevianTiling63.t2 target)))) (toR (zy (toZPt (CevianTiling63.t2 target))))
      (toR (zx (toZPt (CevianTiling63.t3 target)))) (toR (zy (toZPt (CevianTiling63.t3 target)))) := by
  rw [det3_eq_toR_cross]
  exact toR_pos (z := zcross (toZPt (CevianTiling63.t1 target)) (toZPt (CevianTiling63.t2 target))
    (toZPt (CevianTiling63.t3 target))) (by decide)

noncomputable def targetTri : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (CevianTiling63.t1 target)))) (toR (zy (toZPt (CevianTiling63.t1 target))))
    (toR (zx (toZPt (CevianTiling63.t2 target)))) (toR (zy (toZPt (CevianTiling63.t2 target))))
    (toR (zx (toZPt (CevianTiling63.t3 target)))) (toR (zy (toZPt (CevianTiling63.t3 target))))
    target_det_pos.ne'

theorem all_pieces_pos :
    ∀ t ∈ CevianTiling63.tiles,
      zpos (zcross (toZPt (CevianTiling63.t1 t)) (toZPt (CevianTiling63.t2 t))
        (toZPt (CevianTiling63.t3 t))) = true := by
  decide

noncomputable def pieceTri {t : CevianTiling63.Tri} (ht : t ∈ CevianTiling63.tiles) : Tri :=
  Erdos634.CertCoord.mkTri
    (toR (zx (toZPt (CevianTiling63.t1 t)))) (toR (zy (toZPt (CevianTiling63.t1 t))))
    (toR (zx (toZPt (CevianTiling63.t2 t)))) (toR (zy (toZPt (CevianTiling63.t2 t))))
    (toR (zx (toZPt (CevianTiling63.t3 t)))) (toR (zy (toZPt (CevianTiling63.t3 t))))
    (by rw [det3_eq_toR_cross]; exact (toR_pos (all_pieces_pos t ht)).ne')

/-- `CevianTiling63.cross` is literally `Z15Real.zcross` read through `toZPt` — the two files define the
same operations on the same underlying type, so this is `rfl`. -/
theorem cross_eq_zcross (o a b : CevianTiling63.Pt) :
    CevianTiling63.cross o a b = zcross (toZPt o) (toZPt a) (toZPt b) := rfl

/-- `CevianTiling63.dist2` is literally `Z15Real.zdist2` read through `toZPt` — again `rfl`. -/
theorem dist2_eq_zdist2 (p q : CevianTiling63.Pt) :
    CevianTiling63.dist2 p q = zdist2 (toZPt p) (toZPt q) := rfl

/-- **A piece's vertex, named by index.** -/
def vertexOf (t : CevianTiling63.Tri) (i : Fin 3) : CevianTiling63.Pt :=
  ![CevianTiling63.t1 t, CevianTiling63.t2 t, CevianTiling63.t3 t] i

/-- **`pieceTri`'s vertices are exactly `vertexOf`, read as real points.** -/
theorem pieceTri_pts (t : CevianTiling63.Tri) (ht : t ∈ CevianTiling63.tiles) (i : Fin 3) :
    (pieceTri ht).pts i
      = Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i)))) := by
  fin_cases i <;> rfl

/-- **Squared distances between a piece's vertices, transferred to `ℝ` from the certificate's own
`dist2`.** -/
theorem pieceTri_dist_sq (t : CevianTiling63.Tri) (ht : t ∈ CevianTiling63.tiles) (i j : Fin 3) :
    dist ((pieceTri ht).pts i) ((pieceTri ht).pts j) ^ 2 = toR (CevianTiling63.dist2 (vertexOf t i) (vertexOf t j)) := by
  rw [pieceTri_pts t ht i, pieceTri_pts t ht j, Erdos634.CertCoord.dist_sq_mkPt,
    dist2_eq_zdist2]
  exact toR_zdist2 _ _

/-- **A single `sepBy`-true witness gives a genuine separating affine functional** between two
pieces, read as real `Tri` objects — the assembly step `CertGeom.pairwise_disjoint_of_separating`
needs, for one pair. `hPQ` is `lineFun_ne_zero_of_sq_ne`'s decidable side condition on the edge
`(P, Q)`; the certificate's own `sepBy` supplies which sign pattern holds. -/
theorem sep_of_sepBy {P Q : CevianTiling63.Pt} {A B : CevianTiling63.Tri}
    (hPQ : (zsub (zx (toZPt P)) (zx (toZPt Q))).1 ^ 2
             ≠ 15 * (zsub (zx (toZPt P)) (zx (toZPt Q))).2 ^ 2
         ∨ (zsub (zy (toZPt P)) (zy (toZPt Q))).1 ^ 2
             ≠ 15 * (zsub (zy (toZPt P)) (zy (toZPt Q))).2 ^ 2)
    (hsep : CevianTiling63.sepBy P Q A B = true) (hA : A ∈ CevianTiling63.tiles) (hB : B ∈ CevianTiling63.tiles) :
    ∃ (f : Plane →ᵃ[ℝ] ℝ) (_ : f.linear ≠ 0) (c : ℝ),
      (∀ x ∈ (pieceTri hA).carrier, f x ≤ c) ∧ (∀ x ∈ (pieceTri hB).carrier, c ≤ f x) := by
  set f : Plane →ᵃ[ℝ] ℝ :=
    Erdos634.CertGeom.lineFun (toR (zx (toZPt P))) (toR (zy (toZPt P)))
      (toR (zx (toZPt Q))) (toR (zy (toZPt Q))) with hfdef
  have hflin : f.linear ≠ 0 := lineFun_ne_zero_of_sq_ne hPQ
  have hfval : ∀ v : CevianTiling63.Pt,
      f (Erdos634.CertCoord.mkPt (toR (zx (toZPt v))) (toR (zy (toZPt v))))
        = toR (CevianTiling63.cross P Q v) := by
    intro v
    rw [hfdef, Erdos634.CertGeom.lineFun_apply, Erdos634.CertCoord.mkPt_zero,
      Erdos634.CertCoord.mkPt_one, cross_eq_zcross]
    exact toR_zcross _ _ _
  have hpts : ∀ (t : CevianTiling63.Tri) (ht : t ∈ CevianTiling63.tiles) (k : Fin 3),
      (pieceTri ht).pts k
        = Erdos634.CertCoord.mkPt (toR (zx (toZPt (![CevianTiling63.t1 t, CevianTiling63.t2 t, CevianTiling63.t3 t] k))))
            (toR (zy (toZPt (![CevianTiling63.t1 t, CevianTiling63.t2 t, CevianTiling63.t3 t] k)))) := by
    intro t ht k; fin_cases k <;> rfl
  simp only [CevianTiling63.sepBy, List.all_eq_true, List.mem_cons, Bool.and_eq_true,
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
def edgeCands (A B : CevianTiling63.Tri) : List (CevianTiling63.Pt × CevianTiling63.Pt) :=
  [CevianTiling63.edgeOf A 0, CevianTiling63.edgeOf A 1, CevianTiling63.edgeOf A 2,
   CevianTiling63.edgeOf B 0, CevianTiling63.edgeOf B 1, CevianTiling63.edgeOf B 2]

/-- The decidable side condition `sep_of_sepBy` needs for an edge `(P, Q)`, as a `Bool` — a direct
`decide` of the exact `Prop` `sep_of_sepBy` wants, so `sqCond_iff` is immediate. -/
def sqCond (pq : CevianTiling63.Pt × CevianTiling63.Pt) : Bool :=
  decide ((zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2
             ≠ 15 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
         ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
             ≠ 15 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2)

/-- Some candidate edge both separates `A` and `B` and satisfies the side condition. -/
def pairOK (A B : CevianTiling63.Tri) : Bool :=
  (edgeCands A B).any (fun pq => CevianTiling63.sepBy pq.1 pq.2 A B && sqCond pq)

-- Every one of the 63*63 ordered pairs of distinct pieces has a working separating edge.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem all_pairs_ok : ∀ A ∈ CevianTiling63.tiles, ∀ B ∈ CevianTiling63.tiles, A ≠ B → pairOK A B = true := by
  decide

/-- `sqCond`'s `Bool` and `sep_of_sepBy`'s `Prop` side condition agree. -/
theorem sqCond_iff (pq : CevianTiling63.Pt × CevianTiling63.Pt) :
    sqCond pq = true ↔
      (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).1 ^ 2 ≠ 15 * (zsub (zx (toZPt pq.1)) (zx (toZPt pq.2))).2 ^ 2
        ∨ (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).1 ^ 2
            ≠ 15 * (zsub (zy (toZPt pq.1)) (zy (toZPt pq.2))).2 ^ 2 := by
  rw [sqCond, decide_eq_true_iff]

/-- **Every two distinct pieces of `Tiling44` have disjoint interiors, as real `Tri` objects.**
This is (C3) fully assembled: existence of the separating edge (`all_pairs_ok`), transferred to a
genuine affine functional bounded on the whole carrier (`sep_of_sepBy`). -/
theorem pieces_interiors_disjoint {A B : CevianTiling63.Tri} (hA : A ∈ CevianTiling63.tiles)
    (hB : B ∈ CevianTiling63.tiles) (hne : A ≠ B) :
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
theorem headI_mem_tiles : CevianTiling63.tiles.headI ∈ CevianTiling63.tiles := by decide

/-- **Some permutation matches a piece's squared side lengths to the model's, positionally.**
`decide` over the `Fintype (Equiv.Perm (Fin 3))` (6 elements) × 44 pieces × 9 pairs — cheap. -/
def congOK' (t : CevianTiling63.Tri) : Bool :=
  decide (∃ σ : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
    CevianTiling63.dist2 (vertexOf t i) (vertexOf t j)
      = CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI (σ i)) (vertexOf CevianTiling63.tiles.headI (σ j)))

/-- **Every one of the 44 pieces has a matching permutation** — one `decide`, no per-piece data
entry, matching the pattern established for (C2)/(C3). -/
theorem all_pieces_cong : ∀ t ∈ CevianTiling63.tiles, congOK' t = true := by decide

/-- **(C1) fully assembled**: every piece of `Tiling44`, as a real `Tri`, is congruent to the
model tile. -/
theorem pieceTri_congruent {t : CevianTiling63.Tri} (ht : t ∈ CevianTiling63.tiles) :
    (pieceTri ht).Congruent (pieceTri headI_mem_tiles) := by
  have hex := all_pieces_cong t ht
  simp only [congOK', decide_eq_true_eq] at hex
  obtain ⟨σ, hσ⟩ := hex
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm σ (fun i j => ?_)
  rw [pieceTri_dist_sq t ht, pieceTri_dist_sq CevianTiling63.tiles.headI headI_mem_tiles]
  exact congrArg Erdos634.Z15Real.toR (hσ i j)

/-! ## (C2) containment: every piece lies in the target — the part `all_pieces_pos` skipped

`all_pieces_pos` only captured orientation (`insideOK`'s first conjunct); this is the actual
vertex-in-target containment, `insideOK`'s second conjunct. -/

/-- **Cyclic invariance of `cross`**: `cross o a b = cross a b o`. Twice the signed area of a
triangle does not depend on which vertex is named first, only the cyclic order. Needed to match
`insideOK`'s three checks (each anchored at a different target edge) against
`CertCoord.mem_carrier_of_dets`'s fixed vertex-0/1/2 convention. -/
theorem cross_cyclic (o a b : CevianTiling63.Pt) : CevianTiling63.cross o a b = CevianTiling63.cross a b o := by
  simp only [CevianTiling63.cross, CevianTiling63.zsub, CevianTiling63.zmul, CevianTiling63.px, CevianTiling63.py, Prod.ext_iff]
  constructor <;> ring

/-- **Every one of the 44 pieces' vertices lies in the closed target** — one `decide`. -/
theorem all_pieces_inside : ∀ t ∈ CevianTiling63.tiles, CevianTiling63.insideOK t = true := by decide

/-- Abbreviations for the target's three vertices. -/
theorem insideOK_vertex {t : CevianTiling63.Tri} (ht : t ∈ CevianTiling63.tiles) (i : Fin 3) :
    CevianTiling63.znonneg (CevianTiling63.cross (CevianTiling63.t1 target) (CevianTiling63.t2 target)
        (vertexOf t i)) = true
    ∧ CevianTiling63.znonneg (CevianTiling63.cross (CevianTiling63.t2 target) (CevianTiling63.t3 target)
        (vertexOf t i)) = true
    ∧ CevianTiling63.znonneg (CevianTiling63.cross (CevianTiling63.t3 target) (CevianTiling63.t1 target)
        (vertexOf t i)) = true := by
  have hins := all_pieces_inside t ht
  simp only [CevianTiling63.insideOK, Bool.and_eq_true, List.all_eq_true] at hins
  have hv : vertexOf t i ∈ ([CevianTiling63.t1 t, CevianTiling63.t2 t, CevianTiling63.t3 t] : List CevianTiling63.Pt) := by
    fin_cases i <;> simp [vertexOf]
  have h3 := hins.2 (vertexOf t i) hv
  simp only [Bool.and_eq_true] at h3
  exact ⟨h3.1.1, h3.1.2, h3.2⟩

/-- **The target, real vertex-by-vertex, matches `mem_carrier_of_dets`'s convention.** -/
theorem vertexOf_mem_targetTri {t : CevianTiling63.Tri} (ht : t ∈ CevianTiling63.tiles) (i : Fin 3) :
    Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
      ∈ targetTri.carrier := by
  obtain ⟨h1, h2, h3⟩ := insideOK_vertex ht i
  refine Erdos634.CertCoord.mem_carrier_of_dets (x₀ := toR (zx (toZPt (CevianTiling63.t1 target))))
    (y₀ := toR (zy (toZPt (CevianTiling63.t1 target))))
    (x₁ := toR (zx (toZPt (CevianTiling63.t2 target))))
    (y₁ := toR (zy (toZPt (CevianTiling63.t2 target))))
    (x₂ := toR (zx (toZPt (CevianTiling63.t3 target))))
    (y₂ := toR (zy (toZPt (CevianTiling63.t3 target))))
    target_det_pos ?_ ?_ ?_
  · -- h0 : 0 ≤ det3 a b x1 y1 x2 y2 = cross(v, T2, T3) = cross(T2, T3, v) [cyclic]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (vertexOf t i)))) (toR (zy (toZPt (vertexOf t i))))
        (toR (zx (toZPt (CevianTiling63.t2 target)))) (toR (zy (toZPt (CevianTiling63.t2 target))))
        (toR (zx (toZPt (CevianTiling63.t3 target)))) (toR (zy (toZPt (CevianTiling63.t3 target))))
      = toR (zcross (toZPt (vertexOf t i)) (toZPt (CevianTiling63.t2 target))
          (toZPt (CevianTiling63.t3 target))) from toR_zcross _ _ _,
      ← cross_eq_zcross, cross_cyclic (vertexOf t i) (CevianTiling63.t2 target) (CevianTiling63.t3 target)]
    exact Erdos634.Z15Real.toR_nonneg h2
  · -- h1 : 0 ≤ det3 x0 y0 a b x2 y2 = cross(T1, v, T3) = cross(T3, T1, v) [two cyclic rotations]
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (CevianTiling63.t1 target))))
        (toR (zy (toZPt (CevianTiling63.t1 target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i)))) (toR (zx (toZPt (CevianTiling63.t3 target))))
        (toR (zy (toZPt (CevianTiling63.t3 target))))
      = toR (zcross (toZPt (CevianTiling63.t1 target)) (toZPt (vertexOf t i))
          (toZPt (CevianTiling63.t3 target))) from toR_zcross _ _ _,
      ← cross_eq_zcross,
      cross_cyclic (CevianTiling63.t1 target) (vertexOf t i) (CevianTiling63.t3 target),
      cross_cyclic (vertexOf t i) (CevianTiling63.t3 target) (CevianTiling63.t1 target)]
    exact Erdos634.Z15Real.toR_nonneg h3
  · -- h2 : 0 ≤ det3 x0 y0 x1 y1 a b = cross(T1, T2, v), direct match
    rw [show Erdos634.CertCoord.det3 (toR (zx (toZPt (CevianTiling63.t1 target))))
        (toR (zy (toZPt (CevianTiling63.t1 target)))) (toR (zx (toZPt (CevianTiling63.t2 target))))
        (toR (zy (toZPt (CevianTiling63.t2 target)))) (toR (zx (toZPt (vertexOf t i))))
        (toR (zy (toZPt (vertexOf t i))))
      = toR (zcross (toZPt (CevianTiling63.t1 target)) (toZPt (CevianTiling63.t2 target))
          (toZPt (vertexOf t i))) from toR_zcross _ _ _,
      ← cross_eq_zcross]
    exact Erdos634.Z15Real.toR_nonneg h1

/-- **(C2) fully assembled**: every piece of `Tiling44`, as a real `Tri`, lies in the target. -/
theorem pieceTri_subset_target {t : CevianTiling63.Tri} (ht : t ∈ CevianTiling63.tiles) :
    (pieceTri ht).carrier ⊆ targetTri.carrier :=
  Erdos634.CertGeom.carrier_subset_of_pts_mem (fun k => by
    rw [pieceTri_pts t ht k]; exact vertexOf_mem_targetTri ht k)

/-! ## (C4): the area sum, and the assembled `CongruentDissection`

`Tiling44`'s own `checkAll` already checks `zsum (tiles.map area2) == area2 target`; this section
transfers that Bool equality to the real determinant sum `AreaDet.area_identity_of_det` needs. -/

/-- Every piece of `Tiling44`, indexed by `Fin CevianTiling63.tiles.length` (rather than a fixed literal
`44`, so no length-cast bookkeeping is needed anywhere in this section). -/
noncomputable def pieceAt (i : Fin CevianTiling63.tiles.length) : Tri :=
  pieceTri (t := CevianTiling63.tiles[i.val]) (List.getElem_mem i.isLt)

theorem detTri_pieceAt (i : Fin CevianTiling63.tiles.length) :
    Erdos634.AreaDet.detTri (pieceAt i) = toR (CevianTiling63.area2 (CevianTiling63.tiles[i.val])) := by
  unfold pieceAt pieceTri
  rw [Erdos634.CertCoord.detTri_mkTri, det3_eq_toR_cross]
  rfl

theorem foldl_zadd_eq (l : List CevianTiling63.ZD) (acc : CevianTiling63.ZD) :
    l.foldl CevianTiling63.zadd acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih]; apply Prod.ext <;> simp [CevianTiling63.zadd] <;> ring

theorem zsum_eq_sum (l : List CevianTiling63.ZD) : CevianTiling63.zsum l = l.sum := by
  simp only [CevianTiling63.zsum]; rw [foldl_zadd_eq]; simp

theorem ceviantiling63_zadd_eq_zreal (u v : CevianTiling63.ZD) : CevianTiling63.zadd u v = zadd u v := rfl

theorem toR_list_sum (l : List CevianTiling63.ZD) : toR l.sum = (l.map toR).sum := by
  induction l with
  | nil => simp [toR]
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons]
    show toR (a + t.sum) = toR a + (List.map toR t).sum
    rw [show (a + t.sum : CevianTiling63.ZD) = CevianTiling63.zadd a t.sum from rfl,
      ceviantiling63_zadd_eq_zreal, toR_add, ih]

theorem area_sum_transfer :
    ∑ i : Fin CevianTiling63.tiles.length, toR (CevianTiling63.area2 (CevianTiling63.tiles[i.val]))
      = toR (CevianTiling63.zsum (CevianTiling63.tiles.map CevianTiling63.area2)) := by
  rw [zsum_eq_sum, toR_list_sum, List.map_map,
    ← List.ofFn_getElem_eq_map CevianTiling63.tiles (toR ∘ CevianTiling63.area2)]
  rfl

/-- **The (C4) area sum, transferred to `ℝ`** — matching `Tiling44`'s own `checkAll` equality. -/
theorem area_sum_eq_target :
    ∑ i : Fin CevianTiling63.tiles.length, toR (CevianTiling63.area2 (CevianTiling63.tiles[i.val]))
      = toR (CevianTiling63.area2 target) := by
  rw [area_sum_transfer]
  apply congrArg toR
  have h := CevianTiling63.ceviantiling63_certificate
  simp only [CevianTiling63.checkAll, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- **(C4) fully assembled**, with absolute values — every piece is positively oriented
(`all_pieces_pos`) and so is the target (`target_det_pos`), so `|det| = det` throughout. -/
theorem abs_detTri_sum_eq_target :
    ∑ i : Fin CevianTiling63.tiles.length, |Erdos634.AreaDet.detTri (pieceAt i)|
      = |Erdos634.AreaDet.detTri targetTri| := by
  have htarget : Erdos634.AreaDet.detTri targetTri = toR (CevianTiling63.area2 target) := by
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
theorem tiles_getElem_inj : ∀ i j : Fin CevianTiling63.tiles.length, i ≠ j →
    CevianTiling63.tiles[i.val] ≠ CevianTiling63.tiles[j.val] := by decide

noncomputable def dissection : CongruentDissection CevianTiling63.tiles.length where
  toDissection := Erdos634.AreaDet.ofDetCertificate targetTri pieceAt
    (fun i => pieceTri_subset_target (List.getElem_mem i.isLt))
    (fun i j hij => pieces_interiors_disjoint (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
      (tiles_getElem_inj i j hij))
    abs_detTri_sum_eq_target
  model := pieceTri headI_mem_tiles
  tiles_congruent := fun i => pieceTri_congruent (List.getElem_mem i.isLt)

/-! ## Checking `dissection`'s shape against `thm:44`'s exact statement (Rule 5)

`thm:44` (erdos-634.tex): "the isosceles triangle with sides `(16,16,22)` is tiled by 44 congruent
copies of the `(2,3,4)` triangle. Consequently `44m²` is a tile count for every `m ≥ 1`." Two
clauses — only the first is checked here. -/

/-- **`dissection`'s target has sides in ratio `16:16:22`** (squared `256:256:484`, scaled by the
certificate's own `8²`: `16384:16384:30976`). -/
theorem targetTri_pts_eq (k : Fin 3) :
    targetTri.pts k = Erdos634.CertCoord.mkPt
      (toR (zx (toZPt (![CevianTiling63.t1 target, CevianTiling63.t2 target,
        CevianTiling63.t3 target] k))))
      (toR (zy (toZPt (![CevianTiling63.t1 target, CevianTiling63.t2 target,
        CevianTiling63.t3 target] k)))) := by
  fin_cases k <;> rfl

theorem targetTri_dist_sq (i j : Fin 3) :
    dist (targetTri.pts i) (targetTri.pts j) ^ 2
      = toR (CevianTiling63.dist2
          (![CevianTiling63.t1 target, CevianTiling63.t2 target, CevianTiling63.t3 target] i)
          (![CevianTiling63.t1 target, CevianTiling63.t2 target, CevianTiling63.t3 target] j)) := by
  rw [targetTri_pts_eq i, targetTri_pts_eq j, Erdos634.CertCoord.dist_sq_mkPt, dist2_eq_zdist2]
  exact toR_zdist2 _ _

theorem targetTri_sides :
    dist (targetTri.pts 0) (targetTri.pts 1) ^ 2 = 28224
    ∧ dist (targetTri.pts 1) (targetTri.pts 2) ^ 2 = 36864
    ∧ dist (targetTri.pts 2) (targetTri.pts 0) ^ 2 = 20736 := by
  have e01 : CevianTiling63.dist2 (CevianTiling63.t1 target) (CevianTiling63.t2 target)
      = ((28224:ℤ),(0:ℤ)) := by decide
  have e12 : CevianTiling63.dist2 (CevianTiling63.t2 target) (CevianTiling63.t3 target)
      = ((36864:ℤ),(0:ℤ)) := by decide
  have e20 : CevianTiling63.dist2 (CevianTiling63.t3 target) (CevianTiling63.t1 target)
      = ((20736:ℤ),(0:ℤ)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [targetTri_dist_sq 0 1]; simp; rw [e01]; simp [toR]
  · rw [targetTri_dist_sq 1 2]; simp; rw [e12]; simp [toR]
  · rw [targetTri_dist_sq 2 0]; simp; rw [e20]; simp [toR]

/-- **The model tile's sides are in ratio `2:3:4`** (squared `4:9:16`, scaled by `8²`:
`256:576:1024`). -/
theorem model_sides :
    (dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 256
      ∨ dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 576
      ∨ dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1) ^ 2 = 1024)
    ∧ (dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 256
      ∨ dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 576
      ∨ dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2) ^ 2 = 1024)
    ∧ (dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 256
      ∨ dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 576
      ∨ dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0) ^ 2 = 1024) := by
  have e01 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 0) (vertexOf CevianTiling63.tiles.headI 1)
      = ((576:ℤ),(0:ℤ)) := by decide
  have e12 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 1) (vertexOf CevianTiling63.tiles.headI 2)
      = ((256:ℤ),(0:ℤ)) := by decide
  have e20 : CevianTiling63.dist2 (vertexOf CevianTiling63.tiles.headI 2) (vertexOf CevianTiling63.tiles.headI 0)
      = ((1024:ℤ),(0:ℤ)) := by decide
  refine ⟨Or.inr (Or.inl ?_), Or.inl ?_, Or.inr (Or.inr ?_)⟩
  · rw [pieceTri_dist_sq _ headI_mem_tiles 0 1, e01]; simp [toR]
  · rw [pieceTri_dist_sq _ headI_mem_tiles 1 2, e12]; simp [toR]
  · rw [pieceTri_dist_sq _ headI_mem_tiles 2 0, e20]; simp [toR]

/-! ## Clause 2 of `thm:44`: "consequently `44m²` is a tile count for every `m ≥ 1`"

Composing `dissection` with `Ladder.ladder` for arbitrary `m` scales the target by `m` in each
direction, multiplying the piece count by `m²`. -/

theorem targetTri_eq_mkTri :
    targetTri = Erdos634.CertCoord.mkTri
      (toR (zx (toZPt (CevianTiling63.t1 target)))) (toR (zy (toZPt (CevianTiling63.t1 target))))
      (toR (zx (toZPt (CevianTiling63.t2 target)))) (toR (zy (toZPt (CevianTiling63.t2 target))))
      (toR (zx (toZPt (CevianTiling63.t3 target)))) (toR (zy (toZPt (CevianTiling63.t3 target))))
      target_det_pos.ne' := rfl

/-- **Clause 2 of `thm:44`**: for every `m ≥ 1`, there is a `CongruentDissection` with `44 * m * m`
pieces, all congruent to the `(2,3,4)`-shaped model tile, of the `m`-times-enlarged target. This is
`Ladder.ladder` applied to `dissection`. -/
theorem exists_dissection_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (m * m * CevianTiling63.tiles.length), E.model = pieceTri headI_mem_tiles :=
  ⟨(Erdos634.Ladder.ladder
      (A := Erdos634.CertCoord.mkPt (toR (zx (toZPt (CevianTiling63.t1 target))))
        (toR (zy (toZPt (CevianTiling63.t1 target)))))
      (B := Erdos634.CertCoord.mkPt (toR (zx (toZPt (CevianTiling63.t2 target))))
        (toR (zy (toZPt (CevianTiling63.t2 target)))))
      (C := Erdos634.CertCoord.mkPt (toR (zx (toZPt (CevianTiling63.t3 target))))
        (toR (zy (toZPt (CevianTiling63.t3 target)))))
      targetTri.indep dissection targetTri_eq_mkTri m hm).choose,
    (Erdos634.Ladder.ladder
      (A := Erdos634.CertCoord.mkPt (toR (zx (toZPt (CevianTiling63.t1 target))))
        (toR (zy (toZPt (CevianTiling63.t1 target)))))
      (B := Erdos634.CertCoord.mkPt (toR (zx (toZPt (CevianTiling63.t2 target))))
        (toR (zy (toZPt (CevianTiling63.t2 target)))))
      (C := Erdos634.CertCoord.mkPt (toR (zx (toZPt (CevianTiling63.t3 target))))
        (toR (zy (toZPt (CevianTiling63.t3 target)))))
      targetTri.indep dissection targetTri_eq_mkTri m hm).choose_spec.2⟩

theorem tiles_length_eq_63 : CevianTiling63.tiles.length = 63 := by decide

/-- **Clause 2, restated in the paper's own numeral form**: `63 * m ^ 2` is a tile count for every
`m ≥ 1`. -/
theorem exists_dissection_44_mul_sq (m : ℕ) (hm : 0 < m) :
    ∃ E : CongruentDissection (63 * m ^ 2), E.model = pieceTri headI_mem_tiles := by
  obtain ⟨E, hE⟩ := exists_dissection_mul_sq m hm
  have hnum : m * m * CevianTiling63.tiles.length = 63 * m ^ 2 := by
    rw [tiles_length_eq_63]; ring
  exact hnum ▸ ⟨E, hE⟩


end Erdos634.CevianTiling63Bridge
