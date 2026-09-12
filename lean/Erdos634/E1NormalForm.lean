import Erdos634.NormalPosition
import Erdos634.MarchCompose
import Erdos634.SssCongruent

/-!
# The `e = 1` family: from an arbitrary congruent dissection to the normal-position bundle

Written 2026-09-12, sequential step 6 after `MarchCompose.lean`.  `MarchCompose.base_word_dies`
is stated for a `CongruentDissection` in **normal position** (`htgt : D.target = baseBetaTarget
1 f`) with the model's vertices in `ModelData`'s order.  A dissection the problem actually hands
us has a target merely *congruent* to `baseBetaTarget 1 f` and a model merely *congruent* to the
tile `(f, f²−1, f²)`, with no vertex order at all.  This file removes both mismatches.

## What is proved

* `normalFormC D₀ g σ hT` — the dissection `D₀` moved into normal position by the isometry `g`
  of a congruence `(g, σ)` of its target with `U`, **with its model replaced by `T`** (any tile
  congruent to `D₀.model`).  Its tiles are `g`-images of `D₀`'s tiles, vertex for vertex
  (`normalFormC_tile_pts`, `rfl`); its target is `U` on the nose (`normalFormC_target`).
* `angleData_model` — the model angles `modelAlpha 1 n, modelBeta 1 n, 2α+β` satisfy `AngleData`
  for every natural `n ≥ 2`; `modelData_of_model_eq` — a dissection whose model *is* `modelTri n`
  has `ModelData`.
* `normal_form` — **the reduction**: for any `CongruentDissection` whose target is congruent to
  `baseBetaTarget 1 n` and whose model is congruent to `modelTri n`, there are an isometry `g` and
  a dissection `D` with `D.target = baseBetaTarget 1 n`, `D.model = modelTri n`, `ModelData D n α β
  γ`, `AngleData α β γ` (the model angles), and `(D.tile i).pts m = g ((D₀.tile i).pts m)`.
* `congruent_modelTri_of_sides`, `congruent_modelTri_of_sides_perm` — the model hypothesis from
  side lengths alone (SSS, `SssCongruent`), so "the tile is `(f, f²−1, f²)`" is enough.
* `laysARun_normalFormC_iff`, `laysWordBFirst_normalFormC_iff`, `laysWordCFirst_normalFormC_iff`
  — the base-word predicates on the normal form are, *definitionally*, the same predicates on
  `D₀`'s own tiles read through `g` (`Iff.rfl`).
* `base_point_iff` — the intrinsic reading: `g p = (x, 0)` iff `p` is the point at parameter
  `x / L` on the segment between `D₀`'s own two base vertices.
* `e1_family_of_word` — **`base_word_dies` transported**: for any `D₀` with the two congruences
  and `f = n ≥ 3`, if the base word `a^p b a^q c a^r` or `a^p c a^q b a^r` (`p, r ≥ 1`) is laid on
  `D₀`'s own base (through `g`), then `False`.  `htgt` and `ModelData`/`AngleData` no longer
  appear as hypotheses; they are *derived*.

## What is NOT proved

The base-word hypothesis of `e1_family_of_word` is still a hypothesis: that a congruent dissection
of the `e = 1` target lays its base as `f` letters `a`, one `b`, one `c`, first and last `a`, is
`thm:e1reduce`(ii) in positional form and is the subject of `E1BaseWord.lean`, not of this file.
Nothing here says such a dissection does not exist.

## Chirality

`normalize` may reverse orientation (`NormalPosition.lean`'s note).  Nothing downstream of this
file uses orientation: `LaysARun`/`LaysWord*` and every theorem of `MarchCompose` are stated
through vertex *sets* and `localAngle`s, both chirality-blind, which is why the transport is
plain `rfl`.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.E1NormalForm

open Erdos634.Geometry Erdos634.NormalPosition Erdos634.MarchCompose Erdos634.MarchKillsFan
  Erdos634.MarchSlots Erdos634.MarchInduction Erdos634.BaseBetaTargetCoord Erdos634.CertCoord
  Erdos634.DissectionMap Erdos634.Ladder Erdos634.TilePlacement

/-! ## 1. Normal position with the model replaced -/

/-- **A congruent dissection in normal position, with the model replaced by a congruent tile
`T`.**  Tiles are `g`-images of the originals; the target is `mapTri (isoAff g) (relabelTri D₀.target σ⁻¹)`. -/
noncomputable def normalFormC {N : ℕ} (D₀ : CongruentDissection N) (g : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) {T : Tri} (hT : D₀.model.Congruent T) : CongruentDissection N where
  toDissection := normalize D₀.toDissection g σ
  model := T
  tiles_congruent := fun i =>
    (congruent_mapTri g (D₀.tile i)).symm.trans ((D₀.tiles_congruent i).trans hT)

@[simp] theorem normalFormC_tile_pts {N : ℕ} (D₀ : CongruentDissection N) (g : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) {T : Tri} (hT : D₀.model.Congruent T) (i : Fin N) (m : Fin 3) :
    ((normalFormC D₀ g σ hT).tile i).pts m = g ((D₀.tile i).pts m) := rfl

@[simp] theorem normalFormC_model {N : ℕ} (D₀ : CongruentDissection N) (g : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) {T : Tri} (hT : D₀.model.Congruent T) :
    (normalFormC D₀ g σ hT).model = T := rfl

theorem normalFormC_target {N : ℕ} (D₀ : CongruentDissection N) {U : Tri} {g : Plane ≃ᵢ Plane}
    {σ : Equiv.Perm (Fin 3)} (hg : ∀ k, g (D₀.target.pts k) = U.pts (σ k)) {T : Tri}
    (hT : D₀.model.Congruent T) : (normalFormC D₀ g σ hT).target = U :=
  normalize_target D₀.toDissection hg

theorem normalFormC_tile_carrier {N : ℕ} (D₀ : CongruentDissection N) (g : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) {T : Tri} (hT : D₀.model.Congruent T) (i : Fin N) :
    ((normalFormC D₀ g σ hT).tile i).carrier = g '' (D₀.tile i).carrier :=
  normalize_tile_carrier D₀.toDissection g σ i

/-! ## 2. The model bundle for `modelTri n` -/

/-- The model angles satisfy `AngleData`, every natural `n ≥ 2`. -/
theorem angleData_model (n : ℕ) (hn : 2 ≤ n) :
    AngleData (modelAlpha 1 n) (modelBeta 1 n) (2 * modelAlpha 1 n + modelBeta 1 n) := by
  have hf : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hf1 : (1:ℝ) < n := by linarith
  exact ⟨modelAlpha_pos hf1, modelAlpha_lt_modelBeta hf, rfl, modelAngle_rel 1 n,
    modelAlpha_irrational n hn⟩

/-- A dissection whose model is `modelTri n` has `ModelData` at the model angles. -/
theorem modelData_of_model_eq {N : ℕ} (D : CongruentDissection N) (n : ℕ) (hn : 2 ≤ n)
    (hD : D.model = modelTri n (by exact_mod_cast (show 1 < n by omega))) :
    ModelData D n (modelAlpha 1 n) (modelBeta 1 n) (2 * modelAlpha 1 n + modelBeta 1 n) := by
  have hf : (2:ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hs0, hs1, hs2⟩ := modelTri_sides hf
  obtain ⟨hA, hB, hC⟩ := modelTri_angles hf
  exact ⟨by rw [hD]; exact hs0, by rw [hD]; exact hs1, by rw [hD]; exact hs2,
    by rw [hD]; exact hA, by rw [hD]; exact hB, by rw [hD]; exact hC⟩

/-! ## 3. SSS: the model hypothesis from side lengths -/

theorem fin3_two_add_one : ((2 : Fin 3) + 1) = 0 := by decide
theorem fin3_two_add_two : ((2 : Fin 3) + 2) = 1 := by decide
theorem fin3_one_add_one : ((1 : Fin 3) + 1) = 2 := by decide
theorem fin3_one_add_two : ((1 : Fin 3) + 2) = 0 := by decide

/-- **A tile with sides `n, n²−1, n²` in `ModelData`'s labelling is congruent to `modelTri n`.** -/
theorem congruent_modelTri_of_sides (n : ℕ) (hn : 2 ≤ n) (T : Tri)
    (h0 : sideOpp T 0 = n) (h1 : sideOpp T 1 = (n : ℝ) ^ 2 - 1) (h2 : sideOpp T 2 = (n : ℝ) ^ 2) :
    T.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega))) := by
  have hf : (2:ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨m0, m1, m2⟩ := modelTri_sides hf
  simp only [sideOpp] at h0 h1 h2 m0 m1 m2
  simp only [fin3_two_add_one, fin3_two_add_two, fin3_one_add_one, fin3_one_add_two,
    zero_add] at h0 h1 h2 m0 m1 m2
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [h2, m2]
  · rw [h0, m0]
  · rw [h1, m1]

/-- **SSS up to relabelling**: any vertex correspondence `τ` with matching distances. -/
theorem congruent_modelTri_of_sides_perm (n : ℕ) (hn : 2 ≤ n) (T : Tri) (τ : Equiv.Perm (Fin 3))
    (hd : ∀ i j, dist (T.pts i) (T.pts j)
      = dist ((modelTri n (by exact_mod_cast (show 1 < n by omega))).pts (τ i))
        ((modelTri n (by exact_mod_cast (show 1 < n by omega))).pts (τ j))) :
    T.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega))) :=
  Erdos634.SssCongruent.congruent_of_dist_perm τ hd

/-! ## 4. The reduction -/

/-- **THE NORMAL FORM.**  Any congruent dissection whose target is congruent to the `e = 1`
target and whose model is congruent to the tile `(n, n²−1, n²)` is carried, by one isometry `g`
of the plane, to a dissection with `D.target = baseBetaTarget 1 n` (on the nose), `D.model =
modelTri n`, `ModelData`, and `AngleData` at the model angles; every tile of `D` is the `g`-image
of the corresponding tile of `D₀`, vertex for vertex. -/
theorem normal_form {N : ℕ} (D₀ : CongruentDissection N) (n : ℕ) (hn : 2 ≤ n)
    (htgt : D₀.target.Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))))
    (hmod : D₀.model.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega)))) :
    ∃ (g : Plane ≃ᵢ Plane) (D : CongruentDissection N),
      D.target = baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega)) ∧
      D.model = modelTri n (by exact_mod_cast (show 1 < n by omega)) ∧
      ModelData D n (modelAlpha 1 n) (modelBeta 1 n) (2 * modelAlpha 1 n + modelBeta 1 n) ∧
      AngleData (modelAlpha 1 n) (modelBeta 1 n) (2 * modelAlpha 1 n + modelBeta 1 n) ∧
      ∀ i m, (D.tile i).pts m = g ((D₀.tile i).pts m) := by
  obtain ⟨g, σ, hg⟩ := htgt
  refine ⟨g, normalFormC D₀ g σ hmod, normalFormC_target D₀ hg hmod, rfl, ?_,
    angleData_model n hn, fun _ _ => rfl⟩
  exact modelData_of_model_eq _ n hn rfl

/-! ## 5. The base-word predicates transport definitionally -/

theorem laysARun_normalFormC_iff {N : ℕ} (D₀ : CongruentDissection N) (g : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) {T : Tri} (hT : D₀.model.Congruent T) (f t : ℝ) (m : ℕ) :
    LaysARun (normalFormC D₀ g σ hT) f t m ↔
      ∀ j, j < m → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        g ((D₀.tile i).pts k) = mkPt (t + j * f) 0 ∧
        g ((D₀.tile i).pts k') = mkPt (t + j * f + f) 0 :=
  Iff.rfl

theorem laysWordBFirst_normalFormC_iff {N : ℕ} (D₀ : CongruentDissection N) (g : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) {T : Tri} (hT : D₀.model.Congruent T) (f : ℝ) (p q r : ℕ) :
    LaysWordBFirst (normalFormC D₀ g σ hT) f p q r ↔
      (∀ j, j < p → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        g ((D₀.tile i).pts k) = mkPt (0 + j * f) 0 ∧
        g ((D₀.tile i).pts k') = mkPt (0 + j * f + f) 0) ∧
      (∃ (jb : Fin N) (kb mb : Fin 3), kb ≠ mb ∧ g ((D₀.tile jb).pts kb) = mkPt (p * f) 0 ∧
        g ((D₀.tile jb).pts mb) = mkPt (p * f + (f ^ 2 - 1)) 0) ∧
      (∀ j, j < q → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        g ((D₀.tile i).pts k) = mkPt (p * f + (f ^ 2 - 1) + j * f) 0 ∧
        g ((D₀.tile i).pts k') = mkPt (p * f + (f ^ 2 - 1) + j * f + f) 0) ∧
      (∃ (jc : Fin N) (kc mc : Fin 3), kc ≠ mc ∧
        g ((D₀.tile jc).pts kc) = mkPt (p * f + (f ^ 2 - 1) + q * f) 0 ∧
        g ((D₀.tile jc).pts mc) = mkPt (p * f + (f ^ 2 - 1) + q * f + f ^ 2) 0) ∧
      (∀ j, j < r → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        g ((D₀.tile i).pts k) = mkPt (p * f + (f ^ 2 - 1) + q * f + f ^ 2 + j * f) 0 ∧
        g ((D₀.tile i).pts k') = mkPt (p * f + (f ^ 2 - 1) + q * f + f ^ 2 + j * f + f) 0) :=
  Iff.rfl

theorem laysWordCFirst_normalFormC_iff {N : ℕ} (D₀ : CongruentDissection N) (g : Plane ≃ᵢ Plane)
    (σ : Equiv.Perm (Fin 3)) {T : Tri} (hT : D₀.model.Congruent T) (f : ℝ) (p q r : ℕ) :
    LaysWordCFirst (normalFormC D₀ g σ hT) f p q r ↔
      (∀ j, j < p → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        g ((D₀.tile i).pts k) = mkPt (0 + j * f) 0 ∧
        g ((D₀.tile i).pts k') = mkPt (0 + j * f + f) 0) ∧
      (∃ (jc : Fin N) (kc mc : Fin 3), kc ≠ mc ∧ g ((D₀.tile jc).pts kc) = mkPt (p * f) 0 ∧
        g ((D₀.tile jc).pts mc) = mkPt (p * f + f ^ 2) 0) ∧
      (∀ j, j < q → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        g ((D₀.tile i).pts k) = mkPt (p * f + f ^ 2 + j * f) 0 ∧
        g ((D₀.tile i).pts k') = mkPt (p * f + f ^ 2 + j * f + f) 0) ∧
      (∃ (jb : Fin N) (kb mb : Fin 3), kb ≠ mb ∧
        g ((D₀.tile jb).pts kb) = mkPt (p * f + f ^ 2 + q * f) 0 ∧
        g ((D₀.tile jb).pts mb) = mkPt (p * f + f ^ 2 + q * f + (f ^ 2 - 1)) 0) ∧
      (∀ j, j < r → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        g ((D₀.tile i).pts k) = mkPt (p * f + f ^ 2 + q * f + (f ^ 2 - 1) + j * f) 0 ∧
        g ((D₀.tile i).pts k') = mkPt (p * f + f ^ 2 + q * f + (f ^ 2 - 1) + j * f + f) 0) :=
  Iff.rfl

/-! ## 6. The intrinsic reading of "a point of `D₀`'s base" -/

/-- An isometry of the plane commutes with `lineMap`. -/
theorem iso_lineMap (g : Plane ≃ᵢ Plane) (A B : Plane) (s : ℝ) :
    g (AffineMap.lineMap A B s) = AffineMap.lineMap (g A) (g B) s := by
  exact (isoAff g).toAffineMap.apply_lineMap A B s

/-- **A point `p` of `D₀` is sent by `g` to the base point `(x, 0)` iff `p` is the point at
parameter `x / L` of the segment between `D₀`'s own two base vertices** `D₀.target.pts (σ⁻¹ 0)`
and `D₀.target.pts (σ⁻¹ 1)` (the vertices `g` sends to `(0,0)` and `(L,0)`).  So every
"laid on the base" hypothesis of `e1_family_of_word` is a statement about `D₀`'s own base. -/
theorem base_point_iff {N : ℕ} (D₀ : CongruentDissection N) {f : ℝ} (hf : 1 < f)
    (g : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3))
    (hg : ∀ k, g (D₀.target.pts k) = (baseBetaTarget 1 f one_pos hf).pts (σ k))
    (p : Plane) (x : ℝ) :
    g p = mkPt x 0 ↔
      p = AffineMap.lineMap (D₀.target.pts (σ.symm 0)) (D₀.target.pts (σ.symm 1))
        (x / baseLen 1 f) := by
  have hL := baseLen_pos one_pos hf
  have h0 : g (D₀.target.pts (σ.symm 0)) = mkPt 0 0 := by
    rw [hg, Equiv.apply_symm_apply]; rfl
  have h1 : g (D₀.target.pts (σ.symm 1)) = mkPt (baseLen 1 f) 0 := by
    rw [hg, Equiv.apply_symm_apply]; rfl
  have hline : g (AffineMap.lineMap (D₀.target.pts (σ.symm 0)) (D₀.target.pts (σ.symm 1))
      (x / baseLen 1 f)) = mkPt x 0 := by
    rw [iso_lineMap, h0, h1, Erdos634.RunPartition.CSlot.lineMap_mkPt]
    exact mkPt_congr (by field_simp; ring) (by ring)
  constructor
  · intro h
    exact g.injective (h.trans hline.symm)
  · intro h
    rw [h, hline]

/-! ## 7. The transported family theorem -/

/-- **`MarchCompose.base_word_dies`, for an arbitrary congruent dissection.**  `D₀` has a target
congruent to the `e = 1` target through `(g, σ)` and a model congruent to the tile `(n, n²−1,
n²)`; `f = n ≥ 3`; the base word `a^p b a^q c a^r` or `a^p c a^q b a^r` (`p, r ≥ 1`, `p+q+r = n`)
is laid on `D₀`'s own base, read through `g` (`laysWord*_normalFormC_iff`, `base_point_iff`).
Then `False`.  Normal position, `ModelData` and `AngleData` are derived, not assumed. -/
theorem e1_family_of_word {N : ℕ} (D₀ : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n)
    (g : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3))
    (hg : ∀ k, g (D₀.target.pts k)
      = (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))).pts (σ k))
    (hmod : D₀.model.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega))))
    {p q r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) (hpqr : p + q + r = n)
    (hw : LaysWordBFirst (normalFormC D₀ g σ hmod) n p q r ∨
          LaysWordCFirst (normalFormC D₀ g σ hmod) n p q r) : False := by
  have hf : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  exact base_word_dies (normalFormC D₀ g σ hmod) hf rfl hn3 (normalFormC_target D₀ hg hmod)
    (modelData_of_model_eq _ n (by omega) rfl) (angleData_model n (by omega)) hp hr hpqr hw

/-! ## 8. Non-vacuity of what this file adds

The congruence hypotheses are satisfiable (a triangle is congruent to itself), and the normal
form of a dissection already in normal position with model `modelTri n` is itself, tile for tile
(`normalFormC_id_tile`).  The whole bundle including the base word is *not* claimed satisfiable —
`e1_family_of_word` says exactly that it is not. -/

theorem target_self_congruent (n : ℕ) (hn : 2 ≤ n) :
    (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))).Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))) :=
  Tri.Congruent.refl _

theorem model_self_congruent (n : ℕ) (hn : 2 ≤ n) :
    (modelTri n (by exact_mod_cast (show 1 < n by omega))).Congruent
      (modelTri n (by exact_mod_cast (show 1 < n by omega))) :=
  Tri.Congruent.refl _

theorem normalFormC_id_tile {N : ℕ} (D₀ : CongruentDissection N) {T : Tri}
    (hT : D₀.model.Congruent T) (i : Fin N) (m : Fin 3) :
    ((normalFormC D₀ (IsometryEquiv.refl Plane) (Equiv.refl _) hT).tile i).pts m
      = (D₀.tile i).pts m := rfl

/-- At `n = 4` (`N = 47`, prime) the model bundle is inhabited. -/
theorem bundle_f4 : AngleData (modelAlpha 1 4) (modelBeta 1 4) (2 * modelAlpha 1 4 + modelBeta 1 4)
    ∧ (modelTri 4 (by norm_num)).Congruent (modelTri 4 (by norm_num)) := by
  have h := angleData_model 4 (by norm_num)
  rw [show ((4 : ℕ) : ℝ) = 4 by norm_num] at h
  exact ⟨h, Tri.Congruent.refl _⟩

end Erdos634.E1NormalForm

#print axioms Erdos634.E1NormalForm.normalFormC
#print axioms Erdos634.E1NormalForm.normal_form
#print axioms Erdos634.E1NormalForm.congruent_modelTri_of_sides
#print axioms Erdos634.E1NormalForm.base_point_iff
#print axioms Erdos634.E1NormalForm.e1_family_of_word
#print axioms Erdos634.E1NormalForm.bundle_f4
