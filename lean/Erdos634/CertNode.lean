import Erdos634.SixPlacements
import Erdos634.ThickBlockingLemmas

/-!
# The certified-search format: per-node soundness lemmas over `ℚ(√Dn)`

Erdős #634, blocker (iv) of `PAPER_MAP.md`.  A refutation tree (`build23.py`-style) is a finite
tree of *nodes*; each node is a set of placed tiles `S`, a lexicographically least point `v`, a
unit ray `d`, and for each of the six oriented placements at `(v, d)` a *kill* — `escape`
(a vertex outside the target), `overlap` (an explicit common interior point with a placed tile),
`baseword` (a base edge that clashes with the hypothesised base word), or `child` (the placement
is admissible and the child node kills it).  `gen_tree.py` turns such a tree into a Lean file in
which every node is a theorem about an arbitrary `CongruentDissection`; every generated proof
step is an application of a lemma in **this** file, and this file is the whole trust base of the
format beyond `PlacementCompleteness` / `SixPlacements`.

## Coordinates

Every point of every node lives in `ℚ × ℚ·√Dn` (`Dn = 32` at `(e,f) = (2,3)`, `Dn = 15` for the
`(2,3,4)` tiling): `rp Dn x y = (x, y·√Dn)`.  Edge functionals of such triangles, evaluated at
`rp Dn X Y`, are `√Dn` times a **rational-linear** form `ef` in `(X, Y)` — so every membership,
escape, overlap and covering fact is a linear-arithmetic fact with rational coefficients, exactly
what `linarith` decides.  Nothing about `√Dn` beyond `√Dn > 0`, `√Dn² = Dn` and crude bounds is
ever used.

## What each lemma certifies

* `mem_rtri` / `rtri_ef_nonneg` / `mem_interior_rtri` / `not_mem_rtri_of_edge*` — closed and
  open membership in a coordinate triangle as three rational-linear inequalities;
* `placeThird_rp` — the third vertex of `SixPlacements.placeThird` in `ℚ(√Dn)` coordinates;
* `hlex_of` + `lexLE_rp` + `halfR` — a closed superset `C` of the unfilled region discharges
  `hlex`; the generator supplies `C` as target ∩ half-planes and proves `U ⊆ C` by a
  binary-space-partition of linear inequalities;
* `hfree_of` + `pt_ccw_rp` — the counter-clockwise side of `d` is free, from an explicit
  polynomial-in-`t` point;
* `hblocked_of_wedge` / `hblocked_base` — the clockwise wedge lies in a placed tile
  (`PlacementCompleteness.wedge_interior`) or below the base;
* `escape_of`, `overlap_of`, `base_edge_clash` — the three kills;
* `carrier_eq_rtri_of_pts`, `mem_unfilled_iff`, `model_sides_rp` — plumbing.

`base_edge_clash` is the base-word kill: two tiles of a dissection with base edges starting at
the same base point `(x₀,0)` and running right to different endpoints have overlapping
interiors (the wedge above the shared start lies in both), so a hypothesised base block
`[x₀, x₁]` excludes any placement with base edge `[x₀, x₁']`, `x₁' ≠ x₁`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CertNode

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.PlacementCompleteness
  Erdos634.SixPlacements

/-! ## 1. The surd and the coordinate points -/

/-- `√Dn`. -/
noncomputable def sr (Dn : ℝ) : ℝ := Real.sqrt Dn

theorem sr_pos {Dn : ℝ} (hD : 0 < Dn) : 0 < sr Dn := Real.sqrt_pos.mpr hD

theorem sr_sq {Dn : ℝ} (hD : 0 < Dn) : sr Dn ^ 2 = Dn := Real.sq_sqrt hD.le

theorem sr_lt {Dn B : ℝ} (hD : 0 < Dn) (hB : 0 < B) (h : Dn < B ^ 2) : sr Dn < B := by
  nlinarith [sr_sq hD, sr_pos hD]

theorem sr_gt {Dn B : ℝ} (hD : 0 < Dn) (hB : 0 ≤ B) (h : B ^ 2 < Dn) : B < sr Dn := by
  nlinarith [sr_sq hD, sr_pos hD]

/-- The point `(x, y·√Dn)`. -/
noncomputable def rp (Dn x y : ℝ) : Plane := mkPt x (y * sr Dn)

@[simp] theorem rp_zero (Dn x y : ℝ) : rp Dn x y 0 = x := by simp [rp]
@[simp] theorem rp_one (Dn x y : ℝ) : rp Dn x y 1 = y * sr Dn := by simp [rp]

theorem rp_eq_mkPt_zero (Dn x : ℝ) : rp Dn x 0 = mkPt x 0 := by simp [rp]

theorem exists_rp {Dn : ℝ} (hD : 0 < Dn) (p : Plane) : ∃ X Y : ℝ, p = rp Dn X Y := by
  refine ⟨p 0, p 1 / sr Dn, plane_ext ?_ ?_⟩
  · simp
  · simp only [rp_one]; field_simp [(sr_pos hD).ne']

theorem rp_add_smul (Dn xv yv c a b : ℝ) :
    rp Dn xv yv + c • rp Dn a b = rp Dn (xv + c * a) (yv + c * b) := by
  refine plane_ext ?_ ?_ <;> simp <;> ring

theorem rp_unit {Dn a b : ℝ} (hD : 0 < Dn) (h : a ^ 2 + Dn * b ^ 2 = 1) :
    (rp Dn a b) 0 ^ 2 + (rp Dn a b) 1 ^ 2 = 1 := by
  simp only [rp_zero, rp_one]
  linear_combination (b ^ 2) * sr_sq hD + h

theorem dist_rp_sq (Dn : ℝ) (hD : 0 < Dn) (x₁ y₁ x₂ y₂ : ℝ) :
    dist (rp Dn x₁ y₁) (rp Dn x₂ y₂) ^ 2 = (x₁ - x₂) ^ 2 + Dn * (y₁ - y₂) ^ 2 := by
  rw [rp, rp, dist_sq_mkPt]
  linear_combination ((y₁ - y₂) ^ 2) * sr_sq hD

theorem dist_rp {Dn : ℝ} (hD : 0 < Dn) {x₁ y₁ x₂ y₂ c : ℝ} (hc : 0 ≤ c)
    (h : (x₁ - x₂) ^ 2 + Dn * (y₁ - y₂) ^ 2 = c ^ 2) :
    dist (rp Dn x₁ y₁) (rp Dn x₂ y₂) = c := by
  have := dist_rp_sq Dn hD x₁ y₁ x₂ y₂
  rw [h] at this
  nlinarith [dist_nonneg (x := rp Dn x₁ y₁) (y := rp Dn x₂ y₂)]

/-! ## 2. Coordinate triangles and the rational edge functional -/

/-- The rational-linear edge functional: positive to the left of the directed edge
`(x₀,y₀) → (x₁,y₁)` (in the rescaled coordinates `(X, Y)`). -/
def ef (x₀ y₀ x₁ y₁ X Y : ℝ) : ℝ := (x₁ - x₀) * (Y - y₀) - (X - x₀) * (y₁ - y₀)

theorem det3_rp (Dn x₀ y₀ x₁ y₁ X Y : ℝ) :
    det3 x₀ (y₀ * sr Dn) x₁ (y₁ * sr Dn) X (Y * sr Dn) = sr Dn * ef x₀ y₀ x₁ y₁ X Y := by
  unfold det3 ef; ring

theorem ef_cyc (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) :
    ef x₁ y₁ x₂ y₂ x₀ y₀ = ef x₀ y₀ x₁ y₁ x₂ y₂ ∧ ef x₂ y₂ x₀ y₀ x₁ y₁ = ef x₀ y₀ x₁ y₁ x₂ y₂ := by
  unfold ef; constructor <;> ring

theorem ef_split (x₀ y₀ x₁ y₁ x₂ y₂ X Y : ℝ) :
    ef x₁ y₁ x₂ y₂ X Y + ef x₂ y₂ x₀ y₀ X Y + ef x₀ y₀ x₁ y₁ X Y = ef x₀ y₀ x₁ y₁ x₂ y₂ := by
  unfold ef; ring

theorem rtri_det {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ} (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) :
    0 < det3 x₀ (y₀ * sr Dn) x₁ (y₁ * sr Dn) x₂ (y₂ * sr Dn) := by
  rw [det3_rp]; exact mul_pos (sr_pos hD) h

/-- The positively oriented coordinate triangle with vertices `rp Dn xᵢ yᵢ`. -/
noncomputable def rtri (Dn : ℝ) (hD : 0 < Dn) (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ)
    (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) : Tri :=
  mkTri x₀ (y₀ * sr Dn) x₁ (y₁ * sr Dn) x₂ (y₂ * sr Dn) (rtri_det hD h).ne'

theorem rtri_pts (Dn : ℝ) (hD : 0 < Dn) (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) :
    (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts 0 = rp Dn x₀ y₀ ∧
    (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts 1 = rp Dn x₁ y₁ ∧
    (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts 2 = rp Dn x₂ y₂ := ⟨rfl, rfl, rfl⟩

/-- **Closed membership from three nonnegative edge functionals.** -/
theorem mem_rtri {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ} (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂)
    {X Y : ℝ} (h₀ : 0 ≤ ef x₀ y₀ x₁ y₁ X Y) (h₁ : 0 ≤ ef x₁ y₁ x₂ y₂ X Y)
    (h₂ : 0 ≤ ef x₂ y₂ x₀ y₀ X Y) :
    rp Dn X Y ∈ (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).carrier := by
  have hs := (sr_pos hD).le
  refine mem_carrier_of_dets (rtri_det hD h) ?_ ?_ ?_
  · have e : det3 X (Y * sr Dn) x₁ (y₁ * sr Dn) x₂ (y₂ * sr Dn) = sr Dn * ef x₁ y₁ x₂ y₂ X Y := by
      unfold det3 ef; ring
    rw [e]; exact mul_nonneg hs h₁
  · have e : det3 x₀ (y₀ * sr Dn) X (Y * sr Dn) x₂ (y₂ * sr Dn) = sr Dn * ef x₂ y₂ x₀ y₀ X Y := by
      unfold det3 ef; ring
    rw [e]; exact mul_nonneg hs h₂
  · rw [det3_rp]; exact mul_nonneg hs h₀

theorem lineFun_rp (Dn px py qx qy X Y : ℝ) :
    lineFun px (py * sr Dn) qx (qy * sr Dn) (rp Dn X Y) = sr Dn * ef px py qx qy X Y := by
  simp only [lineFun_apply, rp_zero, rp_one, ef]; ring

/-- **Closed membership gives three nonnegative edge functionals.** -/
theorem rtri_ef_nonneg {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ}
    (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) {X Y : ℝ}
    (hm : rp Dn X Y ∈ (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).carrier) :
    0 ≤ ef x₀ y₀ x₁ y₁ X Y ∧ 0 ≤ ef x₁ y₁ x₂ y₂ X Y ∧ 0 ≤ ef x₂ y₂ x₀ y₀ X Y := by
  have hs := sr_pos hD
  have h' : 0 < (x₁ - x₀) * (y₂ - y₀) - (x₂ - x₀) * (y₁ - y₀) := h
  obtain ⟨c1, c2⟩ := ef_cyc x₀ y₀ x₁ y₁ x₂ y₂
  have key : ∀ px py qx qy : ℝ,
      (∀ k, 0 ≤ lineFun px (py * sr Dn) qx (qy * sr Dn) ((rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts k)) →
      0 ≤ ef px py qx qy X Y := by
    intro px py qx qy hk
    have := Erdos634.ThickBlockingLemmas.ge_of_forall_pts_ge _ hk _ hm
    rw [lineFun_rp] at this
    exact (mul_nonneg_iff_of_pos_left hs).mp this
  refine ⟨key _ _ _ _ ?_, key _ _ _ _ ?_, key _ _ _ _ ?_⟩ <;> intro k <;> fin_cases k <;>
    simp only [rtri, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    (try rw [show mkPt x₀ (y₀ * sr Dn) = rp Dn x₀ y₀ from rfl]) <;>
    (try rw [show mkPt x₁ (y₁ * sr Dn) = rp Dn x₁ y₁ from rfl]) <;>
    (try rw [show mkPt x₂ (y₂ * sr Dn) = rp Dn x₂ y₂ from rfl]) <;>
    rw [lineFun_rp] <;> refine mul_nonneg hs.le ?_ <;>
    (unfold ef; linarith [h'])

theorem not_mem_rtri_of_edge0 {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ}
    (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) {X Y : ℝ} (hn : ef x₀ y₀ x₁ y₁ X Y < 0) :
    rp Dn X Y ∉ (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).carrier :=
  fun hm => absurd (rtri_ef_nonneg hD h hm).1 (not_le.mpr hn)

theorem not_mem_rtri_of_edge1 {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ}
    (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) {X Y : ℝ} (hn : ef x₁ y₁ x₂ y₂ X Y < 0) :
    rp Dn X Y ∉ (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).carrier :=
  fun hm => absurd (rtri_ef_nonneg hD h hm).2.1 (not_le.mpr hn)

theorem not_mem_rtri_of_edge2 {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ}
    (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) {X Y : ℝ} (hn : ef x₂ y₂ x₀ y₀ X Y < 0) :
    rp Dn X Y ∉ (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).carrier :=
  fun hm => absurd (rtri_ef_nonneg hD h hm).2.2 (not_le.mpr hn)

/-- **Interior membership from three strictly positive edge functionals.** -/
theorem mem_interior_rtri {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ}
    (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) {X Y : ℝ} (h₀ : 0 < ef x₀ y₀ x₁ y₁ X Y)
    (h₁ : 0 < ef x₁ y₁ x₂ y₂ X Y) (h₂ : 0 < ef x₂ y₂ x₀ y₀ X Y) :
    rp Dn X Y ∈ interior (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).carrier := by
  set T := rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h with hT
  set E := ef x₀ y₀ x₁ y₁ x₂ y₂ with hE
  set a := ef x₂ y₂ x₀ y₀ X Y / E with ha
  set b := ef x₀ y₀ x₁ y₁ X Y / E with hb
  have hE0 : E ≠ 0 := h.ne'
  have hpt : rp Dn X Y = T.pts 0 + a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0) := by
    obtain ⟨p0, p1, p2⟩ := rtri_pts Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h
    rw [← hT] at p0 p1 p2
    rw [p0, p1, p2]
    refine plane_ext ?_ ?_
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, rp_zero, ha, hb, hE]
      field_simp
      unfold ef; ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, rp_one, ha, hb, hE]
      field_simp
      unfold ef; ring
  rw [hpt, (edge_combo_mem_iff T a b).2]
  refine ⟨div_pos h₂ h, div_pos h₀ h, ?_⟩
  rw [ha, hb, ← add_div, div_lt_one h, hE, ← ef_split x₀ y₀ x₁ y₁ x₂ y₂ X Y]
  linarith

/-- Rotating the vertex order does not move the carrier. -/
theorem rtri_rot_carrier {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ}
    (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) (h' : 0 < ef x₁ y₁ x₂ y₂ x₀ y₀) :
    (rtri Dn hD x₁ y₁ x₂ y₂ x₀ y₀ h').carrier = (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).carrier := by
  show convexHull ℝ (Set.range _) = convexHull ℝ (Set.range _)
  congr 1
  ext p
  simp only [Set.mem_range, rtri, mkTri_pts]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-! ## 3. A triangle with three known vertices is the coordinate triangle -/

theorem fin3_exhaust : ∀ k₀ k₁ k₂ k : Fin 3, k₀ ≠ k₁ → k₀ ≠ k₂ → k₁ ≠ k₂ →
    k = k₀ ∨ k = k₁ ∨ k = k₂ := by decide

theorem fin3_third : ∀ k₀ k₁ : Fin 3, k₀ ≠ k₁ → ∃ k₂, k₂ ≠ k₀ ∧ k₂ ≠ k₁ := by decide

/-- **A `Tri` whose three vertices are the three coordinate points has the coordinate
triangle's carrier.** -/
theorem carrier_eq_rtri_of_pts {Dn : ℝ} (hD : 0 < Dn) (T : Tri) {k₀ k₁ k₂ : Fin 3}
    (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ}
    (h0 : T.pts k₀ = rp Dn x₀ y₀) (h1 : T.pts k₁ = rp Dn x₁ y₁) (h2 : T.pts k₂ = rp Dn x₂ y₂)
    (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) :
    T.carrier = (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).carrier := by
  show convexHull ℝ (Set.range _) = convexHull ℝ (Set.range _)
  congr 1
  ext p
  simp only [Set.mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    rcases fin3_exhaust k₀ k₁ k₂ k h01 h02 h12 with rfl | rfl | rfl
    · exact ⟨0, by rw [h0]; rfl⟩
    · exact ⟨1, by rw [h1]; rfl⟩
    · exact ⟨2, by rw [h2]; rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact ⟨k₀, h0⟩
    · exact ⟨k₁, h1⟩
    · exact ⟨k₂, h2⟩

/-! ## 4. The unfilled region of a list of placed tiles -/

theorem mem_unfilled_iff {N : ℕ} (D : Dissection N) (l : List (Fin N)) (p : Plane) :
    p ∈ unfilled D l.toFinset ↔ p ∈ D.target.carrier ∧ ∀ i ∈ l, p ∉ (D.tile i).carrier := by
  rw [unfilled, Set.mem_diff, Set.mem_iUnion₂]
  simp only [List.mem_toFinset, not_exists]

/-! ## 5. `hlex` from a closed superset -/

/-- A closed half-plane in the rescaled coordinates. -/
def halfR (Dn α β γ : ℝ) : Set Plane := {p | 0 ≤ α * p 0 + β * (p 1 / sr Dn) + γ}

theorem isClosed_halfR (Dn α β γ : ℝ) : IsClosed (halfR Dn α β γ) := by
  have h0 : Continuous fun q : Plane => q 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have h1 : Continuous fun q : Plane => q 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  exact isClosed_le continuous_const
    (((continuous_const.mul h0).add (continuous_const.mul (h1.div_const _))).add continuous_const)

theorem mem_halfR_rp {Dn : ℝ} (hD : 0 < Dn) (α β γ X Y : ℝ) :
    rp Dn X Y ∈ halfR Dn α β γ ↔ 0 ≤ α * X + β * Y + γ := by
  simp only [halfR, Set.mem_setOf_eq, rp_zero, rp_one]
  rw [mul_div_assoc, div_self (sr_pos hD).ne', mul_one]

theorem lexLE_rp {Dn : ℝ} (hD : 0 < Dn) {xv yv X Y : ℝ} (hY : yv ≤ Y) (hX : yv = Y → xv ≤ X) :
    LexLE (rp Dn xv yv) (rp Dn X Y) := by
  simp only [LexLE, rp_zero, rp_one]
  rcases lt_or_eq_of_le hY with h | h
  · exact Or.inl (mul_lt_mul_of_pos_right h (sr_pos hD))
  · exact Or.inr ⟨by rw [h], hX h⟩

/-- **`hlex` from a closed set `C ⊇ U` on which `v` is lexicographically least.** -/
theorem hlex_of {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) (v : Plane) (C : Set Plane)
    (hC : IsClosed C) (hsub : ∀ p ∈ D.target.carrier, (∀ i ∈ S, p ∉ (D.tile i).carrier) → p ∈ C)
    (hlexC : ∀ p ∈ C, LexLE v p) : ∀ p ∈ closure (unfilled D S), LexLE v p := by
  intro p hp
  refine hlexC p (closure_minimal ?_ hC hp)
  intro q hq
  obtain ⟨hqt, hqn⟩ := hq
  refine hsub q hqt fun i hi hqi => hqn ?_
  exact Set.mem_iUnion₂.mpr ⟨i, hi, hqi⟩

/-! ## 6. `hfree` from an explicit polynomial point -/

theorem pt_ccw_rp (Dn : ℝ) (hD : 0 < Dn) (xv yv a b t : ℝ) :
    rp Dn xv yv + t • (rp Dn a b + (t * sr Dn) • perp (rp Dn a b))
      = rp Dn (xv + a * t - Dn * b * t ^ 2) (yv + b * t + a * t ^ 2) := by
  refine plane_ext ?_ ?_
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, perp_zero, rp_zero, rp_one]
    linear_combination (-(t ^ 2 * b)) * sr_sq hD
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, perp_one, rp_zero, rp_one]
    ring

/-- **`hfree` from a one-parameter family** `t ↦ v + t·(d + t√Dn·d⊥)` in `U` for `0 < t ≤ τ`. -/
theorem hfree_of {Dn B : ℝ} (hD : 0 < Dn) (hB : 1 ≤ B) (hsB : sr Dn < B) {τ : ℝ} (hτ : 0 < τ)
    (v d : Plane) (U : Set Plane)
    (key : ∀ t : ℝ, 0 < t → t ≤ τ → v + t • (d + (t * sr Dn) • perp d) ∈ U) :
    ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧ v + t • (d + s • perp d) ∈ U := by
  intro ε hε
  have hs := sr_pos hD
  set t := min (ε / (2 * B)) τ with ht
  have ht0 : 0 < t := by positivity
  have htτ : t ≤ τ := min_le_right _ _
  have htB : t ≤ ε / (2 * B) := min_le_left _ _
  have htε : t < ε := by
    have : ε / (2 * B) < ε := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  refine ⟨t, t * sr Dn, ht0, htε, by positivity, ?_, key t ht0 htτ⟩
  have h1 : t * sr Dn < t * B := mul_lt_mul_of_pos_left hsB ht0
  have h2 : t * B ≤ ε / 2 := by
    calc t * B ≤ ε / (2 * B) * B := mul_le_mul_of_nonneg_right htB (by positivity)
      _ = ε / 2 := by field_simp
  linarith

/-! ## 7. `hblocked`: the clockwise wedge is inside a placed tile, or below the base -/

theorem cw_eq {Dn : ℝ} (hD : 0 < Dn) (v d : Plane) (t s : ℝ) :
    v + t • (d - s • perp d) = v + t • (d - (s / sr Dn) • (sr Dn • perp d)) := by
  rw [smul_smul, div_mul_cancel₀ _ (sr_pos hD).ne']

theorem sr_smul_perp_rp {Dn : ℝ} (hD : 0 < Dn) (a b : ℝ) :
    sr Dn • perp (rp Dn a b) = rp Dn (-(Dn * b)) a := by
  refine plane_ext ?_ ?_
  · simp only [PiLp.smul_apply, smul_eq_mul, perp_zero, rp_zero, rp_one]
    linear_combination (-b) * sr_sq hD
  · simp only [PiLp.smul_apply, smul_eq_mul, perp_one, rp_zero, rp_one]
    ring

/-- **`hblocked` from `wedge_interior`**: a triangle `T` inside a placed tile has vertex `0` at
`v` and the clockwise wedge of `d` at `v` lies in its interior.  (`T` is the placed tile itself
when `v` is one of its vertices, and a sub-triangle with a vertex at `v` when `v` lies on one of
its edges — a T-junction.) -/
theorem hblocked_of_wedge {Dn : ℝ} (hD : 0 < Dn) (h1 : 1 < sr Dn) {N : ℕ} (D : Dissection N)
    (S : Finset (Fin N)) {i : Fin N} (hi : i ∈ S) (v d : Plane) (T : Tri)
    (hT : T.carrier ⊆ (D.tile i).carrier) (hT0 : T.pts 0 = v)
    (hw : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      T.pts 0 + t • (d - s • (sr Dn • perp d)) ∈ interior T.carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      v + t • (d - s • perp d) ∉ unfilled D S := by
  obtain ⟨δ, hδ, h⟩ := hw
  refine ⟨δ, hδ, fun t s ht htδ hs hsδ hU => ?_⟩
  have hs' : 0 < s / sr Dn := div_pos hs (by linarith)
  have hsδ' : s / sr Dn < δ := by
    calc s / sr Dn < s := div_lt_self hs h1
      _ < δ := hsδ
  have hmem := h t (s / sr Dn) ht htδ hs' hsδ'
  rw [hT0, ← cw_eq hD] at hmem
  obtain ⟨-, hn⟩ := hU
  apply hn
  exact Set.mem_iUnion₂.mpr ⟨i, hi, hT (interior_subset hmem)⟩

theorem target_y_nonneg {Dn : ℝ} (hD : 0 < Dn) {tx ax ay : ℝ} (htx : 0 < tx)
    (h : 0 < ef 0 0 tx 0 ax ay) {p : Plane} (hp : p ∈ (rtri Dn hD 0 0 tx 0 ax ay h).carrier) :
    0 ≤ p 1 := by
  obtain ⟨X, Y, rfl⟩ := exists_rp hD p
  have := (rtri_ef_nonneg hD h hp).1
  unfold ef at this
  rw [rp_one]
  have hY : 0 ≤ Y := by nlinarith
  exact mul_nonneg hY (sr_pos hD).le

/-- **`hblocked` below the base**: at a base point with the ray along the base, the clockwise
wedge is below `y = 0`, outside the target. -/
theorem hblocked_base {Dn : ℝ} (hD : 0 < Dn) {N : ℕ} (D : Dissection N) (S : Finset (Fin N))
    (hy : ∀ p ∈ D.target.carrier, 0 ≤ p 1) (xv : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      rp Dn xv 0 + t • (rp Dn 1 0 - s • perp (rp Dn 1 0)) ∉ unfilled D S := by
  refine ⟨1, one_pos, fun t s ht _ hs _ hU => ?_⟩
  have := hy _ hU.1
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, perp_one, rp_zero,
    rp_one] at this
  nlinarith [mul_pos ht hs]

/-! ## 8. The three kills -/

/-- **Escape**: a vertex of a tile outside the target. -/
theorem escape_of {N : ℕ} (D : Dissection N) {T : Tri} (htarget : D.target.carrier = T.carrier)
    (j : Fin N) (k : Fin 3) {w : Plane} (hpt : (D.tile j).pts k = w) (hout : w ∉ T.carrier) :
    False := by
  apply hout
  rw [← htarget, ← hpt]
  exact Erdos634.BaseSelection.tile_subset_target D j (subset_convexHull ℝ _ (Set.mem_range_self k))

/-- **Overlap**: a common interior point of two distinct tiles. -/
theorem overlap_of {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {Ti Tj : Tri}
    (hi : (D.tile i).carrier = Ti.carrier) (hj : (D.tile j).carrier = Tj.carrier) {w : Plane}
    (hwi : w ∈ interior Ti.carrier) (hwj : w ∈ interior Tj.carrier) : False := by
  have hdis : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
    D.interiors_disjoint hij
  rw [hi, hj] at hdis
  exact Set.disjoint_left.mp hdis hwi hwj

/-- Tile `i` has an edge on the base from `(x₀,0)` to `(x₁,0)`. -/
def HasBaseEdge {N : ℕ} (D : Dissection N) (i : Fin N) (x₀ x₁ : ℝ) : Prop :=
  ∃ k₀ k₁ : Fin 3, k₀ ≠ k₁ ∧ (D.tile i).pts k₀ = mkPt x₀ 0 ∧ (D.tile i).pts k₁ = mkPt x₁ 0

theorem tri_det_eq (T : Tri) : T.det = (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1
    - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0 := rfl

/-- The third vertex of a tile with a base edge lies strictly above the base. -/
theorem third_above (T : Tri) (hy : ∀ p ∈ T.carrier, 0 ≤ p 1) {k₀ k₁ : Fin 3} (hk : k₀ ≠ k₁)
    {x₀ x₁ : ℝ} (h0 : T.pts k₀ = mkPt x₀ 0) (h1 : T.pts k₁ = mkPt x₁ 0) :
    ∃ k₂, k₂ ≠ k₀ ∧ k₂ ≠ k₁ ∧ 0 < (T.pts k₂) 1 := by
  obtain ⟨k₂, h20, h21⟩ := fin3_third k₀ k₁ hk
  refine ⟨k₂, h20, h21, ?_⟩
  have hnn := hy _ (subset_convexHull ℝ _ (Set.mem_range_self k₂))
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    have hall : ∀ k, (T.pts k) 1 = 0 := by
      intro k
      rcases fin3_exhaust k₀ k₁ k₂ k hk (Ne.symm h20) (Ne.symm h21) with rfl | rfl | rfl
      · rw [h0]; simp
      · rw [h1]; simp
      · exact h.symm
    apply T.det_ne_zero
    rw [tri_det_eq]
    simp only [PiLp.sub_apply, hall]
    ring

theorem fin3_succ : ∀ k₀ k₁ : Fin 3, k₀ ≠ k₁ → k₁ = 1 + k₀ ∨ k₁ = 2 + k₀ := by decide

/-- **The wedge just above a base edge, at its left end, is inside the tile.** -/
theorem base_wedge (T : Tri) {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂)
    {x₀ x₁ : ℝ} (h0 : T.pts k₀ = mkPt x₀ 0) (h1 : T.pts k₁ = mkPt x₁ 0) (hq : 0 < (T.pts k₂) 1)
    (hx : x₀ < x₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      mkPt (x₀ + t) (t * s) ∈ interior T.carrier := by
  set T' := T.relabel (Equiv.addRight k₀) with hT'
  have hTc : T'.carrier = T.carrier := relabel_carrier _ _
  have p0 : T'.pts 0 = mkPt x₀ 0 := by rw [hT', Tri.relabel_pts]; simpa using h0
  have hpt : ∀ t s : ℝ, mkPt (x₀ + t) (t * s) = T'.pts 0 + t • (mkPt 1 0 - s • mkPt 0 (-1)) := by
    intro t s; rw [p0]; refine plane_ext ?_ ?_ <;> simp
  rw [← hTc]
  have hx' : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx.ne'
  rcases fin3_succ k₀ k₁ h01 with hk | hk
  · -- `k₁ = 1 + k₀`: the base edge is `pts 0 → pts 1`, the third vertex is `pts 2`
    have hk2 : k₂ = 2 + k₀ := by
      rcases fin3_succ k₀ k₂ h02 with h | h
      · exact absurd (h.trans hk.symm) (Ne.symm h12)
      · exact h
    have p1 : T'.pts 1 = mkPt x₁ 0 := by
      rw [hT', Tri.relabel_pts]; simp only [Equiv.coe_addRight]; rw [← hk]; exact h1
    have p2 : 0 < (T'.pts 2) 1 := by
      rw [hT', Tri.relabel_pts]; simp only [Equiv.coe_addRight]; rw [← hk2]; exact hq
    set q := (T'.pts 2) 1 with hqdef
    set p := (T'.pts 2) 0 with hpdef
    have hq0 : q ≠ 0 := p2.ne'
    have hd : mkPt 1 0 = (1 / (x₁ - x₀)) • (T'.pts 1 - T'.pts 0) + (0:ℝ) • (T'.pts 2 - T'.pts 0) := by
      rw [p0, p1]; refine plane_ext ?_ ?_
      · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero]
        field_simp; ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_one]
        ring
    have hn : mkPt 0 (-1) = ((p - x₀) / (q * (x₁ - x₀))) • (T'.pts 1 - T'.pts 0)
        + (-1 / q) • (T'.pts 2 - T'.pts 0) := by
      rw [p0, p1]; refine plane_ext ?_ ?_
      · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, ← hpdef]
        field_simp; ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_one, ← hqdef]
        field_simp; ring
    obtain ⟨δ, hδ, hw⟩ := wedge_interior T' (mkPt 1 0) (mkPt 0 (-1)) _ _ _ _ hd hn
      (Or.inl (by positivity)) (Or.inr ⟨rfl, div_neg_of_neg_of_pos (by norm_num) p2⟩)
    exact ⟨δ, hδ, fun t s ht htδ hs hsδ => by rw [hpt]; exact hw t s ht htδ hs hsδ⟩
  · -- `k₁ = 2 + k₀`: the base edge is `pts 0 → pts 2`, the third vertex is `pts 1`
    have hk2 : k₂ = 1 + k₀ := by
      rcases fin3_succ k₀ k₂ h02 with h | h
      · exact h
      · exact absurd (h.trans hk.symm) (Ne.symm h12)
    have p2 : T'.pts 2 = mkPt x₁ 0 := by
      rw [hT', Tri.relabel_pts]; simp only [Equiv.coe_addRight]; rw [← hk]; exact h1
    have p1 : 0 < (T'.pts 1) 1 := by
      rw [hT', Tri.relabel_pts]; simp only [Equiv.coe_addRight]; rw [← hk2]; exact hq
    set q := (T'.pts 1) 1 with hqdef
    set p := (T'.pts 1) 0 with hpdef
    have hq0 : q ≠ 0 := p1.ne'
    have hd : mkPt 1 0 = (0:ℝ) • (T'.pts 1 - T'.pts 0) + (1 / (x₁ - x₀)) • (T'.pts 2 - T'.pts 0) := by
      rw [p0, p2]; refine plane_ext ?_ ?_
      · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero]
        field_simp; ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_one]
        ring
    have hn : mkPt 0 (-1) = (-1 / q) • (T'.pts 1 - T'.pts 0)
        + ((p - x₀) / (q * (x₁ - x₀))) • (T'.pts 2 - T'.pts 0) := by
      rw [p0, p2]; refine plane_ext ?_ ?_
      · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, ← hpdef]
        field_simp; ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_one, ← hqdef]
        field_simp; ring
    obtain ⟨δ, hδ, hw⟩ := wedge_interior T' (mkPt 1 0) (mkPt 0 (-1)) _ _ _ _ hd hn
      (Or.inr ⟨rfl, div_neg_of_neg_of_pos (by norm_num) p1⟩) (Or.inl (by positivity))
    exact ⟨δ, hδ, fun t s ht htδ hs hsδ => by rw [hpt]; exact hw t s ht htδ hs hsδ⟩

theorem pts_injective (T : Tri) : Function.Injective T.pts := T.indep.injective

/-- **The base-word kill.**  Two tiles with base edges starting at the same base point and
running to the right to different endpoints cannot both belong to a dissection. -/
theorem base_edge_clash {N : ℕ} (D : Dissection N) (hy : ∀ i, ∀ p ∈ (D.tile i).carrier, 0 ≤ p 1)
    {i j : Fin N} {x₀ x₁ x₁' : ℝ} (hi : HasBaseEdge D i x₀ x₁) (hj : HasBaseEdge D j x₀ x₁')
    (h1 : x₀ < x₁) (h1' : x₀ < x₁') (hne : x₁ ≠ x₁') : False := by
  obtain ⟨k₀, k₁, hk, h0, h1e⟩ := hi
  obtain ⟨k₀', k₁', hk', h0', h1e'⟩ := hj
  obtain ⟨k₂, h20, h21, hq⟩ := third_above (D.tile i) (hy i) hk h0 h1e
  obtain ⟨k₂', h20', h21', hq'⟩ := third_above (D.tile j) (hy j) hk' h0' h1e'
  by_cases hij : i = j
  · subst hij
    have e0 : k₀ = k₀' := pts_injective _ (h0.trans h0'.symm)
    have e1 : k₁ ≠ k₁' := by
      intro e; rw [e, h1e'] at h1e
      have := congrArg (fun p : Plane => p 0) h1e
      simp at this; exact hne this.symm
    have hk2 : k₂ = k₁' := by
      rcases fin3_exhaust k₀ k₁ k₂ k₁' hk (Ne.symm h20) (Ne.symm h21) with h | h | h
      · exact absurd (h.trans e0) (Ne.symm hk')
      · exact absurd h (Ne.symm e1)
      · exact h.symm
    rw [hk2, h1e'] at hq
    simp at hq
  · obtain ⟨δ₁, hδ₁, hw₁⟩ := base_wedge (D.tile i) hk h20.symm h21.symm h0 h1e hq h1
    obtain ⟨δ₂, hδ₂, hw₂⟩ := base_wedge (D.tile j) hk' h20'.symm h21'.symm h0' h1e' hq' h1'
    set t := min δ₁ δ₂ / 2 with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t < δ₁ := by
      have := min_le_left δ₁ δ₂; linarith
    have ht2 : t < δ₂ := by
      have := min_le_right δ₁ δ₂; linarith
    have hm₁ := hw₁ t t ht0 ht1 ht0 ht1
    have hm₂ := hw₂ t t ht0 ht2 ht0 ht2
    have hdis : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
      D.interiors_disjoint hij
    exact Set.disjoint_left.mp hdis hm₁ hm₂

theorem tiles_y_nonneg {N : ℕ} (D : Dissection N) {T : Tri} (htarget : D.target.carrier = T.carrier)
    (hy : ∀ p ∈ T.carrier, 0 ≤ p 1) : ∀ i, ∀ p ∈ (D.tile i).carrier, 0 ≤ p 1 :=
  fun i p hp => hy p (htarget ▸ Erdos634.BaseSelection.tile_subset_target D i hp)

/-! ## 9. The third vertex of a placement in coordinates -/

theorem placeThird_rp {Dn : ℝ} (hD : 0 < Dn) (xv yv a b ℓ₁ ℓ₂ ℓ₃ p q : ℝ)
    (hp : (ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) / (2 * ℓ₁) = p) (hq : 0 ≤ q)
    (hq2 : ℓ₂ ^ 2 - p ^ 2 = Dn * q ^ 2) :
    placeThird (rp Dn xv yv) (rp Dn a b) ℓ₁ ℓ₂ ℓ₃
      = rp Dn (xv + p * a - Dn * q * b) (yv + p * b + q * a) := by
  rw [placeThird, hp, hq2]
  have hsq : Real.sqrt (Dn * q ^ 2) = q * sr Dn := by
    rw [Real.sqrt_mul hD.le, Real.sqrt_sq hq, mul_comm]; rfl
  rw [hsq]
  refine plane_ext ?_ ?_
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, perp_zero, rp_zero, rp_one]
    linear_combination (-(q * b)) * sr_sq hD
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, perp_one, rp_zero, rp_one]
    ring

/-- The side lengths of a coordinate model, as `six_placements` wants them. -/
theorem model_sides_rp {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ}
    (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ea : (x₀ - x₁) ^ 2 + Dn * (y₀ - y₁) ^ 2 = a ^ 2)
    (eb : (x₁ - x₂) ^ 2 + Dn * (y₁ - y₂) ^ 2 = b ^ 2)
    (ec : (x₀ - x₂) ^ 2 + Dn * (y₀ - y₂) ^ 2 = c ^ 2) :
    dist ((rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts 0) ((rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts 1) = a ∧
    dist ((rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts 1) ((rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts 2) = b ∧
    dist ((rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts 0) ((rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).pts 2) = c := by
  obtain ⟨p0, p1, p2⟩ := rtri_pts Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h
  rw [p0, p1, p2]
  exact ⟨dist_rp hD ha ea, dist_rp hD hb eb, dist_rp hD hc ec⟩

/-! ## 10. Witness plumbing: a separating edge line gives disjoint interiors -/

/-- **Two coordinate triangles on opposite closed sides of a line have disjoint interiors.** -/
theorem disj_of_sep_edge {Dn : ℝ} (hD : 0 < Dn) (T U : Tri) (px py qx qy : ℝ)
    (hpq : px ≠ qx ∨ py ≠ qy)
    (hT : ∀ k, ∃ X Y, T.pts k = rp Dn X Y ∧ ef px py qx qy X Y ≤ 0)
    (hU : ∀ k, ∃ X Y, U.pts k = rp Dn X Y ∧ 0 ≤ ef px py qx qy X Y) :
    Disjoint (interior T.carrier) (interior U.carrier) := by
  have hs := sr_pos hD
  refine interiors_disjoint_of_separating (lineFun px (py * sr Dn) qx (qy * sr Dn)) ?_ 0 ?_ ?_
  · refine lineFun_linear_ne_zero ?_
    rcases hpq with h | h
    · exact Or.inl h
    · exact Or.inr (fun e => h (mul_right_cancel₀ hs.ne' e))
  · refine le_of_forall_pts_le _ ?_
    intro k
    obtain ⟨X, Y, e, h⟩ := hT k
    rw [e, lineFun_rp]
    exact mul_nonpos_of_nonneg_of_nonpos hs.le h
  · refine Erdos634.ThickBlockingLemmas.ge_of_forall_pts_ge _ ?_
    intro k
    obtain ⟨X, Y, e, h⟩ := hU k
    rw [e, lineFun_rp]
    exact mul_nonneg hs.le h

theorem rtri_subset {Dn : ℝ} (hD : 0 < Dn) {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ} (h : 0 < ef x₀ y₀ x₁ y₁ x₂ y₂)
    (T : Tri) (h0 : rp Dn x₀ y₀ ∈ T.carrier) (h1 : rp Dn x₁ y₁ ∈ T.carrier)
    (h2 : rp Dn x₂ y₂ ∈ T.carrier) : (rtri Dn hD x₀ y₀ x₁ y₁ x₂ y₂ h).carrier ⊆ T.carrier := by
  refine carrier_subset_of_pts_mem ?_
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

end Erdos634.CertNode
