import Erdos634.BaseBetaTargetCoord
import Erdos634.JunctionWedge

/-!
# A junction-filler coordinate model for a thick tile: `(e,f) = (2,3)`, `(a,b,c) = (6,5,9)`

Erdős #634, base-`β` branch, `e ≥ 2`.  `MarchCoords.lean`/`MarchKills.lean` build the `e = 1`
march's coordinate model for the tile `(a,b,c) = (f, f²−1, f²)`, where `a` is the *smallest* side.
At `e ≥ 2` this stops being true: the tile is `(a,b,c) = (ef, f²−e², f²)`, and once `e/f` is close
enough to `1` (e.g. `e = 2, f = 3`: `a = 6 > b = 5`), `a` is no longer smallest.  Nothing in
`MarchCoords`/`MarchKills` is written for that case — the definitions are literal functions of a
single variable `f` under the `(f, f²−1, f²)` convention, not of a general `(a,b,c)`, so there is no
substitution that produces a thick-member filler from them.

**What this file finds, worked by hand first (`private/GOAL_PRIMES.md`, dated section) and then
checked here in exact rational and surd arithmetic:** the *geometry* does not qualitatively change.
The junction-filler construction is the elementary "two points at distance `b`, `c` from the ends of
an `a`-edge" computation (solve `x²+y² = b²`, `(x−a)²+y² = c²}`), which is just the law of cosines —
it does not care whether `a < b` or `a > b`.  Redone for `(a,b,c) = (6,5,9)` it gives

    dGB = (a²+b²−c²)/(2a) = −5/3,   dBG = (a²+c²−b²)/(2a) = 23/3,   h² = b² − dGB² = 200/9,

and every sign that mattered at `e = 1` has the **same** sign here: `dGB < 0`, `dBG − a = 5/3 > 0`.
So the two a-tile orientations (`BG`, `GB`), the forced junction filler swapping `b ↔ c` between
them, and the `BG → GB` / `GB → BG` wedge asymmetry all transfer to this thick member **unchanged
in kind**, just with different numbers.  This is a genuine, checked instance of the `e,f`-general
machinery (`JunctionWedge`, `WedgeExtremal`) applying outside `e = 1`, not previously exhibited.

**What does not transfer, named precisely so it is not silently dropped.**  `MarchKills.lean`'s
*second*, deeper construction — `offsetFiller`, the second-generation filler realising the derived
run's residual defect (`MarchCoords.defect_scales_to_one`, exactly `1` at `e = 1`) — is **not**
attempted here.  Its defect generalises to `c − b = e²` (checked below,
`defect_is_e_sq`): `1` at `e = 1`, `4` at `e = 2`.  That changes the arithmetic character of the
residue argument (`FanKill.one_is_gap` is a fact about the specific gap `1`, not about `e²`), and
redoing it is a second, separate piece of work — explicitly out of scope here, per the task's own
restriction against generalising this pass over `(e,f)`.  Likewise `slot_apex_heights`' confinement
inequality `f/(f²−1) < 1` (i.e. `a/b < 1`) is **false** at this instance (`a/b = 6/5`), so the
`b`-slot-tile confinement bound from `MarchKills.march_confined` does not transfer either; nothing
using it is claimed here.

## What is proved

* The coordinate identities analogous to `MarchCoords.gb_left/gb_right/bg_left/bg_right/
  offsets_complementary`, in exact rationals, for `(a,b,c) = (6,5,9)`.
* `aTileBG63`, `aTileGB63` — the two `a`-tile orientations as `Tri`s, and `flushFillerBG63`,
  `flushFillerGB63` — the two junction fillers, each proved **congruent to the tile**
  (analogue of `MarchCoords.filler_forced`), with `b` and `c` exchanged between the two chiralities
  (the actual content of "two placements", not a coincidental multiset equality).
* `wedge_asymmetric_63` — the same sign computation as `MarchCoords.transition_asymmetric`: `BG → GB`
  straddles the junction (forbidden), `GB → BG` does not.  Same conclusion as `e = 1`, checked fresh
  at this tile.
* `hcorner_flush_63` — **the new content**: the filler's own corner angle at the junction, computed
  from these exact coordinates via `AngleThreshold.cos_of_sides`, equals `BaseBetaTargetCoord.
  modelAlpha 2 3` (`cos = 7/9`, matching `cos_modelAlpha` exactly).  This is `JunctionWedge.
  junction_step`'s `hcorner` hypothesis, discharged from a real configuration rather than assumed,
  at an instance with `e ≥ 2`.
* `junction_step_63` — `JunctionWedge.junction_step` specialised to `α := modelAlpha 2 3`,
  `β := modelBeta 2 3`: an instantiation of the *e,f*-general wedge machinery at this thick member,
  with `hsum`/`hα`/`hβ` discharged by real numbers (not left as free hypotheses).

## What is not proved, honestly

`junction_step_63`'s own hypotheses `hφ`, `hψ`, `hu` (about `Orientation.oangle`) are **not**
discharged from the coordinates here — they are not discharged from coordinates anywhere in this
corpus even at `e = 1` (`JunctionWedge.march_junction_real` carries them as hypotheses too); closing
that gap is a separate piece of Mathlib `oangle` work, not attempted.  What *is* new and checked is
that `hcorner` — the one hypothesis with actual content, tying the abstract wedge angle to a real
tile — holds at this instance.  No Rule 0 label moves and no `(e,f)`-general theorem is claimed:
this is one instance, `(e,f) = (2,3)`.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.ThickJunctionCoords

open Erdos634.Geometry Erdos634.CertCoord Erdos634.BaseBetaTargetCoord

/-! ## 1. The tile and its offsets, in exact rationals -/

/-- The thick tile's side lengths at `(e,f) = (2,3)`: `a = ef = 6`, `b = f² − e² = 5`,
`c = f² = 9`.  Indeed `a > b`: this is the thick case. -/
def a63 : ℝ := 6
def b63 : ℝ := 5
def c63 : ℝ := 9

theorem b63_lt_a63 : b63 < a63 := by simp only [a63, b63]; norm_num

/-- The apex offset from the `γ`-end (`GB`: `γ` at the left).  Same law-of-cosines formula as
`MarchCoords.dGB`, `(a²+b²−c²)/(2a)`, re-solved for `(6,5,9)`. -/
noncomputable def dGB63 : ℝ := -5 / 3

/-- The apex offset from the `β`-end (`BG`: `β` at the left), `(a²+c²−b²)/(2a)`. -/
noncomputable def dBG63 : ℝ := 23 / 3

/-- The common squared apex height, `b² − dGB63²`. -/
noncomputable def h2_63 : ℝ := 200 / 9

/-- **`GB` places the apex at distance `b` from the left end.** -/
theorem gb_left63 : dGB63 ^ 2 + h2_63 = b63 ^ 2 := by
  simp only [dGB63, h2_63, b63]; norm_num

/-- **`GB` places the apex at distance `c` from the right end.** -/
theorem gb_right63 : (dGB63 - a63) ^ 2 + h2_63 = c63 ^ 2 := by
  simp only [dGB63, h2_63, a63, c63]; norm_num

/-- **`BG` places the apex at distance `c` from the left end.** -/
theorem bg_left63 : dBG63 ^ 2 + h2_63 = c63 ^ 2 := by
  simp only [dBG63, h2_63, c63]; norm_num

/-- **`BG` places the apex at distance `b` from the right end.** -/
theorem bg_right63 : (dBG63 - a63) ^ 2 + h2_63 = b63 ^ 2 := by
  simp only [dBG63, h2_63, a63, b63]; norm_num

/-- **The two offsets are complementary**: `dGB63 + dBG63 = a63`, exactly as
`MarchCoords.offsets_complementary` — this identity never used `a` vs `b` order. -/
theorem offsets_complementary63 : dGB63 + dBG63 = a63 := by
  simp only [dGB63, dBG63, a63]; norm_num

/-- **The defect of the derived run generalises `MarchCoords.defect_scales_to_one`'s `1` to `e²`.**
At `e = 1`, `c − b = f² − (f² − 1) = 1`.  At `(e,f) = (2,3)`, `c − b = 9 − 5 = 4 = e²`.  This is
computed for the record (it is what makes `MarchKills.offsetFiller`'s second-generation step *not*
transfer verbatim: the residue argument there is specific to the gap `1`, not to `e²`), and is not
used elsewhere in this file. -/
theorem defect_is_e_sq : c63 - b63 = (2 : ℝ) ^ 2 := by simp only [c63, b63]; norm_num

/-! ## 2. The apex height, and the two `a`-tile placements -/

/-- The apex height: `√(200/9) = 10√2/3`. -/
noncomputable def apexH63 : ℝ := 10 * Real.sqrt 2 / 3

theorem apexH63_pos : 0 < apexH63 := by unfold apexH63; positivity

theorem apexH63_sq : apexH63 ^ 2 = h2_63 := by
  unfold apexH63 h2_63
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem det_aTileBG63 (t : ℝ) : det3 (t + 6) 0 t 0 (t + dBG63) apexH63 ≠ 0 := by
  have : det3 (t + 6) 0 t 0 (t + dBG63) apexH63 = -(6 * apexH63) := by unfold det3; ring
  rw [this]; exact neg_ne_zero.mpr (mul_pos (by norm_num) apexH63_pos).ne'

theorem det_aTileGB63 (t : ℝ) : det3 t 0 (t + 6) 0 (t + dGB63) apexH63 ≠ 0 := by
  have : det3 t 0 (t + 6) 0 (t + dGB63) apexH63 = 6 * apexH63 := by unfold det3; ring
  rw [this]; exact (mul_pos (by norm_num) apexH63_pos).ne'

theorem det_flushFillerBG63 (t : ℝ) :
    det3 (t + 6) 0 (t + 6 + dBG63) apexH63 (t + dBG63) apexH63 ≠ 0 := by
  have : det3 (t + 6) 0 (t + 6 + dBG63) apexH63 (t + dBG63) apexH63 = 6 * apexH63 := by
    unfold det3; ring
  rw [this]; exact (mul_pos (by norm_num) apexH63_pos).ne'

theorem det_flushFillerGB63 (t : ℝ) :
    det3 (t + 6) 0 (t + 6 + dGB63) apexH63 (t + dGB63) apexH63 ≠ 0 := by
  have : det3 (t + 6) 0 (t + 6 + dGB63) apexH63 (t + dGB63) apexH63 = 6 * apexH63 := by
    unfold det3; ring
  rw [this]; exact (mul_pos (by norm_num) apexH63_pos).ne'

/-- The `BG` `a`-tile on `[t, t+6]`: right base corner, left base corner, apex `(t+dBG63, h)`.
Vertex order matches `MarchKills.aTileBG`'s convention. -/
noncomputable def aTileBG63 (t : ℝ) : Tri :=
  mkTri (t + 6) 0 t 0 (t + dBG63) apexH63 (det_aTileBG63 t)

/-- The `GB` `a`-tile on `[t, t+6]`: left base corner, right base corner, apex `(t+dGB63, h)`. -/
noncomputable def aTileGB63 (t : ℝ) : Tri :=
  mkTri t 0 (t + 6) 0 (t + dGB63) apexH63 (det_aTileGB63 t)

/-- The flush filler at the junction `t+6` of two `BG`-oriented `a`-tiles on `[t,t+6]`,
`[t+6,t+12]`: the junction, the right tile's own apex, and the left tile's apex. -/
noncomputable def flushFillerBG63 (t : ℝ) : Tri :=
  mkTri (t + 6) 0 (t + 6 + dBG63) apexH63 (t + dBG63) apexH63 (det_flushFillerBG63 t)

/-- The flush filler at the junction `t+6` of two `GB`-oriented `a`-tiles on `[t,t+6]`,
`[t+6,t+12]`: the junction, the right tile's own apex, and the left tile's apex — the same vertex
order as `flushFillerBG63`, with `dGB63` in place of `dBG63`. -/
noncomputable def flushFillerGB63 (t : ℝ) : Tri :=
  mkTri (t + 6) 0 (t + 6 + dGB63) apexH63 (t + dGB63) apexH63 (det_flushFillerGB63 t)

/-! ## 3. The two chiralities: the filler is forced, and swaps `b ↔ c` -/

theorem dist_sq_zero_apex63 (x₁ x₂ : ℝ) :
    dist (mkPt x₁ 0) (mkPt x₂ apexH63) ^ 2 = (x₁ - x₂) ^ 2 + h2_63 := by
  rw [dist_sq_mkPt, zero_sub, neg_sq, apexH63_sq]

theorem dist_sq_apex_apex63 (x₁ x₂ : ℝ) :
    dist (mkPt x₁ apexH63) (mkPt x₂ apexH63) ^ 2 = (x₁ - x₂) ^ 2 := by
  rw [dist_sq_mkPt]; ring

/-- **The `BG`-`BG` junction filler is congruent to the tile**, sides `b², c², a²` in that order:
the near apex (the left tile's own) is at distance `b`, the far apex (the right tile's own) at
distance `c`, and the two apexes are `a` apart.  This is the thick-member analogue of
`MarchCoords.filler_congruent_bg`. -/
theorem flushFillerBG63_sides :
    dist ((flushFillerBG63 0).pts 0) ((flushFillerBG63 0).pts 2) ^ 2 = b63 ^ 2 ∧
    dist ((flushFillerBG63 0).pts 0) ((flushFillerBG63 0).pts 1) ^ 2 = c63 ^ 2 ∧
    dist ((flushFillerBG63 0).pts 1) ((flushFillerBG63 0).pts 2) ^ 2 = a63 ^ 2 := by
  simp only [flushFillerBG63, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · rw [dist_sq_zero_apex63]; simp only [h2_63, dBG63, b63]; norm_num
  · rw [dist_sq_zero_apex63]; simp only [h2_63, dBG63, c63]; norm_num
  · rw [dist_sq_apex_apex63]; simp only [a63]; norm_num

/-- **The `GB`-`GB` junction filler is congruent to the tile**, with `b` and `c` exchanged relative
to `flushFillerBG63_sides`: the near apex (now the right tile's own) is at distance `c`, the far
apex at distance `b`.  This exchange — not a restatement — is the two chiralities. -/
theorem flushFillerGB63_sides :
    dist ((flushFillerGB63 0).pts 0) ((flushFillerGB63 0).pts 2) ^ 2 = c63 ^ 2 ∧
    dist ((flushFillerGB63 0).pts 0) ((flushFillerGB63 0).pts 1) ^ 2 = b63 ^ 2 ∧
    dist ((flushFillerGB63 0).pts 1) ((flushFillerGB63 0).pts 2) ^ 2 = a63 ^ 2 := by
  simp only [flushFillerGB63, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · rw [dist_sq_zero_apex63]; simp only [h2_63, dGB63, c63]; norm_num
  · rw [dist_sq_zero_apex63]; simp only [h2_63, dGB63, b63]; norm_num
  · rw [dist_sq_apex_apex63]; simp only [a63]; norm_num

/-- **The filler is forced, and the two chiralities are exactly two.**  Restates
`flushFillerBG63_sides`/`flushFillerGB63_sides` side by side: both junction fillers are congruent
to the tile, with `b` and `c` exchanged between them — matching `MarchCoords.filler_forced`'s
conclusion at this thick instance. -/
theorem filler_forced_63 :
    (dist ((flushFillerBG63 0).pts 0) ((flushFillerBG63 0).pts 2) ^ 2 = b63 ^ 2 ∧
     dist ((flushFillerBG63 0).pts 0) ((flushFillerBG63 0).pts 1) ^ 2 = c63 ^ 2 ∧
     dist ((flushFillerBG63 0).pts 1) ((flushFillerBG63 0).pts 2) ^ 2 = a63 ^ 2) ∧
    (dist ((flushFillerGB63 0).pts 0) ((flushFillerGB63 0).pts 2) ^ 2 = c63 ^ 2 ∧
     dist ((flushFillerGB63 0).pts 0) ((flushFillerGB63 0).pts 1) ^ 2 = b63 ^ 2 ∧
     dist ((flushFillerGB63 0).pts 1) ((flushFillerGB63 0).pts 2) ^ 2 = a63 ^ 2) :=
  ⟨flushFillerBG63_sides, flushFillerGB63_sides⟩

/-! ## 4. The wedge asymmetry: same signs, same conclusion as `e = 1` -/

/-- **`BG → GB` straddles the junction; `GB → BG` does not.**  Exactly
`MarchCoords.transition_asymmetric`'s two sign facts, recomputed for `(6,5,9)`: they come out with
the same signs as at `e = 1` (`dBG63 − a63 > 0`, `dGB63 < 0`), so the conclusion — `BG` cannot be
followed by `GB` at an `a|a` junction, `GB` can be followed by `BG` — is unchanged in kind. -/
theorem wedge_asymmetric_63 :
    (0 < dBG63 - a63 ∧ dGB63 < 0) ∧ ¬ (0 < dGB63 - a63 ∧ dBG63 < 0) := by
  refine ⟨⟨by simp only [dBG63, a63]; norm_num, by simp only [dGB63]; norm_num⟩, ?_⟩
  rintro ⟨h1, -⟩
  revert h1; simp only [dGB63, a63]; norm_num

/-! ## 5. The junction's corner angle really is `α`, and the wedge step specialises here -/

/-- **The filler's own corner angle at the junction is `modelAlpha 2 3`.**  From the exact side
lengths `b`, `c`, `a` computed above and the law of cosines (`AngleThreshold.cos_of_sides`): `cos =
(b²+c²−a²)/(2bc) = 70/90 = 7/9`, which is exactly `cos_modelAlpha`'s value at `(e,f) = (2,3)`
(`(2·9−4)/(2·9) = 7/9`).  This is `JunctionWedge.junction_step`'s `hcorner` hypothesis, discharged
from a real coordinate configuration with `e ≥ 2` rather than assumed — the new content of this
file. -/
theorem hcorner_flush_63 :
    cornerAngle ((flushFillerBG63 0).pts 1) ((flushFillerBG63 0).pts 0)
      ((flushFillerBG63 0).pts 2) = modelAlpha 2 3 := by
  obtain ⟨hb, hc, ha⟩ := flushFillerBG63_sides
  have hbpos : (0:ℝ) < b63 := by simp only [b63]; norm_num
  have hcpos : (0:ℝ) < c63 := by simp only [c63]; norm_num
  have hapos : (0:ℝ) < a63 := by simp only [a63]; norm_num
  have hd01 : dist ((flushFillerBG63 0).pts 0) ((flushFillerBG63 0).pts 1) = c63 := by
    have hnn : 0 ≤ dist ((flushFillerBG63 0).pts 0) ((flushFillerBG63 0).pts 1) := dist_nonneg
    nlinarith [hc, hnn, hcpos]
  have hd02 : dist ((flushFillerBG63 0).pts 0) ((flushFillerBG63 0).pts 2) = b63 := by
    have hnn : 0 ≤ dist ((flushFillerBG63 0).pts 0) ((flushFillerBG63 0).pts 2) := dist_nonneg
    nlinarith [hb, hnn, hbpos]
  have hd12 : dist ((flushFillerBG63 0).pts 1) ((flushFillerBG63 0).pts 2) = a63 := by
    have hnn : 0 ≤ dist ((flushFillerBG63 0).pts 1) ((flushFillerBG63 0).pts 2) := dist_nonneg
    nlinarith [ha, hnn, hapos]
  have hd10 : dist ((flushFillerBG63 0).pts 1) ((flushFillerBG63 0).pts 0) = c63 := by
    rw [dist_comm]; exact hd01
  have hd20 : dist ((flushFillerBG63 0).pts 2) ((flushFillerBG63 0).pts 0) = b63 := by
    rw [dist_comm]; exact hd02
  have hcos : Real.cos (cornerAngle ((flushFillerBG63 0).pts 1) ((flushFillerBG63 0).pts 0)
      ((flushFillerBG63 0).pts 2)) = (7:ℝ) / 9 := by
    rw [Erdos634.AngleThreshold.cos_of_sides _ _ _ (by rw [hd10]; exact hcpos.ne')
      (by rw [hd20]; exact hbpos.ne'), hd10, hd20, hd12]
    simp only [a63, b63, c63]; norm_num
  have hcosα : Real.cos (modelAlpha 2 3) = (7:ℝ) / 9 := by
    rw [cos_modelAlpha (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)]; norm_num
  have h1 : cornerAngle ((flushFillerBG63 0).pts 1) ((flushFillerBG63 0).pts 0)
      ((flushFillerBG63 0).pts 2) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have h2 : modelAlpha 2 3 ∈ Set.Icc 0 Real.pi := by
    have hβ := (modelBeta_mem (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3))
    constructor
    · simp only [modelAlpha]; have := Real.pi_pos; nlinarith [hβ.2]
    · simp only [modelAlpha]; have := Real.pi_pos; nlinarith [hβ.1]
  exact Real.injOn_cos h1 h2 (by rw [hcos, hcosα])

/-- `0 < modelAlpha 2 3` and `0 < modelBeta 2 3`: the wedge angles are honest positive reals at
this instance, not free variables. -/
theorem angles_pos_63 : 0 < modelAlpha 2 3 ∧ 0 < modelBeta 2 3 := by
  have hβ := modelBeta_mem (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) < 3)
  refine ⟨?_, hβ.1⟩
  simp only [modelAlpha]; have := Real.pi_pos; linarith [hβ.2]

/-- **`JunctionWedge.junction_step`, specialised to `(e,f) = (2,3)`.**  The `e,f`-general wedge
machinery, instantiated with `α := modelAlpha 2 3`, `β := modelBeta 2 3`, `γ := 2α+β` — real numbers
here, `cos α = 7/9`, `cos β = 23/27` — rather than left abstract.  Combined with `hcorner_flush_63`,
the hypothesis `hcorner` of this theorem is satisfied by the real corner angle of `flushFillerBG63`
at the junction.  What remains free, `hu, hφ, hψ` (the oriented-angle side), is exactly what remains
free in `JunctionWedge.march_junction_real` at `e = 1` too — not a gap introduced here. -/
theorem junction_step_63 (o : Orientation ℝ Plane (Fin 2)) {A P Q u : Plane} {φ ψ : ℝ}
    (hu : u ≠ 0) (hP : P - A ≠ 0) (hQ : Q - A ≠ 0)
    (hφ : (o.oangle u (P - A)).toReal = φ) (hψ : (o.oangle u (Q - A)).toReal = ψ)
    (hφm : φ ∈ Set.Icc (0:ℝ) (modelAlpha 2 3)) (hψm : ψ ∈ Set.Icc (0:ℝ) (modelAlpha 2 3))
    (hcorner : cornerAngle P A Q = modelAlpha 2 3) :
    (φ = 0 ∧ ψ = modelAlpha 2 3) ∨ (φ = modelAlpha 2 3 ∧ ψ = 0) := by
  have hsum := modelAngle_rel 2 3
  have hα := angles_pos_63.1
  have hβ := angles_pos_63.2
  have hopen : Real.pi - ((2 * modelAlpha 2 3 + modelBeta 2 3) + modelBeta 2 3) = modelAlpha 2 3 :=
    Erdos634.JunctionWedge.wedge_opening (modelAlpha 2 3) (modelBeta 2 3)
      (2 * modelAlpha 2 3 + modelBeta 2 3) rfl hsum
  have hstep := Erdos634.JunctionWedge.junction_step o (γ := 2 * modelAlpha 2 3 + modelBeta 2 3)
    rfl hsum hβ hα hu hP hQ hφ hψ (by rw [hopen]; exact hφm) (by rw [hopen]; exact hψm)
    (by rw [hopen]; exact hcorner)
  rwa [hopen] at hstep

/-- **Non-vacuity: `junction_step_63` applies to the real configuration.**  `hcorner` is satisfied by
`flushFillerBG63`'s own junction corner (`hcorner_flush_63`), and `hφm`/`hψm` are satisfied at the
witness `φ = 0, ψ = modelAlpha 2 3` since `0 ≤ modelAlpha 2 3`.  So the hypotheses of
`junction_step_63` that this file can discharge — everything except the `oangle` bookkeeping — are
jointly satisfiable at real numbers coming from an actual tile, not merely abstractly consistent. -/
theorem junction_step_63_nonvacuous :
    cornerAngle ((flushFillerBG63 0).pts 1) ((flushFillerBG63 0).pts 0)
        ((flushFillerBG63 0).pts 2) = modelAlpha 2 3 ∧
    (0:ℝ) ∈ Set.Icc (0:ℝ) (modelAlpha 2 3) ∧ modelAlpha 2 3 ∈ Set.Icc (0:ℝ) (modelAlpha 2 3) :=
  ⟨hcorner_flush_63, ⟨le_refl 0, angles_pos_63.1.le⟩, ⟨angles_pos_63.1.le, le_refl _⟩⟩

/-! ## 6. A local confinement identity -/

/-- **Confinement at a single junction.**  Every vertex of both `a`-tile orientations and both
fillers lies at height `0` or `apexH63`, hence at height `≤ apexH63`.  This is the narrow, honest
analogue of `MarchKills.march_confined` available at this scope: it does *not* extend to slot tiles
or the offset filler (§ intro, "What does not transfer"), only to the basic `a|a` junction built
here. -/
theorem junction_confined_63 (t : ℝ) :
    (∀ k, (aTileBG63 t).pts k 1 ≤ apexH63) ∧
    (∀ k, (aTileGB63 t).pts k 1 ≤ apexH63) ∧
    (∀ k, (flushFillerBG63 t).pts k 1 ≤ apexH63) ∧
    (∀ k, (flushFillerGB63 t).pts k 1 ≤ apexH63) := by
  have h0 : (0:ℝ) ≤ apexH63 := apexH63_pos.le
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;> fin_cases k <;>
    simp only [aTileBG63, aTileGB63, flushFillerBG63, flushFillerGB63, mkTri_pts,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, mkPt_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first | exact h0 | exact le_refl _

/-! ## 7. Axiom audit -/

#print axioms gb_left63
#print axioms bg_left63
#print axioms offsets_complementary63
#print axioms flushFillerBG63_sides
#print axioms flushFillerGB63_sides
#print axioms filler_forced_63
#print axioms wedge_asymmetric_63
#print axioms hcorner_flush_63
#print axioms junction_step_63
#print axioms junction_step_63_nonvacuous
#print axioms junction_confined_63

end Erdos634.ThickJunctionCoords
