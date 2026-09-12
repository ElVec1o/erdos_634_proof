import Erdos634.MarchKills
import Erdos634.TileAt
import Erdos634.CornerBaseEdgesReal
import Erdos634.SideWall
import Erdos634.AngleArithmetic

/-!
# The `c`-slot kills of the layer-1 march at `e = 1`: the fan (K3) and the pockets

Written 2026-09-12.  `MarchKills.lean` left one kill of the layer-1 march unformalised, (K3), the
`c`-slot fan, because the reports recorded only its type (`P4c`) and site.  This file reads the
configuration off the traces and proves what is a theorem about it.

## What the traces say (instrumentation only; every orbit already EXHAUSTED in the sweeps)

Analysers `scratchpad/k3/{fan,term,pocket}.py` on the `CENGINE_TRACE=2 CENGINE_GEN=1` trees of
`uni_f12_b5c8` (rerun 2026-09-12 through `guard_run.sh`, byte-identical to room `data`'s
`tree_f12_b5c8.txt`, 1693 nodes), `uni_f12_b7c4`, `uni_f14_b5c8`, and the 85-orbit ledger.  In
the basis `α ↦ (1,0)`, `β ↦ (0,1)`, `γ ↦ (2,1)`, `π ↦ (3,2)`:

* **Every `P4c` leaf of all 85 orbits has exactly one failing vertex, on the base**; at the
  `c`-slot it is `V`, the far end of the `c`-tile (`(x_c + c, 0)`, letter `cp`), a straight
  boundary point.  **The residual is `(−1, 1) = β − α`** on all 85 orbits (`286/286` leaves of
  `b5c8`; slot counts equal `report_targetA.md`'s `P4c` histogram, e.g. `250, 1050, 340, 275`
  for `(5,8), (5,11), (5,12), (5,13)`); the far-corner `P4c` leaves have the same residual.
  On the five pin orbits (`cp = bp − 1`: `f=12` `(6,5),(7,6)`; `f=14` `(6,5),(7,6),(8,7)`) two
  more residuals occur at the slot, `(−1, 2) = 2β − α` and `(−2, 1) = β − 2α`, each on a `2/18`
  share of the slot's `P4c` leaves.  The residual list is `{β − α, 2β − α, β − 2α}`, the last two
  on the pin family only; every entry has a negative coefficient (`neg_label_not_cone`).
* The nine terminal signatures at the `c`-slot are the same on every orbit checked.  With the
  `c`-tile presenting `α` at `V` (`cSlotTile`, `β` at its left end):
  - after a `BG` `a`-tile (`β` at `V`) the wedge is `γ = 2α + β`; two `α`-fan tiles reduce it to
    `β`; the children are the `α`-tile in either chirality (`P4c`, residual `β − α`) and the
    `β`-tile (`P2`, run `b − a`);
  - after a `GB` `a`-tile (`γ` at `V`) the wedge is `β` at once; same three children;
  - after `BG` and a `β`-tile placed directly, the wedge is `2α` and the `α`-tile pinches a
    pocket (`P1a`).
  With the `c`-tile presenting `β` at `V` (`cSlotTile'`): after `BG` the wedge is `3α`, the fan
  dies by `P2` (`b − a`) at the third `α` or by a pocket (`P1a`) at the second; after `GB` the
  wedge is `α` and the `α`-tile dies by `P2`.
* **The pockets, exactly.**  Two shapes.  (R) At the `β`-end of `cSlotTile'`: the tile riding the
  `c`-tile's `b`-edge from the left base end overruns the apex `A` by `c − b = 1` to a point `C`,
  and `|VC| = a` exactly (because `cos γ = −1/(2f)`); the pocket is the isosceles triangle
  `(a, a, 1)` with area `(1/b)·tile`.  (L) At the `α`-end of `cSlotTile`: the pocket is the
  isosceles triangle `V, A, K` with `|VA| = |VK| = b`, apex angle `α`, `|AK| = b/f`, area
  `(b/c)·tile`; the variant with one more tile has area `(1 + b/c)·tile`.  Both ratios are
  outside `ℕ`.

## What is proved here

1. **The wedges and the residual** (`wedge_L_BG`, …, `residual_L_BG`, `residual_L_GB`): real
   identities from `γ = 2α + β`, `3α + 2β = π`.  The residual is `β − α` in both fan branches.
2. **`β − α` is not a corner sum** (`beta_sub_alpha_not_cone`; the general `neg_label_not_cone`
   and `ledger_residuals_not_cone` cover the pin family's `2β − α`, `β − 2α` too), and **a
   `β`-wedge admits only a `β`-corner** (`beta_wedge_only_beta`): via `Geometry.vertex_multiplicities`
   (irrationality of `α/π`, not re-proved).  The integer forms `pi_point_no_fourth_alpha`,
   `pi_point_gamma_at_most_one_alpha` are the `(X,Y)` arithmetic of the two fan branches.
3. **The model angles at `e = 1`**: `modelAlpha_lt_modelBeta` (`f ≥ 2`) and
   `modelAlpha_irrational` (`f : ℕ`, `f ≥ 2`, through `BaseBetaE1.tile_alpha_irrational` with
   `sin(α/2) = 1/(2f)` derived from `cos_modelAlpha`).  These witness every angle hypothesis
   below (`angle_bundle_nonvacuous_f3`).
4. **The pockets** (`pocketR_*`, `pocketL_*`): the coordinate points `C`, `K`, their exact
   distances, the exact determinants `f·h/(f²−1)` and `(f²−1)·h/f` against the tile's `f·h`, and
   that neither ratio (`1/b`, `b/c`, `1 + b/c`) is a natural number.  This is the arithmetic of
   `P1a` at the `c`-slot; that the pocket *is* a union of tiles in a hypothetical dissection is
   the region-level fact the engine computes and this file does not prove.
5. **The composite** (`c_slot_kill`, `c_slot_kill_gb`, `c_slot_forced_beta`): for a
   `CongruentDissection` of the `e = 1` target whose model has the tile's side lengths and
   angles, if the `c`-tile `cSlotTile x f` and the `BG` tile `aTileBG (x + f²) f` are tiles of
   `D` and two further tiles present `α` at `V` (the fan), then **no tile of `D` presents `α`
   at `V`** beyond those — the `P4c` candidates of both chiralities are not tiles of any
   dissection extending the configuration — and **exactly one further tile presents `β`**
   there (the `P2` branch, whose kill `b − a` is (K2) of `MarchKills`, arithmetic existing but
   not realised at edge level here).  The `GB` variant is `c_slot_kill_gb`.  Local angles of the
   coordinate tiles are read off their opposite sides (`localAngle_of_oppSide`), the straight
   boundary point is `base_point_mem_frontier`, and the vertex-figure trichotomy is
   `TileAt.congruentDissection_boundary_figure_cases`.

## Novelty ledger (`code/novelty_check.sh`, 2026-09-12)

"β − α", "β-wedge", "four α", "fourth alpha": no corpus match.  Related, pre-existing and cited
rather than re-proved: `OrderForcing` (`π − β − α` has exactly the two figures `{γ}`, `{2α, β}` —
the wedge `wedge_L_BG`), `LadderInvariant.flush_overrun_mem` (the `b/c`-parameter point of a
`c`-edge and the overrun `c − b = 1`, which is `overrun_on_ray` in the pocket's coordinates),
`ApexRigidity.middle_fraction` (a `b/c` area fraction, in the apex configuration, not this one).
The pockets' shapes `(a, a, 1)` and `(b, b, b/f)` and their areas `tile/b`, `(b/c)·tile` are new.

## What is not proved (R_c, stated exactly)

`c_slot_kill` is conditional on **R_c**: that `D` contains `cSlotTile x f` on `[x, x + f²]`,
`aTileBG (x + f²) f` on the next `a`-letter, and two tiles with corner angle `α` at `V` — i.e.
that a hypothetical tiling's base layer is the march up to and into the `c`-slot, with the
`c`-tile in the `β`-left reflection and the fan begun.  That is `rem:marchobl` (i)–(iii) plus
the reflection choice, and is not proved.  The `cSlotTile'` reflection's kills are `P2` and the
pocket, whose region-level content is not assembled.  Nothing here decides the crossing question.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.MarchKillsFan

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchCoords Erdos634.BaseBetaTargetCoord
  Erdos634.MarchKills Erdos634.TilePlacement

/-! ## 1. The wedges at `V` and the residual -/

/-- `c`-tile `α`, `BG` tile `β` at `V`: the wedge is `γ`. -/
theorem wedge_L_BG {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi) :
    Real.pi - (α + β) = γ := by rw [hγ, ← hrel]; ring

/-- `c`-tile `α`, `GB` tile `γ` at `V`: the wedge is `β`. -/
theorem wedge_L_GB {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi) :
    Real.pi - (α + γ) = β := by rw [hγ, ← hrel]; ring

/-- `c`-tile `β`, `BG` tile `β` at `V`: the wedge is `3α`. -/
theorem wedge_R_BG {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) :
    Real.pi - (β + β) = 3 * α := by rw [← hrel]; ring

/-- `c`-tile `β`, `GB` tile `γ` at `V`: the wedge is `α`. -/
theorem wedge_R_GB {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi) :
    Real.pi - (β + γ) = α := by rw [hγ, ← hrel]; ring

/-- **The residual of the `BG` fan.**  `c`-tile `α`, `BG` tile `β`, two fan tiles `α`, and the
`P4c` candidate `α`: `π − (4α + β) = β − α`. -/
theorem residual_L_BG {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) :
    Real.pi - (α + β + α + α) - α = β - α := by rw [← hrel]; ring

/-- **The residual of the `GB` fan.**  `c`-tile `α`, `GB` tile `γ`, and the `P4c` candidate `α`:
`π − (α + γ) − α = β − α`. -/
theorem residual_L_GB {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi) :
    Real.pi - (α + γ) - α = β - α := by rw [hγ, ← hrel]; ring

/-- The two fans leave the same residual: after two fan tiles the `BG` wedge `γ` is the `GB`
wedge `β`. -/
theorem fans_agree {α β γ : ℝ} (hγ : γ = 2 * α + β) : γ - (α + α) = β := by rw [hγ]; ring

/-! ## 2. `β − α` is not a corner sum -/

/-- **`β − α` is not `Xα + Yβ` with `X, Y ∈ ℕ`.**  A representation would be a vertex figure
`(X, Y, 0)` of label `(−1, 1)`; `Dissection.vertex_multiplicities` (which carries the
irrationality of `α/π`) forces `X = −1`. -/
theorem beta_sub_alpha_not_cone {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (X Y : ℕ) :
    (X : ℝ) * α + (Y : ℝ) * β ≠ β - α := by
  intro h
  have hsum : (X : ℝ) * α + (Y : ℝ) * β + ((0 : ℕ) : ℝ) * (2 * α + β)
      = ((-1 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β := by push_cast; linarith
  obtain ⟨h1, _⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr X Y 0 (-1) 1 hsum
  omega

/-- **Any label with a negative coefficient is not a corner sum** — the general form covering all
three residuals of the ledger, `(−1,1)`, `(−1,2)`, `(−2,1)`: a vertex figure `(X, Y, Z)` summing to
`sα + tβ` has `X + 2Z = s` and `Y + Z = t`, so `s, t ≥ 0`. -/
theorem neg_label_not_cone {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (s t : ℤ) (hst : s < 0 ∨ t < 0) (X Y Z : ℕ) :
    (X : ℝ) * α + (Y : ℝ) * β + (Z : ℝ) * (2 * α + β) ≠ (s : ℝ) * α + (t : ℝ) * β := by
  intro h
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr X Y Z s t h
  omega

/-- The three residuals of the ledger, as instances: `β − α`, `2β − α`, `β − 2α`. -/
theorem ledger_residuals_not_cone {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (X Y Z : ℕ) :
    (X : ℝ) * α + (Y : ℝ) * β + (Z : ℝ) * (2 * α + β) ≠ β - α ∧
    (X : ℝ) * α + (Y : ℝ) * β + (Z : ℝ) * (2 * α + β) ≠ 2 * β - α ∧
    (X : ℝ) * α + (Y : ℝ) * β + (Z : ℝ) * (2 * α + β) ≠ β - 2 * α := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact neg_label_not_cone hrel hirr (-1) 1 (Or.inl (by norm_num)) X Y Z (by push_cast; linarith)
  · exact neg_label_not_cone hrel hirr (-1) 2 (Or.inl (by norm_num)) X Y Z (by push_cast; linarith)
  · exact neg_label_not_cone hrel hirr (-2) 1 (Or.inl (by norm_num)) X Y Z (by push_cast; linarith)

/-- **A `β`-wedge admits exactly one `β`-corner.**  Any vertex figure `(X, Y, Z)` summing to `β`
is `(0, 1, 0)` — so the first `α` placed into the residual `β` wedge is already dead.  This is
`AngleArithmetic.beta_corner_forced` fed by `vertex_multiplicities`. -/
theorem beta_wedge_only_beta {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (X Y Z : ℕ)
    (h : (X : ℝ) * α + (Y : ℝ) * β + (Z : ℝ) * (2 * α + β) = β) :
    X = 0 ∧ Y = 1 ∧ Z = 0 := by
  have hsum : (X : ℝ) * α + (Y : ℝ) * β + (Z : ℝ) * (2 * α + β)
      = ((0 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β := by push_cast; linarith
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr X Y Z 0 1 hsum
  omega

/-- **Integer form of the `BG` fan kill.**  At a straight point (`na + 2nγ = 3`, `nβ + nγ = 2`)
there are at most three `α`-corners: the `c`-tile, the two fan tiles and the candidate are four. -/
theorem pi_point_no_fourth_alpha (na nb ng : ℕ) (hx : na + 2 * ng = 3) (hy : nb + ng = 2) :
    na ≤ 3 := by omega

/-- **Integer form of the `GB` fan kill.**  A straight point carrying a `γ` carries at most one
`α`: the `c`-tile's `α` and the candidate's `α` are two. -/
theorem pi_point_gamma_at_most_one_alpha (na nb ng : ℕ) (hx : na + 2 * ng = 3)
    (hy : nb + ng = 2) (hg : 1 ≤ ng) : na ≤ 1 := by omega

/-! ## 3. The model angles at `e = 1`: order and irrationality -/

theorem modelAlpha_pos {f : ℝ} (hf : 1 < f) : 0 < modelAlpha 1 f := by
  have := (modelBeta_mem one_pos hf).2
  unfold modelAlpha; linarith

theorem modelAlpha_lt_pi_div_three {f : ℝ} (hf : 1 < f) : modelAlpha 1 f < Real.pi / 3 := by
  have := (modelBeta_mem one_pos hf).1
  unfold modelAlpha; linarith

/-- **`α < β` at `e = 1` for `f ≥ 2`.**  `cos α = 1 − 1/(2f²) > (3f² − 1)/(2f³) = cos β`, since
`2f³ − 3f² − f + 1 = (f − 2)(2f² + f + 1) + 3 > 0`; `cos` is strictly decreasing on `[0, π]`. -/
theorem modelAlpha_lt_modelBeta {f : ℝ} (hf : 2 ≤ f) : modelAlpha 1 f < modelBeta 1 f := by
  have hf1 : 1 < f := by linarith
  have hβ := modelBeta_mem one_pos hf1
  have hα0 := modelAlpha_pos hf1
  have hαπ := modelAlpha_lt_pi_div_three hf1
  have hpi := Real.pi_pos
  have hcosα := cos_modelAlpha (e := 1) (f := f) one_pos hf1
  have hcosβ := cos_modelBeta (e := 1) (f := f) one_pos hf1
  have hf0 : (0 : ℝ) < f := by linarith
  have hlt : Real.cos (modelBeta 1 f) < Real.cos (modelAlpha 1 f) := by
    rw [hcosα, hcosβ, baseLen_one]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f - 2) (by positivity : (0:ℝ) ≤ 2 * f ^ 2 + f + 1),
      pow_pos hf0 2, pow_pos hf0 3]
  by_contra hle
  have hle' : modelBeta 1 f ≤ modelAlpha 1 f := not_lt.mp hle
  have := Real.cos_le_cos_of_nonneg_of_le_pi hβ.1.le (by linarith) hle'
  linarith

/-- `sin(α/2) = 1/(2f)` at `e = 1`, from `cos α = 1 − 1/(2f²)` and `sin² (α/2) = (1 − cos α)/2`. -/
theorem sin_half_modelAlpha {f : ℝ} (hf : 1 < f) :
    Real.sin (modelAlpha 1 f / 2) = 1 / (2 * f) := by
  have hf0 : (0 : ℝ) < f := by linarith
  have hα0 := modelAlpha_pos hf
  have hαπ := modelAlpha_lt_pi_div_three hf
  have hpi := Real.pi_pos
  have hsq : Real.sin (modelAlpha 1 f / 2) ^ 2 = (1 / (2 * f)) ^ 2 := by
    rw [Real.sin_sq_eq_half_sub, show 2 * (modelAlpha 1 f / 2) = modelAlpha 1 f by ring,
      cos_modelAlpha one_pos hf]
    field_simp; ring
  have hnn : 0 ≤ Real.sin (modelAlpha 1 f / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  exact (sq_eq_sq₀ hnn (by positivity)).mp hsq

/-- **`α/π` is irrational at `e = 1` for every natural `f ≥ 2`** — `BaseBetaE1.tile_alpha_irrational`
at the model's own `α`. -/
theorem modelAlpha_irrational (f : ℕ) (hf : 2 ≤ f) :
    ¬ ∃ r : ℚ, modelAlpha 1 (f : ℝ) = (r : ℝ) * Real.pi := by
  have hf1 : (1 : ℝ) < f := by exact_mod_cast (by omega : 1 < f)
  refine Erdos634.BaseBetaE1.tile_alpha_irrational 1 f le_rfl (by omega) _ ?_
  rw [sin_half_modelAlpha hf1]; push_cast; ring

/-- **Non-vacuity of the angle bundle**, at `f = 3` (tile `(3, 8, 9)`): the model angles satisfy
every hypothesis the theorems below carry. -/
theorem angle_bundle_nonvacuous_f3 :
    ∃ α β γ : ℝ, γ = 2 * α + β ∧ 3 * α + 2 * β = Real.pi ∧
      (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ 0 < α ∧ α < β := by
  refine ⟨modelAlpha 1 3, modelBeta 1 3, 2 * modelAlpha 1 3 + modelBeta 1 3, rfl,
    modelAngle_rel 1 3, ?_, modelAlpha_pos (by norm_num), modelAlpha_lt_modelBeta (by norm_num)⟩
  have h := modelAlpha_irrational 3 (by norm_num)
  rw [show ((3 : ℕ) : ℝ) = 3 by norm_num] at h
  exact h

/-! ## 4. The pockets -/

/-- Twice the tile's area as the coordinate determinant: `f · h`. -/
theorem tile_det {f : ℝ} (hf : 1 < f) (x : ℝ) :
    det3 x 0 (x + f ^ 2) 0 (x + dBG f / f) (1 / f * apexH f) = f * apexH f := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  unfold det3; field_simp; ring

/-! ### (R) The overrun pocket at the `β`-end of `cSlotTile'`

`B = (x, 0)`, `V = (x + f², 0)`, apex `A = (x + f² − dBG/f, h/f)`.  The tile riding the `b`-edge
`BA` with its `c`-edge overruns `A` by `c − b = 1`, to `C = B + (c/b)(A − B) = (x + f² − 1/2,
f·h/(f² − 1))`. -/

/-- The overrun point `C`, in coordinates. -/
noncomputable def overrunX (x f : ℝ) : ℝ := x + f ^ 2 - 1 / 2
noncomputable def overrunY (f : ℝ) : ℝ := f / (f ^ 2 - 1) * apexH f

/-- `C = B + (c/b)·(A − B)`: the point at distance `c` along the `b`-edge ray. -/
theorem overrun_on_ray {f : ℝ} (hf : 1 < f) (x : ℝ) :
    overrunX x f = x + f ^ 2 / (f ^ 2 - 1) * (f ^ 2 - dBG f / f) ∧
    overrunY f = f ^ 2 / (f ^ 2 - 1) * (1 / f * apexH f) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  constructor
  · unfold overrunX dBG; field_simp; ring
  · unfold overrunY; field_simp

/-- **`|AC| = 1`**: the overrun is exactly `c − b`. -/
theorem pocketR_AC {f : ℝ} (hf : 1 < f) (x : ℝ) :
    dist (mkPt (x + f ^ 2 - dBG f / f) (1 / f * apexH f)) (mkPt (overrunX x f) (overrunY f)) ^ 2
      = 1 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  unfold overrunX overrunY
  rw [dist_sq_kapex_kapex hf]; unfold h2 dBG; field_simp; ring

/-- **`|VC| = a`**: the pocket is isosceles.  This is `cos γ = −1/(2f)`: `a² + 1 + 2a·(1/(2f)) …`
collapses to `a²` at `e = 1`. -/
theorem pocketR_VC {f : ℝ} (hf : 1 < f) (x : ℝ) :
    dist (mkPt (x + f ^ 2) 0) (mkPt (overrunX x f) (overrunY f)) ^ 2 = f ^ 2 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  unfold overrunX overrunY
  rw [dist_sq_zero_kapex hf]; unfold h2; field_simp; ring

/-- **`|VA| = a`**: the `c`-tile's edge at its `β`-end (`cSlotTile_sides`). -/
theorem pocketR_VA {f : ℝ} (hf : 1 < f) (x : ℝ) :
    dist (mkPt (x + f ^ 2) 0) (mkPt (x + f ^ 2 - dBG f / f) (1 / f * apexH f)) ^ 2 = f ^ 2 :=
  (cSlotTile_sides x f hf).2.1

/-- **Twice the pocket's area is `f·h/(f² − 1)`**: the tile's `f·h` over `b`. -/
theorem pocketR_det {f : ℝ} (hf : 1 < f) (x : ℝ) :
    det3 (x + f ^ 2) 0 (x + f ^ 2 - dBG f / f) (1 / f * apexH f) (overrunX x f) (overrunY f)
      = -(f * apexH f / (f ^ 2 - 1)) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  unfold det3 overrunX overrunY dBG; field_simp; ring

/-- The pocket is a nondegenerate triangle (so it exists as a coordinate triangle). -/
theorem pocketR_det_ne {f : ℝ} (hf : 1 < f) (x : ℝ) :
    det3 (x + f ^ 2) 0 (x + f ^ 2 - dBG f / f) (1 / f * apexH f) (overrunX x f) (overrunY f)
      ≠ 0 := by
  rw [pocketR_det hf]
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have := div_pos (mul_pos (by linarith) (apexH_pos hf)) hb
  linarith

/-- The pocket `V A C` as a triangle. -/
noncomputable def pocketR (x f : ℝ) (hf : 1 < f) : Tri :=
  mkTri (x + f ^ 2) 0 (x + f ^ 2 - dBG f / f) (1 / f * apexH f) (overrunX x f) (overrunY f)
    (pocketR_det_ne hf x)

/-- **The pocket is not a union of tiles, by area**: `k · (f·h) = f·h/(f² − 1)` has no solution
`k ∈ ℕ` once `f ≥ 2` (`k(f² − 1) = 1` with `f² − 1 ≥ 3`). -/
theorem pocketR_not_tile_multiple {f : ℝ} (hf : 2 ≤ f) (k : ℕ) :
    (k : ℝ) * (f * apexH f) ≠ f * apexH f / (f ^ 2 - 1) := by
  intro h
  have hf1 : 1 < f := by linarith
  have hpos : 0 < f * apexH f := mul_pos (by linarith) (apexH_pos hf1)
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have h2 : ((k : ℝ) * (f ^ 2 - 1) - 1) * (f * apexH f) = 0 := by
    have h' := h
    rw [eq_div_iff hb.ne'] at h'
    linear_combination h'
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; norm_num at h3
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      nlinarith
  · exact absurd h3 hpos.ne'

/-! ### (L) The `α`-wedge pocket at the `α`-end of `cSlotTile`

`B = (x, 0)`, apex `A = (x + dBG/f, h/f)` (`β` at `B`, so `BA` is the `a`-edge), `V = (x + f², 0)`.
The pocket's third vertex `K = B + ((2f² − 1)/f²)(A − B)` lies on the ray `BA` at distance
`a + b/f`; the pocket `V A K` has `|VA| = |VK| = b`, `|AK| = b/f`, apex angle `α` at `V`. -/

noncomputable def pocketLX (x f : ℝ) : ℝ := x + (2 * f ^ 2 - 1) / f ^ 2 * (dBG f / f)
noncomputable def pocketLY (f : ℝ) : ℝ := (2 * f ^ 2 - 1) / f ^ 3 * apexH f

/-- **`|VK| = b`.** -/
theorem pocketL_VK {f : ℝ} (hf : 1 < f) (x : ℝ) :
    dist (mkPt (x + f ^ 2) 0) (mkPt (pocketLX x f) (pocketLY f)) ^ 2 = (f ^ 2 - 1) ^ 2 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  unfold pocketLX pocketLY
  rw [dist_sq_zero_kapex hf]; unfold h2 dBG; field_simp; ring

/-- **`|VA| = b`**: the `c`-tile's edge at its `α`-end (`cSlotTile_sides`). -/
theorem pocketL_VA {f : ℝ} (hf : 1 < f) (x : ℝ) :
    dist (mkPt (x + f ^ 2) 0) (mkPt (x + dBG f / f) (1 / f * apexH f)) ^ 2 = (f ^ 2 - 1) ^ 2 :=
  (cSlotTile_sides x f hf).1.2

/-- **`|AK| = b/f`.** -/
theorem pocketL_AK {f : ℝ} (hf : 1 < f) (x : ℝ) :
    dist (mkPt (x + dBG f / f) (1 / f * apexH f)) (mkPt (pocketLX x f) (pocketLY f)) ^ 2
      = ((f ^ 2 - 1) / f) ^ 2 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  unfold pocketLX pocketLY
  rw [dist_sq_kapex_kapex hf]; unfold h2 dBG; field_simp; ring

/-- **Twice the pocket's area is `(f² − 1)·h/f`**: the tile's `f·h` times `b/c`. -/
theorem pocketL_det {f : ℝ} (hf : 1 < f) (x : ℝ) :
    det3 (x + f ^ 2) 0 (x + dBG f / f) (1 / f * apexH f) (pocketLX x f) (pocketLY f)
      = -((f ^ 2 - 1) * apexH f / f) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  unfold det3 pocketLX pocketLY dBG; field_simp; ring

theorem pocketL_det_ne {f : ℝ} (hf : 1 < f) (x : ℝ) :
    det3 (x + f ^ 2) 0 (x + dBG f / f) (1 / f * apexH f) (pocketLX x f) (pocketLY f) ≠ 0 := by
  rw [pocketL_det hf]
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have := div_pos (mul_pos hb (apexH_pos hf)) (by linarith : (0:ℝ) < f)
  linarith

noncomputable def pocketL (x f : ℝ) (hf : 1 < f) : Tri :=
  mkTri (x + f ^ 2) 0 (x + dBG f / f) (1 / f * apexH f) (pocketLX x f) (pocketLY f)
    (pocketL_det_ne hf x)

/-- **`b/c` and `1 + b/c` are not natural numbers**: `k·f² = f² − 1` and `k·f² = 2f² − 1` have no
solution `k ∈ ℕ` for `f ≥ 2`. -/
theorem pocketL_not_tile_multiple {f : ℝ} (hf : 2 ≤ f) (k : ℕ) :
    (k : ℝ) * (f * apexH f) ≠ (f ^ 2 - 1) * apexH f / f ∧
    (k : ℝ) * (f * apexH f) ≠ (2 * f ^ 2 - 1) * apexH f / f := by
  have hf1 : 1 < f := by linarith
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hpos := apexH_pos hf1
  constructor
  · intro h
    have h2 : ((k : ℝ) * f ^ 2 - (f ^ 2 - 1)) * apexH f = 0 := by
      have h' := h
      rw [eq_div_iff hf0] at h'
      linear_combination h'
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; norm_num at h3; nlinarith
      · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
        nlinarith
    · exact absurd h3 hpos.ne'
  · intro h
    have h2 : ((k : ℝ) * f ^ 2 - (2 * f ^ 2 - 1)) * apexH f = 0 := by
      have h' := h
      rw [eq_div_iff hf0] at h'
      linear_combination h'
    rcases mul_eq_zero.mp h2 with h3 | h3
    · by_cases hk1 : k ≤ 1
      · have : (k : ℝ) ≤ 1 := by exact_mod_cast hk1
        nlinarith
      · have : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
        nlinarith
    · exact absurd h3 hpos.ne'

/-- **The pockets at `f = 3`, in numbers.**  Tile `(3, 8, 9)`; the (R) pocket has area `1/8` of
the tile, the (L) pocket `8/9`: `f·h/(f²−1) = 3h/8`, `(f²−1)h/f = 8h/3`. -/
theorem pockets_f3 :
    (3 : ℝ) * apexH 3 / (3 ^ 2 - 1) = 3 / 8 * apexH 3 ∧
    ((3 : ℝ) ^ 2 - 1) * apexH 3 / 3 = 8 / 3 * apexH 3 ∧
    overrunX 0 3 = 17 / 2 ∧ pocketLX 0 3 = 221 / 81 := by
  refine ⟨by ring, by ring, ?_, ?_⟩
  · unfold overrunX; norm_num
  · unfold pocketLX dBG; norm_num

/-! ## 5. The composite: the `c`-slot fan in a real congruent dissection -/

/-- **A coordinate tile's local angle at one of its vertices, read off the opposite side.**  With
the model's opposite sides `f, f² − 1, f²` (pairwise distinct for `f ≥ 2`) and its corner angles
`α, β, γ`, a tile of `D` whose corner at `pts j` faces a side of length `f` (resp. `f² − 1`,
`f²`) has local angle `α` (resp. `β`, `γ`) there. -/
theorem localAngle_of_oppSide {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hs0 : sideOpp D.model 0 = f) (hs1 : sideOpp D.model 1 = f ^ 2 - 1)
    (hs2 : sideOpp D.model 2 = f ^ 2)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (i : Fin N) (j : Fin 3) :
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = f →
      (D.tile i).localAngle ((D.tile i).pts j) = α) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = f ^ 2 - 1 →
      (D.tile i).localAngle ((D.tile i).pts j) = β) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = f ^ 2 →
      (D.tile i).localAngle ((D.tile i).pts j) = γ) := by
  rw [Tri.localAngle_vertex]
  obtain ⟨k, hk, hd⟩ :=
    Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent i).symm j
  rw [hk]
  simp only [sideOpp] at hs0 hs1 hs2
  have h1 : f ≠ f ^ 2 - 1 := by nlinarith
  have h2 : f ≠ f ^ 2 := by nlinarith
  have h3 : f ^ 2 - 1 ≠ f ^ 2 := by linarith
  fin_cases k <;> simp at hd hs0 hs1 hs2 ⊢
  · refine ⟨fun _ => hα', fun h => ?_, fun h => ?_⟩
    · exact absurd (hs0.symm.trans (hd.trans h)) h1
    · exact absurd (hs0.symm.trans (hd.trans h)) h2
  · refine ⟨fun h => ?_, fun _ => hβ', fun h => ?_⟩
    · exact absurd (hs1.symm.trans (hd.trans h)) h1.symm
    · exact absurd (hs1.symm.trans (hd.trans h)) h3
  · refine ⟨fun h => ?_, fun h => ?_, fun _ => hγ'⟩
    · exact absurd (hs2.symm.trans (hd.trans h)) h2.symm
    · exact absurd (hs2.symm.trans (hd.trans h)) h3.symm

theorem dist_eq_of_sq_eq {d s : ℝ} (hd : d ^ 2 = s ^ 2) (h0 : 0 ≤ d) (hs : 0 ≤ s) : d = s :=
  (sq_eq_sq₀ h0 hs).mp hd

/-- The bundle of hypotheses on the model, packaged. -/
structure ModelData {N : ℕ} (D : CongruentDissection N) (f α β γ : ℝ) : Prop where
  hs0 : sideOpp D.model 0 = f
  hs1 : sideOpp D.model 1 = f ^ 2 - 1
  hs2 : sideOpp D.model 2 = f ^ 2
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ

/-- **The `c`-tile (`β` at its left end) presents `α` at `V`.** -/
theorem cSlotTile_localAngle_V {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {x : ℝ} (hi : D.tile i = cSlotTile x f (by linarith)) :
    (D.tile i).localAngle (mkPt (x + f ^ 2) 0) = α := by
  have hf1 : 1 < f := by linarith
  have hV : mkPt (x + f ^ 2) 0 = (D.tile i).pts 1 := by rw [hi]; rfl
  rw [hV]
  refine (localAngle_of_oppSide D hf hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' i 1).1 ?_
  rw [hi]
  show dist ((cSlotTile x f hf1).pts 2) ((cSlotTile x f hf1).pts 0) = f
  rw [dist_comm]
  exact dist_eq_of_sq_eq (cSlotTile_sides x f hf1).1.1 dist_nonneg (by linarith)

/-- **The `BG` `a`-tile presents `β` at its left base corner.** -/
theorem aTileBG_localAngle_left {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {j : Fin N} {t : ℝ} (hj : D.tile j = aTileBG t f (by linarith)) :
    (D.tile j).localAngle (mkPt t 0) = β := by
  have hf1 : 1 < f := by linarith
  have hV : mkPt t 0 = (D.tile j).pts 1 := by rw [hj]; rfl
  rw [hV]
  refine (localAngle_of_oppSide D hf hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' j 1).2.1 ?_
  rw [hj]
  show dist (mkPt (t + dBG f) (apexH f)) (mkPt (t + f) 0) = f ^ 2 - 1
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by nlinarith)
  rw [dist_comm, dist_sq_zero_apex hf1]
  have := bg_right f (by linarith : (0:ℝ) < f).ne'
  rw [← this]; ring

/-- **The `GB` `a`-tile presents `γ` at its left base corner.** -/
theorem aTileGB_localAngle_left {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {j : Fin N} {t : ℝ} (hj : D.tile j = aTileGB t f (by linarith)) :
    (D.tile j).localAngle (mkPt t 0) = γ := by
  have hf1 : 1 < f := by linarith
  have hV : mkPt t 0 = (D.tile j).pts 0 := by rw [hj]; rfl
  rw [hV]
  refine (localAngle_of_oppSide D hf hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' j 0).2.2 ?_
  rw [hj]
  show dist (mkPt (t + f) 0) (mkPt (t + dGB f) (apexH f)) = f ^ 2
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
  rw [dist_sq_zero_apex hf1]
  have := gb_right f (by linarith : (0:ℝ) < f).ne'
  rw [← this]; ring

/-- **The flush filler presents `α` at the junction.** -/
theorem flushFiller_localAngle {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {k : Fin N} {t : ℝ}
    (hk : D.tile k = flushFiller t f (by linarith)) :
    (D.tile k).localAngle (mkPt (t + f) 0) = α := by
  have hf1 : 1 < f := by linarith
  have hV : mkPt (t + f) 0 = (D.tile k).pts 0 := by rw [hk]; rfl
  rw [hV]
  refine (localAngle_of_oppSide D hf hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' k 0).1 ?_
  rw [hk]
  show dist (mkPt (t + f + dBG f) (apexH f)) (mkPt (t + dBG f) (apexH f)) = f
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by linarith)
  rw [show apexH f = 1 * apexH f by ring, dist_sq_kapex_kapex hf1]; ring

/-- **The offset filler presents `α` at the junction.** -/
theorem offsetFiller_localAngle {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {k : Fin N} {t : ℝ}
    (hk : D.tile k = offsetFiller t f (by linarith)) :
    (D.tile k).localAngle (mkPt (t + f) 0) = α := by
  have hf1 : 1 < f := by linarith
  have hV : mkPt (t + f) 0 = (D.tile k).pts 0 := by rw [hk]; rfl
  rw [hV]
  refine (localAngle_of_oppSide D hf hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' k 0).1 ?_
  rw [hk]
  exact dist_eq_of_sq_eq (offsetFiller_sides t f hf1).2.2 dist_nonneg (by linarith)

/-! ### The straight boundary point `V` -/

/-- **A base point is a frontier point of the target**: it lies on edge `0`, the base. -/
theorem base_point_mem_frontier {f : ℝ} (hf : 1 < f) {v : ℝ} (h0 : 0 ≤ v)
    (hL : v ≤ baseLen 1 f) :
    mkPt v 0 ∈ frontier (baseBetaTarget 1 f one_pos hf).carrier := by
  apply Erdos634.SideWall.edge_subset_frontier _ 0
  have hLpos := baseLen_pos one_pos hf
  show mkPt v 0 ∈ segment ℝ (mkPt 0 0) (mkPt (baseLen 1 f) 0)
  refine ⟨1 - v / baseLen 1 f, v / baseLen 1 f, ?_, by positivity, by ring, ?_⟩
  · rw [sub_nonneg, div_le_one hLpos]; exact hL
  · ext k
    fin_cases k
    · simp [mkPt_zero]
      first | done | field_simp
    · simp [mkPt_one]

/-- **An interior base point is not a target vertex.** -/
theorem base_point_not_vertex {f : ℝ} (hf : 1 < f) {v : ℝ} (h0 : 0 < v)
    (hL : v < baseLen 1 f) :
    mkPt v 0 ∉ Set.range (baseBetaTarget 1 f one_pos hf).pts := by
  rintro ⟨k, hk⟩
  have hH := height_pos one_pos hf
  fin_cases k
  · have := congrArg (fun p : Plane => p 0) hk
    simp [mkPt_zero] at this; linarith
  · have := congrArg (fun p : Plane => p 0) hk
    simp [mkPt_zero] at this; linarith
  · have := congrArg (fun p : Plane => p 1) hk
    simp [mkPt_one] at this; linarith

/-! ### The abstract kills at a straight boundary point -/

/-- **Order-free form.**  The ten distinctness facts the trichotomy consumes, from *positivity of
both angles and their distinctness* — `0 < α`, `0 < β`, `α ≠ β` — together with `γ = 2α + β` and
`3α + 2β = π`.  No comparison between `α` and `β` is used anywhere.

This matters beyond `e = 1`: at the thick member `(e, f) = (2, 3)` the tile angle order is
**reversed** (`cos α = 21/27`, `cos β = 23/27`, so `β < α`), and every consumer of the trichotomy
below therefore needed re-checking.  The check is discharged here once and for all: the order was
only ever a convenient way to produce `α ≠ β` and the positivity of `β`. -/
theorem distinct_of_pos_ne {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≠ β)
    (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi) :
    α ≠ β ∧ α ≠ γ ∧ α ≠ Real.pi ∧ α ≠ 0 ∧ β ≠ γ ∧ β ≠ Real.pi ∧ β ≠ 0 ∧ γ ≠ Real.pi ∧ γ ≠ 0 ∧
      Real.pi ≠ 0 := by
  subst hγ
  refine ⟨hαβ, ?_, ?_, hα.ne', ?_, ?_, hβ.ne', ?_, ?_, Real.pi_pos.ne'⟩ <;> nlinarith

/-- Legacy order-carrying form, kept for callers that still hold `α < β`.  A one-line corollary of
the order-free `distinct_of_pos_ne`: the order contributes nothing but `0 < β` and `α ≠ β`. -/
theorem distinct_of_order {α β γ : ℝ} (hα : 0 < α) (hαβ : α < β) (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) :
    α ≠ β ∧ α ≠ γ ∧ α ≠ Real.pi ∧ α ≠ 0 ∧ β ≠ γ ∧ β ≠ Real.pi ∧ β ≠ 0 ∧ γ ≠ Real.pi ∧ γ ≠ 0 ∧
      Real.pi ≠ 0 :=
  distinct_of_pos_ne hα (hα.trans hαβ) hαβ.ne hγ hrel

/-- **No straight boundary point of a congruent dissection carries four `α`-corners.**  The
trichotomy `{π}`, `{3α, 2β}`, `{α, β, γ}` allows at most three. -/
theorem straight_point_no_fourth_alpha {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    {i k₁ k₂ l : Fin N} (h12 : i ≠ k₁) (h13 : i ≠ k₂) (h14 : i ≠ l) (h23 : k₁ ≠ k₂)
    (h24 : k₁ ≠ l) (h34 : k₂ ≠ l)
    (hi : (D.tile i).localAngle v = α) (hk₁ : (D.tile k₁).localAngle v = α)
    (hk₂ : (D.tile k₂).localAngle v = α) (hl : (D.tile l).localAngle v = α) : False := by
  classical
  obtain ⟨hαβ', hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ := distinct_of_pos_ne hα hβpos hαβ hγdef hrel
  have hsub : ({i, k₁, k₂, l} : Finset (Fin N)) ⊆ ({m | (D.tile m).localAngle v = α} : Finset (Fin N)) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hm with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({i, k₁, k₂, l} : Finset (Fin N)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h34]
    · simp [h23, h24]
    · simp [h12, h13, h14]
  have h4 := Finset.card_le_card hsub
  rw [hcard] at h4
  rcases Erdos634.Geometry.Dissection.congruentDissection_boundary_figure_cases D α β γ hαβ' hαγ
      hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' hv hnv with
    ⟨_, hA, _, _⟩ | ⟨hA, _, _⟩ | ⟨hA, _, _⟩ <;> omega

/-- **A straight boundary point carrying a `γ`-corner carries no second `α`-corner.** -/
theorem straight_point_gamma_no_second_alpha {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    {i j l : Fin N} (hil : i ≠ l)
    (hi : (D.tile i).localAngle v = α) (hj : (D.tile j).localAngle v = γ)
    (hl : (D.tile l).localAngle v = α) : False := by
  classical
  obtain ⟨hαβ', hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ := distinct_of_pos_ne hα hβpos hαβ hγdef hrel
  have hsubα : ({i, l} : Finset (Fin N)) ⊆ ({m | (D.tile m).localAngle v = α} : Finset (Fin N)) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hm with rfl | rfl <;> assumption
  have hsubγ : ({j} : Finset (Fin N)) ⊆ ({m | (D.tile m).localAngle v = γ} : Finset (Fin N)) := by
    intro m hm
    simp only [Finset.mem_singleton] at hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    subst hm; exact hj
  have h2 := Finset.card_le_card hsubα
  rw [Finset.card_pair hil] at h2
  have h1 := Finset.card_le_card hsubγ
  rw [Finset.card_singleton] at h1
  rcases Erdos634.Geometry.Dissection.congruentDissection_boundary_figure_cases D α β γ hαβ' hαγ
      hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' hv hnv with
    ⟨_, hA, _, hG⟩ | ⟨hA, _, hG⟩ | ⟨hA, _, hG⟩ <;> omega

/-- **A straight boundary point with three `α`-corners carries exactly two `β`-corners.** -/
theorem straight_point_three_alpha_two_beta {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ}
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    {i k₁ k₂ : Fin N} (h12 : i ≠ k₁) (h13 : i ≠ k₂) (h23 : k₁ ≠ k₂)
    (hi : (D.tile i).localAngle v = α) (hk₁ : (D.tile k₁).localAngle v = α)
    (hk₂ : (D.tile k₂).localAngle v = α) :
    ({m | (D.tile m).localAngle v = β} : Finset (Fin N)).card = 2 := by
  classical
  obtain ⟨hαβ', hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ := distinct_of_pos_ne hα hβpos hαβ hγdef hrel
  have hsub : ({i, k₁, k₂} : Finset (Fin N)) ⊆ ({m | (D.tile m).localAngle v = α} : Finset (Fin N)) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hm with rfl | rfl | rfl <;> assumption
  have hcard : ({i, k₁, k₂} : Finset (Fin N)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h23]
    simp [h12, h13]
  have h3 := Finset.card_le_card hsub
  rw [hcard] at h3
  rcases Erdos634.Geometry.Dissection.congruentDissection_boundary_figure_cases D α β γ hαβ' hαγ
      hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hα' hβ' hγ' hv hnv with
    ⟨_, hA, _, _⟩ | ⟨hA, hB, _⟩ | ⟨hA, _, _⟩
  · omega
  · exact hB
  · omega

/-! ### The `c`-slot kill, in coordinates -/

/-- **The `c`-slot fan kill (`P4c`), conditional on R_c.**  Let `D` be a congruent dissection of
the `e = 1` target whose model has the tile's sides and angles, and suppose (**R_c**):
* `D.tile i` is the `c`-tile `cSlotTile x f` on `[x, x + f²]`, `β` at its left end, so `α` at
  `V = (x + f², 0)`;
* two further tiles `k₁, k₂` of `D` present corner angle `α` at `V` — the fan of the traces
  (`flushFiller`/`offsetFiller` at the junction `V` in either chirality, `flushFiller_localAngle`,
  `offsetFiller_localAngle`; the second fan tile in either chirality likewise).

Then **no other tile of `D` presents `α` at `V`**: the `P4c` candidates, both chiralities, are not
tiles of any dissection extending R_c.  The `BG` tile on `[V, V + f]` is not needed for this
half (four `α`-corners at a straight point are already impossible); it enters
`c_slot_forced_beta`.  The residual `β − α` (`residual_L_BG`) is what the trichotomy refuses.

`x ≥ 0` and `x + f² < L` place `V` on the base strictly inside it. -/
theorem c_slot_kill {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {x : ℝ} (hx : 0 ≤ x) (hxL : x + f ^ 2 < baseLen 1 f)
    {i k₁ k₂ : Fin N} (h12 : i ≠ k₁) (h13 : i ≠ k₂) (h23 : k₁ ≠ k₂)
    (hi : D.tile i = cSlotTile x f (by linarith))
    (hk₁ : (D.tile k₁).localAngle (mkPt (x + f ^ 2) 0) = α)
    (hk₂ : (D.tile k₂).localAngle (mkPt (x + f ^ 2) 0) = α) :
    ∀ l : Fin N, l ≠ i → l ≠ k₁ → l ≠ k₂ → (D.tile l).localAngle (mkPt (x + f ^ 2) 0) ≠ α := by
  intro l hli hl1 hl2 hl
  have hf1 : 1 < f := by linarith
  have hv : mkPt (x + f ^ 2) 0 ∈ frontier D.target.carrier := by
    rw [htgt]; exact base_point_mem_frontier hf1 (by positivity) hxL.le
  have hnv : mkPt (x + f ^ 2) 0 ∉ Set.range D.target.pts := by
    rw [htgt]; exact base_point_not_vertex hf1 (by positivity) hxL
  exact straight_point_no_fourth_alpha D hα hβpos hαβ hγdef hrel hirr hM.hα' hM.hβ' hM.hγ' hv hnv
    h12 h13 (Ne.symm hli) h23 (Ne.symm hl1) (Ne.symm hl2)
    (cSlotTile_localAngle_V D hf hM hi) hk₁ hk₂ hl

/-- **The `GB` variant.**  With the `c`-tile `cSlotTile x f` and the `GB` tile
`aTileGB (x + f²) f` on the next letter (`γ` at `V`), the wedge at `V` is already `β`
(`wedge_L_GB`), and no other tile of `D` presents `α` at `V`: the first fan tile is dead. -/
theorem c_slot_kill_gb {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {x : ℝ} (hx : 0 ≤ x) (hxL : x + f ^ 2 < baseLen 1 f)
    {i j : Fin N}
    (hi : D.tile i = cSlotTile x f (by linarith))
    (hj : D.tile j = aTileGB (x + f ^ 2) f (by linarith)) :
    ∀ l : Fin N, l ≠ i → (D.tile l).localAngle (mkPt (x + f ^ 2) 0) ≠ α := by
  intro l hli hl
  have hf1 : 1 < f := by linarith
  have hv : mkPt (x + f ^ 2) 0 ∈ frontier D.target.carrier := by
    rw [htgt]; exact base_point_mem_frontier hf1 (by positivity) hxL.le
  have hnv : mkPt (x + f ^ 2) 0 ∉ Set.range D.target.pts := by
    rw [htgt]; exact base_point_not_vertex hf1 (by positivity) hxL
  exact straight_point_gamma_no_second_alpha D hα hβpos hαβ hγdef hrel hirr hM.hα' hM.hβ' hM.hγ' hv hnv
    (Ne.symm hli) (cSlotTile_localAngle_V D hf hM hi) (aTileGB_localAngle_left D hf hM hj) hl

/-- **What R_c forces instead: exactly one more `β`-corner at `V`.**  With the `c`-tile, the `BG`
tile `aTileBG (x + f²) f` (`β` at `V`) and the two fan tiles, the figure at `V` is `{3α, 2β}`,
so besides the `BG` tile there is exactly one further tile presenting `β` at `V`.  That tile is
the `P2` branch of the traces: its kill, the run `b − a`, is (K2) of `MarchKills` (arithmetic
existing, edge-level realisation not built). -/
theorem c_slot_forced_beta {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : α ≠ β) (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {x : ℝ} (hx : 0 ≤ x) (hxL : x + f ^ 2 < baseLen 1 f)
    {i j k₁ k₂ : Fin N} (h12 : i ≠ k₁) (h13 : i ≠ k₂) (h23 : k₁ ≠ k₂)
    (hi : D.tile i = cSlotTile x f (by linarith))
    (hj : D.tile j = aTileBG (x + f ^ 2) f (by linarith))
    (hk₁ : (D.tile k₁).localAngle (mkPt (x + f ^ 2) 0) = α)
    (hk₂ : (D.tile k₂).localAngle (mkPt (x + f ^ 2) 0) = α) :
    ∃ l : Fin N, l ≠ j ∧ (D.tile l).localAngle (mkPt (x + f ^ 2) 0) = β ∧
      ∀ m : Fin N, (D.tile m).localAngle (mkPt (x + f ^ 2) 0) = β → m = j ∨ m = l := by
  classical
  have hf1 : 1 < f := by linarith
  have hv : mkPt (x + f ^ 2) 0 ∈ frontier D.target.carrier := by
    rw [htgt]; exact base_point_mem_frontier hf1 (by positivity) hxL.le
  have hnv : mkPt (x + f ^ 2) 0 ∉ Set.range D.target.pts := by
    rw [htgt]; exact base_point_not_vertex hf1 (by positivity) hxL
  have hcard := straight_point_three_alpha_two_beta D hα hβpos hαβ hγdef hrel hirr hM.hα' hM.hβ' hM.hγ'
    hv hnv h12 h13 h23 (cSlotTile_localAngle_V D hf hM hi) hk₁ hk₂
  have hjβ : (D.tile j).localAngle (mkPt (x + f ^ 2) 0) = β := aTileBG_localAngle_left D hf hM hj
  set S : Finset (Fin N) := ({m | (D.tile m).localAngle (mkPt (x + f ^ 2) 0) = β} : Finset (Fin N)) with hS
  have hjS : j ∈ S := by simp [hS, hjβ]
  obtain ⟨l, hlS, hlj⟩ : ∃ l ∈ S, l ≠ j := by
    by_contra hcon
    have hall : ∀ m ∈ S, m = j := fun m hm => by
      by_contra hne; exact hcon ⟨m, hm, hne⟩
    have : S = {j} := by
      ext m; constructor
      · intro hm; simp [hall m hm]
      · intro hm; simp at hm; subst hm; exact hjS
    rw [this, Finset.card_singleton] at hcard; omega
  refine ⟨l, hlj, by simpa [hS] using hlS, fun m hm => ?_⟩
  by_contra hcon
  have hmj : m ≠ j := fun h => hcon (Or.inl h)
  have hml : m ≠ l := fun h => hcon (Or.inr h)
  have hsub : ({j, l, m} : Finset (Fin N)) ⊆ S := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact hjS
    · exact hlS
    · simp [hS, hm]
  have h3 : ({j, l, m} : Finset (Fin N)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hml.symm]
    simp [hlj.symm, hmj.symm]
  have := Finset.card_le_card hsub
  omega

/-! ### Non-vacuity of the configuration -/

/-- **The `c`-tile and the `BG` tile of R_c lie in the target** (their six vertices do), for
`x ≥ 0` and `x + f² + 2·dBG ≤ L` — the `BG` apex, `dBG` to the right of `V + f`... exactly
`L/(2f)` further to the left of the right side at its height.  So the hypotheses of `c_slot_kill`
describe an actual placement inside `baseBetaTarget 1 f`, the two tiles sharing only `V`; what is
not exhibited is a dissection containing it — the theorem is that none does once the fan has
begun. -/
theorem cslot_config_in_target {f : ℝ} (hf : 2 ≤ f) {x : ℝ} (hx : 0 ≤ x)
    (hxL : x + f ^ 2 + 2 * dBG f ≤ baseLen 1 f) :
    (∀ k, (cSlotTile x f (by linarith)).pts k ∈ (baseBetaTarget 1 f one_pos (by linarith)).carrier) ∧
    (∀ k, (aTileBG (x + f ^ 2) f (by linarith)).pts k
      ∈ (baseBetaTarget 1 f one_pos (by linarith)).carrier) := by
  have hf1 : 1 < f := by linarith
  have hH := height_pos one_pos hf1
  have hf0 : (0:ℝ) < f := by linarith
  have hL := baseLen_pos one_pos hf1
  have hpos := apexH_pos hf1
  have hL' : baseLen 1 f = 3 * f ^ 2 - 1 := baseLen_one f
  have hapexH : apexH f = height 1 f / f := rfl
  have hdBG : 2 * dBG f = (3 * f ^ 2 - 1) / f := by unfold dBG; field_simp
  have hfL : f ≤ 2 * dBG f := by rw [hdBG, le_div_iff₀ hf0]; nlinarith
  have hxf : x * f ≤ (2 * f ^ 2 - 1) * f - (3 * f ^ 2 - 1) := by
    have h1 : (3 * f ^ 2 - 1) / f ≤ 2 * f ^ 2 - 1 - x := by rw [hdBG, hL'] at hxL; linarith
    rw [div_le_iff₀ hf0] at h1; nlinarith
  have base_pt : ∀ v, 0 ≤ v → v ≤ baseLen 1 f →
      mkPt v 0 ∈ (baseBetaTarget 1 f one_pos hf1).carrier := by
    intro v h0 hv
    refine mem_carrier_of_dets (target_det_pos one_pos hf1) ?_ ?_ ?_ <;> unfold det3
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ baseLen 1 f - v) hH.le]
    · nlinarith [mul_nonneg h0 hH.le]
    · nlinarith
  have capex : mkPt (x + dBG f / f) (1 / f * apexH f)
      ∈ (baseBetaTarget 1 f one_pos hf1).carrier := by
    refine mem_carrier_of_dets (target_det_pos one_pos hf1) ?_ ?_ ?_
    · have e : det3 (x + dBG f / f) (1 / f * apexH f) (baseLen 1 f) 0 (baseLen 1 f / 2)
          (height 1 f) = height 1 f / f ^ 2 * ((3 * f ^ 2 - 1) * (f ^ 2 - 1) - x * f ^ 2) := by
        unfold det3 dBG; rw [hapexH, hL']; field_simp; ring
      rw [e]
      apply mul_nonneg (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hxf hf0.le, pow_pos hf0 2, pow_pos hf0 3,
        pow_pos hf0 4, mul_nonneg (mul_nonneg hf0.le hf0.le) (by linarith : (0:ℝ) ≤ f - 2)]
    · have e : det3 0 0 (x + dBG f / f) (1 / f * apexH f) (baseLen 1 f / 2) (height 1 f)
          = height 1 f * x := by
        unfold det3 dBG; rw [hapexH, hL']; field_simp; ring
      rw [e]; exact mul_nonneg hH.le hx
    · have e : det3 0 0 (baseLen 1 f) 0 (x + dBG f / f) (1 / f * apexH f)
          = baseLen 1 f * (1 / f * apexH f) := by unfold det3; ring
      rw [e]; positivity
  have bgapex : mkPt (x + f ^ 2 + dBG f) (apexH f)
      ∈ (baseBetaTarget 1 f one_pos hf1).carrier := by
    refine mem_carrier_of_dets (target_det_pos one_pos hf1) ?_ ?_ ?_
    · have e : det3 (x + f ^ 2 + dBG f) (apexH f) (baseLen 1 f) 0 (baseLen 1 f / 2) (height 1 f)
          = height 1 f * (baseLen 1 f - (x + f ^ 2 + 2 * dBG f)) := by
        unfold det3 dBG; rw [hapexH, hL']; field_simp; ring
      rw [e]; exact mul_nonneg hH.le (by linarith)
    · have e : det3 0 0 (x + f ^ 2 + dBG f) (apexH f) (baseLen 1 f / 2) (height 1 f)
          = height 1 f * (x + f ^ 2) := by
        unfold det3 dBG; rw [hapexH, hL']; field_simp; ring
      rw [e]; exact mul_nonneg hH.le (by positivity)
    · have e : det3 0 0 (baseLen 1 f) 0 (x + f ^ 2 + dBG f) (apexH f)
          = baseLen 1 f * apexH f := by unfold det3; ring
      rw [e]; positivity
  have hxL1 : x + f ^ 2 ≤ baseLen 1 f := by linarith
  have hxL2 : x + f ^ 2 + f ≤ baseLen 1 f := by linarith
  constructor <;> intro k <;> fin_cases k
  · exact base_pt x hx (by linarith)
  · exact base_pt (x + f ^ 2) (by positivity) hxL1
  · exact capex
  · exact base_pt (x + f ^ 2 + f) (by positivity) hxL2
  · exact base_pt (x + f ^ 2) (by positivity) hxL1
  · exact bgapex

/-- **`f = 3`, in numbers.**  Tile `(3, 8, 9)`, `L = 26`, `c`-tile on `[0, 9]`: `V = (9, 0)`, the
`c`-apex at `(13/9, h/3)`, the `BG` apex at `(40/3, h)`, and the configuration fits:
`9 + 2·dBG = 9 + 26/3 ≤ 26`. -/
theorem cslot_f3 :
    (0 : ℝ) + 3 ^ 2 = 9 ∧ dBG 3 / 3 = 13 / 9 ∧ (0 : ℝ) + 3 ^ 2 + dBG 3 = 40 / 3 ∧
    baseLen 1 3 = 26 ∧ (0 : ℝ) + 3 ^ 2 + 2 * dBG 3 ≤ baseLen 1 3 := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> simp only [dBG, baseLen, Nq] <;> norm_num

end Erdos634.MarchKillsFan
