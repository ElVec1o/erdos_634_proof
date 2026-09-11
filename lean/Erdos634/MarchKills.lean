import Erdos634.BaseBetaTargetCoord
import Erdos634.MarchKill
import Erdos634.MarchStep

/-!
# The layer-1 march's kills at `e = 1`, in coordinates: what is a theorem and what is not

Written 2026-09-12, after room `data`'s Target A computation (`private/ROOM/data/VERDICT.md` §5,
`report_targetA.md`): 85 orbits traced at `f = 12, 14`, every refutation a layer-1 monomer–dimer
march with two death sites, the `c`-slot and the second-to-last base letter.  This file records,
for each of the kills the data names, whether it is a theorem about the geometric configuration,
and proves the ones that were missing.  Nothing here is a statement about the search.

Tile `(a, b, c) = (f, f²−1, f²)`, target `baseBetaTarget 1 f` with base `L = 3f² − 1` and height
`H = (f²−1)√(4f²−1)/2` (`BaseBetaTargetCoord`), march coordinates `dBG, dGB, h2`
(`MarchCoords`).  The apex height of every `a`-tile on the base is `h = H/f = c·sin β`.

## Ledger (checked against `lean/` and `paper/` on 2026-09-12; nothing below is re-proved)

* **(K1) the second-offset kill** — after an offset filler a second offset leaves a run of
  length `c − b = 1 ∉ ⟨a,b,c⟩`.  The stub is exactly `1` in coordinates:
  `MarchCoords.defect_scales_to_one`; `1` is a gap: `FanKill.one_is_gap`; the terminal form:
  `MarchStep.offset_terminal_dies`.  **Existing.**  (`VERDICT.md` §5 cites
  `MarchFrontier.noTwoZeros` for this; that declaration is the *count* of surviving chirality
  strings, not the kill.  The kill is the three declarations above.)
* **(K2) the `c`-slot gap** — a run of length `b − a = f² − f − 1` cannot be covered by tile edges:
  `OrderForcing.east_cover_gap` (exactly this statement, `f ≥ 3`), `Frontier.gap_b_sub_a` (all
  `e`), `FanKill.two_gap_contract`; its realisation at the `c`-slot, the `α`-tile's flank
  overflowing the `c`-tile's `a`-edge by `b − a`: `PinBuffer.buffer_overflow_b_is_gap`,
  `.buffer_dichotomy`.  **Existing.**
* **(K3) the `c`-slot fan** — the arithmetic of a corner angle outside `{Xα + Yβ : X, Y ≥ 0}` is
  in the corpus (`AngleArithmetic`, `BaseBetaE1.tile_alpha_irrational`, `A2BranchRow3`'s header
  for the integer encoding).  The *residual angle itself* at the far end of the `c`-slot is **not**
  determined by the reports: `report_targetA.md` records the kill's type (`P4c`) and site, and the
  angle depends on the fan's chirality bits, which only the engine trace carries.  The one fan
  site computable from the vertex figures — the `c`-tile presenting `β` at its far end against a
  `BG` `a`-tile, figure `{3α, 2β}` — has, after its first flush tile, the residues
  `4α + 2β` at the `β`-end (`RESEARCH_LOG` 2026-08-29: three admissible figures, *no*
  contradiction) — so no single residual angle kills it.  **Not formalised; not claimed.**
* **(K4) the far-corner containment kill** — the `a`-tile on the second-to-last base letter fits in
  neither orientation.  Its `GB` half is `MarchKill.bg_gb_dies` (VERIFIED, row M-kill): a `BG`
  tile followed by a `GB` tile at a shared junction is impossible in a dissection.  Its `BG` half
  is **new** here: the `BG` apex on `[L−2f, L−f]` lies outside the target (`f − 1/f` to the right
  of the right side).  Assembled as `far_corner_kill` below.
* **(C) layer-1 confinement** — **new** here as coordinate identities: the overshoot vertex of the
  offset filler is at height `(c/b)·h = c²·sin β / b`, every other march vertex is lower, and
  `(c/b)·h < h + 1` (the strip bound `c·sin β + e²`, with margin `1 − h/b`).
* **(F) flat slot tiles** — a tile laying the `b`- (resp. `c`-) letter on the base has that edge on
  the base by definition of "laying the letter"; "flat" adds nothing.  What is a theorem is the
  apex height: `f·h/(f²−1)` for the `b`-tile, `h/f` for the `c`-tile, both `< h`, in either
  reflection.  Which reflection a tiling admits is **not** decided here.

## The composite, honestly

`far_corner_kill` is conditional on **R**: that the tile on base letter `f` (the interval
`[L−3f, L−2f]`) is the march's `BG` `a`-tile.  R is `rem:marchobl` (i)–(iii) — that a hypothetical
tiling's base layer *is* the march — and is not proved.  Its consequent is a theorem.  The
hypotheses are individually satisfiable: the march tile fits inside the target
(`march_tile_apex_inside`, apex `1/f` short of the right side, the number `report_targetA.md`
records) and the `GB` candidate fits inside the target (`gb_candidate_subset_target`); they die
only together.  The `c`-slot site is not assembled: (K2) is arithmetic, (K3) is open as above.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.MarchKills

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchCoords Erdos634.BaseBetaTargetCoord

/-! ## 1. The apex height `h = H/f = c·sin β` -/

/-- The apex height of the march's `a`-tiles at `e = 1`: the target's height over `f`. -/
noncomputable def apexH (f : ℝ) : ℝ := height 1 f / f

theorem apexH_pos {f : ℝ} (hf : 1 < f) : 0 < apexH f :=
  div_pos (height_pos one_pos hf) (by linarith)

/-- **`h² = h2 f`**: the apex height is `MarchCoords`' common apex height. -/
theorem apexH_sq {f : ℝ} (hf : 1 < f) : apexH f ^ 2 = h2 f := by
  have hs := sq_sqrtD (e := 1) (f := f) one_pos hf
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have : apexH f ^ 2 = (f ^ 2 - 1 ^ 2) ^ 2 * Real.sqrt (Dr 1 f) ^ 2 / (4 * f ^ 2) := by
    unfold apexH height; field_simp; ring
  rw [this, hs]; unfold Dr h2; ring

/-- **`h = c·sin β`**: with `c = f²` and `sin β = H/f³` (leg `f³`, height `H`). -/
theorem apexH_eq_c_sinβ {f : ℝ} (hf : 1 < f) : f ^ 2 * (height 1 f / f ^ 3) = apexH f := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  unfold apexH; field_simp

/-- **`h < b`.**  `h² = (f²−1)²(4f²−1)/(4f²) < (f²−1)²`. -/
theorem apexH_lt_b {f : ℝ} (hf : 1 < f) : apexH f < f ^ 2 - 1 := by
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hpos := apexH_pos hf
  have hsq : apexH f ^ 2 < (f ^ 2 - 1) ^ 2 := by
    rw [apexH_sq hf]; unfold h2
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hb hb]
  nlinarith

/-- The value at `f = 12`: `143√575/24`, the `143√575/24 + 1` of `report_targetA.md`. -/
theorem apexH_f12 : apexH 12 = 143 * Real.sqrt 575 / 24 := by
  unfold apexH height Dr; norm_num; ring

/-! ## 2. (C) Confinement: the overshoot vertex is the highest point, and it is below `h + 1` -/

/-- The height of the offset filler's overshoot vertex, `(c/b)·h`. -/
noncomputable def overshootH (f : ℝ) : ℝ := f ^ 2 / (f ^ 2 - 1) * apexH f

theorem overshootH_eq {f : ℝ} (hf : 1 < f) :
    overshootH f = apexH f + apexH f / (f ^ 2 - 1) := by
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  unfold overshootH; field_simp; ring

/-- **`(c/b)·h = c²·sin β / b`**, the report's exact maximum. -/
theorem overshootH_eq_c_sq_sinβ_div_b {f : ℝ} (hf : 1 < f) :
    overshootH f = (f ^ 2) ^ 2 * (height 1 f / f ^ 3) / (f ^ 2 - 1) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  unfold overshootH apexH; field_simp

theorem apexH_lt_overshootH {f : ℝ} (hf : 1 < f) : apexH f < overshootH f := by
  rw [overshootH_eq hf]
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have := div_pos (apexH_pos hf) hb
  linarith

/-- **The strip bound.**  `(c/b)·h < h + 1`: the overshoot exceeds the level `h` by `h/b < 1`.
This is the engine's bound `c·sin β + e²` with its exact margin `1 − h/b`. -/
theorem overshootH_lt_strip {f : ℝ} (hf : 1 < f) : overshootH f < apexH f + 1 := by
  rw [overshootH_eq hf]
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have : apexH f / (f ^ 2 - 1) < 1 := by rw [div_lt_one hb]; exact apexH_lt_b hf
  linarith

/-! ### The march's tiles as coordinate triangles

Vertex orders are chosen for their consumers, not for orientation: `aTileBG` lists its right base
corner first, which is how `MarchKill.bg_gb_dies` reads a `BG` tile; the others start at the left
base corner or the junction. -/

theorem det_aTileBG (t f : ℝ) (hf : 1 < f) : det3 (t + f) 0 t 0 (t + dBG f) (apexH f) ≠ 0 := by
  have : det3 (t + f) 0 t 0 (t + dBG f) (apexH f) = -(f * apexH f) := by unfold det3; ring
  rw [this]; exact neg_ne_zero.mpr (mul_pos (by linarith) (apexH_pos hf)).ne'

theorem det_aTileGB (t f : ℝ) (hf : 1 < f) : det3 t 0 (t + f) 0 (t + dGB f) (apexH f) ≠ 0 := by
  have : det3 t 0 (t + f) 0 (t + dGB f) (apexH f) = f * apexH f := by unfold det3; ring
  rw [this]; exact (mul_pos (by linarith) (apexH_pos hf)).ne'

theorem det_flushFiller (t f : ℝ) (hf : 1 < f) :
    det3 (t + f) 0 (t + f + dBG f) (apexH f) (t + dBG f) (apexH f) ≠ 0 := by
  have : det3 (t + f) 0 (t + f + dBG f) (apexH f) (t + dBG f) (apexH f) = f * apexH f := by
    unfold det3; ring
  rw [this]; exact (mul_pos (by linarith) (apexH_pos hf)).ne'

theorem det_offsetFiller (t f : ℝ) (hf : 1 < f) :
    det3 (t + f) 0 (t + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)
      (t + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f) ≠ 0 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  have : det3 (t + f) 0 (t + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)
      (t + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f)
      = f * apexH f := by
    unfold det3; field_simp; ring
  rw [this]; exact (mul_pos (by linarith) (apexH_pos hf)).ne'

theorem det_cSlotTile (x f : ℝ) (hf : 1 < f) :
    det3 x 0 (x + f ^ 2) 0 (x + dBG f / f) (1 / f * apexH f) ≠ 0 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have : det3 x 0 (x + f ^ 2) 0 (x + dBG f / f) (1 / f * apexH f) = f * apexH f := by
    unfold det3; field_simp; ring
  rw [this]; exact (mul_pos (by linarith) (apexH_pos hf)).ne'

theorem det_cSlotTile' (x f : ℝ) (hf : 1 < f) :
    det3 x 0 (x + f ^ 2) 0 (x + f ^ 2 - dBG f / f) (1 / f * apexH f) ≠ 0 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have : det3 x 0 (x + f ^ 2) 0 (x + f ^ 2 - dBG f / f) (1 / f * apexH f) = f * apexH f := by
    unfold det3; field_simp; ring
  rw [this]; exact (mul_pos (by linarith) (apexH_pos hf)).ne'

theorem det_bSlotTile (x f : ℝ) (hf : 1 < f) :
    det3 x 0 (x + (f ^ 2 - 1)) 0 (x - 1 / 2) (f / (f ^ 2 - 1) * apexH f) ≠ 0 := by
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  have : det3 x 0 (x + (f ^ 2 - 1)) 0 (x - 1 / 2) (f / (f ^ 2 - 1) * apexH f) = f * apexH f := by
    unfold det3; field_simp; ring
  rw [this]; exact (mul_pos (by linarith) (apexH_pos hf)).ne'

theorem det_bSlotTile' (x f : ℝ) (hf : 1 < f) :
    det3 x 0 (x + (f ^ 2 - 1)) 0 (x + (f ^ 2 - 1) + 1 / 2) (f / (f ^ 2 - 1) * apexH f) ≠ 0 := by
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  have : det3 x 0 (x + (f ^ 2 - 1)) 0 (x + (f ^ 2 - 1) + 1 / 2) (f / (f ^ 2 - 1) * apexH f)
      = f * apexH f := by
    unfold det3; field_simp; ring
  rw [this]; exact (mul_pos (by linarith) (apexH_pos hf)).ne'

/-- The `BG` `a`-tile on `[t, t+f]`: right base corner, left base corner, apex `(t + dBG, h)`. -/
noncomputable def aTileBG (t f : ℝ) (hf : 1 < f) : Tri :=
  mkTri (t + f) 0 t 0 (t + dBG f) (apexH f) (det_aTileBG t f hf)

/-- The `GB` `a`-tile on `[t, t+f]`: left base corner, right base corner, apex `(t + dGB, h)`. -/
noncomputable def aTileGB (t f : ℝ) (hf : 1 < f) : Tri :=
  mkTri t 0 (t + f) 0 (t + dGB f) (apexH f) (det_aTileGB t f hf)

/-- The flush filler at the junction `t+f` of `BG` tiles on `[t,t+f]`, `[t+f,t+2f]`: the junction
and the two apexes (`MarchCoords.filler_forced`). -/
noncomputable def flushFiller (t f : ℝ) (hf : 1 < f) : Tri :=
  mkTri (t + f) 0 (t + f + dBG f) (apexH f) (t + dBG f) (apexH f) (det_flushFiller t f hf)

/-- The offset filler at the same junction: `b` along the `c`-ray (to `(b/c)` of the far apex) and
`c` along the `b`-ray (to `(c/b)` of the near apex — one unit *past* it: the overshoot vertex). -/
noncomputable def offsetFiller (t f : ℝ) (hf : 1 < f) : Tri :=
  mkTri (t + f) 0 (t + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)
    (t + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f)
    (det_offsetFiller t f hf)

/-- The tile laying the `c`-letter on `[x, x+f²]`, `β` at the left end: apex `(x + dBG/f, h/f)`. -/
noncomputable def cSlotTile (x f : ℝ) (hf : 1 < f) : Tri :=
  mkTri x 0 (x + f ^ 2) 0 (x + dBG f / f) (1 / f * apexH f) (det_cSlotTile x f hf)

/-- The same tile reflected: `β` at the right end. -/
noncomputable def cSlotTile' (x f : ℝ) (hf : 1 < f) : Tri :=
  mkTri x 0 (x + f ^ 2) 0 (x + f ^ 2 - dBG f / f) (1 / f * apexH f) (det_cSlotTile' x f hf)

/-- The tile laying the `b`-letter on `[x, x+f²−1]`, `γ` at the left end: apex
`(x − 1/2, f·h/(f²−1))` (`cos γ = −1/(2f)`). -/
noncomputable def bSlotTile (x f : ℝ) (hf : 1 < f) : Tri :=
  mkTri x 0 (x + (f ^ 2 - 1)) 0 (x - 1 / 2) (f / (f ^ 2 - 1) * apexH f) (det_bSlotTile x f hf)

/-- The same tile reflected: `γ` at the right end. -/
noncomputable def bSlotTile' (x f : ℝ) (hf : 1 < f) : Tri :=
  mkTri x 0 (x + (f ^ 2 - 1)) 0 (x + (f ^ 2 - 1) + 1 / 2) (f / (f ^ 2 - 1) * apexH f)
    (det_bSlotTile' x f hf)

/-! ### Squared distances with apex-height ordinates -/

theorem mkTri_pts₀ (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (h : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    (mkTri x₀ y₀ x₁ y₁ x₂ y₂ h).pts 0 = mkPt x₀ y₀ := rfl
theorem mkTri_pts₁ (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (h : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    (mkTri x₀ y₀ x₁ y₁ x₂ y₂ h).pts 1 = mkPt x₁ y₁ := rfl
theorem mkTri_pts₂ (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (h : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    (mkTri x₀ y₀ x₁ y₁ x₂ y₂ h).pts 2 = mkPt x₂ y₂ := rfl

theorem dist_sq_zero_apex {f : ℝ} (hf : 1 < f) (x₁ x₂ : ℝ) :
    dist (mkPt x₁ 0) (mkPt x₂ (apexH f)) ^ 2 = (x₁ - x₂) ^ 2 + h2 f := by
  rw [dist_sq_mkPt, zero_sub, neg_sq, apexH_sq hf]

theorem dist_sq_zero_kapex {f : ℝ} (hf : 1 < f) (x₁ x₂ k : ℝ) :
    dist (mkPt x₁ 0) (mkPt x₂ (k * apexH f)) ^ 2 = (x₁ - x₂) ^ 2 + k ^ 2 * h2 f := by
  rw [dist_sq_mkPt, zero_sub, neg_sq, mul_pow, apexH_sq hf]

theorem dist_sq_kapex_kapex {f : ℝ} (hf : 1 < f) (x₁ x₂ k₁ k₂ : ℝ) :
    dist (mkPt x₁ (k₁ * apexH f)) (mkPt x₂ (k₂ * apexH f)) ^ 2
      = (x₁ - x₂) ^ 2 + (k₁ - k₂) ^ 2 * h2 f := by
  rw [dist_sq_mkPt, ← sub_mul, mul_pow, apexH_sq hf]

/-- **The offset filler is congruent to the tile**: sides `b` (junction to the `c`-ray point),
`c` (junction to the overshoot vertex), `a` (between them).  So the overshoot vertex is a genuine
tile vertex of the march, and its height `(c/b)·h` is attained. -/
theorem offsetFiller_sides (t f : ℝ) (hf : 1 < f) :
    dist ((offsetFiller t f hf).pts 0) ((offsetFiller t f hf).pts 1) ^ 2 = (f ^ 2 - 1) ^ 2 ∧
    dist ((offsetFiller t f hf).pts 0) ((offsetFiller t f hf).pts 2) ^ 2 = (f ^ 2) ^ 2 ∧
    dist ((offsetFiller t f hf).pts 1) ((offsetFiller t f hf).pts 2) ^ 2 = f ^ 2 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  simp only [offsetFiller, mkTri_pts₀, mkTri_pts₁, mkTri_pts₂]
  refine ⟨?_, ?_, ?_⟩
  · rw [dist_sq_zero_kapex hf]; unfold h2 dBG; field_simp; ring
  · rw [dist_sq_zero_kapex hf]; unfold h2 dBG; field_simp; ring
  · rw [dist_sq_kapex_kapex hf]; unfold h2 dBG; field_simp; ring

/-- **The `c`-slot tile is congruent to the tile** (both reflections): base `c`, then `a` at the
`β`-end and `b` at the other. -/
theorem cSlotTile_sides (x f : ℝ) (hf : 1 < f) :
    (dist ((cSlotTile x f hf).pts 0) ((cSlotTile x f hf).pts 2) ^ 2 = f ^ 2 ∧
     dist ((cSlotTile x f hf).pts 1) ((cSlotTile x f hf).pts 2) ^ 2 = (f ^ 2 - 1) ^ 2) ∧
    (dist ((cSlotTile' x f hf).pts 1) ((cSlotTile' x f hf).pts 2) ^ 2 = f ^ 2 ∧
     dist ((cSlotTile' x f hf).pts 0) ((cSlotTile' x f hf).pts 2) ^ 2 = (f ^ 2 - 1) ^ 2) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  simp only [cSlotTile, cSlotTile', mkTri_pts₀, mkTri_pts₁, mkTri_pts₂]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [dist_sq_zero_kapex hf] <;> unfold h2 dBG <;> field_simp <;> ring

/-- **The `b`-slot tile is congruent to the tile** (both reflections): base `b`, then `a` at the
`γ`-end and `c` at the other. -/
theorem bSlotTile_sides (x f : ℝ) (hf : 1 < f) :
    (dist ((bSlotTile x f hf).pts 0) ((bSlotTile x f hf).pts 2) ^ 2 = f ^ 2 ∧
     dist ((bSlotTile x f hf).pts 1) ((bSlotTile x f hf).pts 2) ^ 2 = (f ^ 2) ^ 2) ∧
    (dist ((bSlotTile' x f hf).pts 1) ((bSlotTile' x f hf).pts 2) ^ 2 = f ^ 2 ∧
     dist ((bSlotTile' x f hf).pts 0) ((bSlotTile' x f hf).pts 2) ^ 2 = (f ^ 2) ^ 2) := by
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  simp only [bSlotTile, bSlotTile', mkTri_pts₀, mkTri_pts₁, mkTri_pts₂]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [dist_sq_zero_kapex hf] <;> unfold h2 <;> field_simp <;> ring

/-! ### (F) The slot tiles live in layer 1 -/

/-- **Slot apex heights.**  The `c`-tile's apex is at `h/f`, the `b`-tile's at `f·h/(f²−1)`; both
are below the level `h` once `f ≥ 2` (the second needs `f² − f − 1 > 0`).  "Flat" is not a
choice: a tile laying the letter has that edge on the base, and this is its height.  Which
*reflection* a tiling admits is not decided here. -/
theorem slot_apex_heights {f : ℝ} (hf : 2 ≤ f) (x : ℝ) :
    (cSlotTile x f (by linarith)).pts 2 1 = 1 / f * apexH f ∧
    (cSlotTile' x f (by linarith)).pts 2 1 = 1 / f * apexH f ∧
    (bSlotTile x f (by linarith)).pts 2 1 = f / (f ^ 2 - 1) * apexH f ∧
    (bSlotTile' x f (by linarith)).pts 2 1 = f / (f ^ 2 - 1) * apexH f ∧
    1 / f * apexH f < apexH f ∧ f / (f ^ 2 - 1) * apexH f < apexH f := by
  have hf1 : 1 < f := by linarith
  have hpos := apexH_pos hf1
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have : 1 / f < 1 := by rw [div_lt_one (by linarith)]; exact hf1
    nlinarith
  · have : f / (f ^ 2 - 1) < 1 := by rw [div_lt_one hb]; nlinarith
    nlinarith

/-! ### (C) Every march vertex is at height `≤ (c/b)·h`, with equality at the overshoot vertex -/

/-- **Layer-1 confinement of the march's coordinates.**  Every vertex of every `a`-tile, flush
filler, offset filler and slot tile lies at height at most `overshootH f = (c/b)·h`, and the
offset filler's third vertex attains it.  With `overshootH_lt_strip` this is the strip
`0 ≤ y ≤ c·sin β + 1` of the engine, as an identity rather than an observation. -/
theorem march_confined {f : ℝ} (hf : 2 ≤ f) (t x : ℝ) :
    (∀ k, (aTileBG t f (by linarith)).pts k 1 ≤ overshootH f) ∧
    (∀ k, (aTileGB t f (by linarith)).pts k 1 ≤ overshootH f) ∧
    (∀ k, (flushFiller t f (by linarith)).pts k 1 ≤ overshootH f) ∧
    (∀ k, (offsetFiller t f (by linarith)).pts k 1 ≤ overshootH f) ∧
    (∀ k, (cSlotTile x f (by linarith)).pts k 1 ≤ overshootH f) ∧
    (∀ k, (bSlotTile x f (by linarith)).pts k 1 ≤ overshootH f) ∧
    (offsetFiller t f (by linarith)).pts 2 1 = overshootH f := by
  have hf1 : 1 < f := by linarith
  have hpos := apexH_pos hf1
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hov := apexH_lt_overshootH hf1
  have h0 : (0:ℝ) ≤ overshootH f := by linarith
  have hsl := slot_apex_heights hf x
  have hbc : (f ^ 2 - 1) / f ^ 2 * apexH f ≤ overshootH f := by
    have : (f ^ 2 - 1) / f ^ 2 < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> intro k <;> fin_cases k <;>
    simp only [aTileBG, aTileGB, flushFiller, offsetFiller, cSlotTile, bSlotTile,
      mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, mkPt_one, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] <;>
    first
    | exact h0
    | exact hov.le
    | exact le_refl _
    | exact hbc
    | exact (lt_trans hsl.2.2.2.2.1 hov).le
    | exact (lt_trans hsl.2.2.2.2.2 hov).le

/-! ## 3. (K4) The far corner -/

/-- The right side's linear functional, `(L − q₀)·H − (L/2)·q₁`: nonnegative on the target. Mirror
of `BaseBetaTargetCoord.leftFunctional_carrier`. -/
theorem rightFunctional_carrier {e f : ℝ} (he : 0 < e) (hef : e < f) :
    ∀ q : Plane, q ∈ (baseBetaTarget e f he hef).carrier →
      0 ≤ (baseLen e f - q 0) * height e f - baseLen e f / 2 * q 1 := by
  have hH := height_pos he hef
  have hL := baseLen_pos he hef
  have hconv : Convex ℝ
      {q : Plane | 0 ≤ (baseLen e f - q 0) * height e f - baseLen e f / 2 * q 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hx0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    have hx1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by simp
    rw [hx0, hx1]
    have key : (baseLen e f - (a * x 0 + b * y 0)) * height e f
        - baseLen e f / 2 * (a * x 1 + b * y 1)
        = a * ((baseLen e f - x 0) * height e f - baseLen e f / 2 * x 1)
          + b * ((baseLen e f - y 0) * height e f - baseLen e f / 2 * y 1) := by
      have hb' : b = 1 - a := by linarith
      subst hb'; ring
    rw [key]; exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hsub : (baseBetaTarget e f he hef).carrier
      ⊆ {q : Plane | 0 ≤ (baseLen e f - q 0) * height e f - baseLen e f / 2 * q 1} := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨k, rfl⟩
    fin_cases k <;>
      simp [baseBetaTarget, mkTri_pts, mkPt_zero, mkPt_one] <;> nlinarith [mul_pos hL hH]
  exact fun q hq => hsub hq

/-- A point strictly beyond the right side is outside the target. -/
theorem not_mem_target_of_right {e f : ℝ} (he : 0 < e) (hef : e < f) {x y : ℝ}
    (hxy : (baseLen e f - x) * height e f - baseLen e f / 2 * y < 0) :
    mkPt x y ∉ (baseBetaTarget e f he hef).carrier := by
  intro hmem
  have := rightFunctional_carrier he hef _ hmem
  simp only [mkPt_zero, mkPt_one] at this
  linarith

theorem baseLen_one (f : ℝ) : baseLen 1 f = 3 * f ^ 2 - 1 := by unfold baseLen Nq; ring

/-- The right-side functional at a point `(x, h)` of the march's level, in closed form:
`(L − x − L/(2f))·H`. -/
theorem right_at_level {f : ℝ} (hf : 1 < f) (x : ℝ) :
    (baseLen 1 f - x) * height 1 f - baseLen 1 f / 2 * apexH f
      = (baseLen 1 f - x - baseLen 1 f / (2 * f)) * height 1 f := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  unfold apexH; field_simp

/-- **The `BG` placement on the second-to-last letter pokes out of the target.**  Its apex
`(L − 2f + dBG, h)` has right-side functional `−((f²−1)/f)·H < 0`: it lies `f − 1/f` to the right
of the right side.  This is the "containment" kill of `report_targetA.md`, exactly. -/
theorem bg_apex_second_to_last_outside {f : ℝ} (hf : 1 < f) :
    mkPt (baseLen 1 f - 2 * f + dBG f) (apexH f) ∉ (baseBetaTarget 1 f one_pos hf).carrier := by
  apply not_mem_target_of_right
  rw [right_at_level hf]
  have hH := height_pos one_pos hf
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have : baseLen 1 f - (baseLen 1 f - 2 * f + dBG f) - baseLen 1 f / (2 * f) = -((f ^ 2 - 1) / f) := by
    rw [baseLen_one]; unfold dBG; field_simp; ring
  rw [this]
  have : 0 < (f ^ 2 - 1) / f * height 1 f := by positivity
  linarith

/-- **The `BG` placement on the last letter pokes out too** (functional `−((2f²−1)/f)·H < 0`): the
corner tile that lays `a` on `[L−f, L]` is `GB`, with its `c`-edge along the right side.  So the
corner presents `γ` at `(L−f, 0)`, which is what makes the far corner a `BG → GB` meeting. -/
theorem bg_apex_last_outside {f : ℝ} (hf : 1 < f) :
    mkPt (baseLen 1 f - f + dBG f) (apexH f) ∉ (baseBetaTarget 1 f one_pos hf).carrier := by
  apply not_mem_target_of_right
  rw [right_at_level hf]
  have hH := height_pos one_pos hf
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : 0 < 2 * f ^ 2 - 1 := by nlinarith
  have : baseLen 1 f - (baseLen 1 f - f + dBG f) - baseLen 1 f / (2 * f) = -((2 * f ^ 2 - 1) / f) := by
    rw [baseLen_one]; unfold dBG; field_simp; ring
  rw [this]
  have : 0 < (2 * f ^ 2 - 1) / f * height 1 f := by positivity
  linarith

/-- **Non-vacuity: the march's tile on letter `f` fits.**  The `BG` apex on `[L−3f, L−2f]` has
right-side functional `+H/f`: it is inside, `1/f` short of the right side — the number
`report_targetA.md` reports for the far-corner terminal. -/
theorem march_tile_apex_inside {f : ℝ} (hf : 1 < f) :
    (baseLen 1 f - (baseLen 1 f - 3 * f + dBG f)) * height 1 f - baseLen 1 f / 2 * apexH f
      = height 1 f / f := by
  rw [right_at_level hf, baseLen_one]
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  unfold dBG; field_simp; ring

/-- The three vertices of the `GB` candidate on `[L−2f, L−f]` lie in the target (`f ≥ 2`; the
apex's left-side check is `3f³ − 4f² − f + 1 > 0`). -/
theorem gb_candidate_pts_mem {f : ℝ} (hf : 2 ≤ f) (k : Fin 3) :
    (aTileGB (baseLen 1 f - 2 * f) f (by linarith)).pts k
      ∈ (baseBetaTarget 1 f one_pos (by linarith)).carrier := by
  have hf1 : 1 < f := by linarith
  have hH := height_pos one_pos hf1
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hL := baseLen_pos one_pos hf1
  have hpos := apexH_pos hf1
  have hLf : 2 * f ≤ baseLen 1 f := by rw [baseLen_one]; nlinarith
  fin_cases k <;>
    simp only [aTileGB, baseBetaTarget, mkTri_pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] <;>
    refine mem_carrier_of_dets (target_det_pos one_pos hf1) ?_ ?_ ?_
  · unfold det3; nlinarith [mul_pos hH (by linarith : (0:ℝ) < 2 * f)]
  · unfold det3; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ baseLen 1 f - 2 * f) hH.le]
  · unfold det3; nlinarith
  · unfold det3; nlinarith [mul_pos hH (by linarith : (0:ℝ) < f)]
  · unfold det3; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ baseLen 1 f - f) hH.le]
  · unfold det3; nlinarith
  · -- right side at the apex: `f·H > 0`
    have : det3 (baseLen 1 f - 2 * f + dGB f) (apexH f) (baseLen 1 f) 0 (baseLen 1 f / 2)
        (height 1 f) = f * height 1 f := by
      unfold det3 apexH; rw [baseLen_one]; unfold dGB; field_simp; ring
    rw [this]; positivity
  · -- left side at the apex: `(3f³ − 4f² − f + 1)·H/f > 0`
    have : det3 0 0 (baseLen 1 f - 2 * f + dGB f) (apexH f) (baseLen 1 f / 2) (height 1 f)
        = (3 * f ^ 3 - 4 * f ^ 2 - f + 1) / f * height 1 f := by
      unfold det3 apexH; rw [baseLen_one]; unfold dGB; field_simp; ring
    rw [this]
    have : 0 < 3 * f ^ 3 - 4 * f ^ 2 - f + 1 := by nlinarith [sq_nonneg (f - 2), mul_pos (by linarith : (0:ℝ) < f) (by linarith : (0:ℝ) < f - 1)]
    positivity
  · -- the base: `L·h ≥ 0`
    have : det3 0 0 (baseLen 1 f) 0 (baseLen 1 f - 2 * f + dGB f) (apexH f)
        = baseLen 1 f * apexH f := by unfold det3; ring
    rw [this]; positivity

/-- **Non-vacuity: the `GB` candidate fits inside the target.**  So the hypothesis
`D.tile j = aTileGB (L−2f) f` of `far_corner_kill` is not refuted by the boundary; that placement
dies only against the march tile. -/
theorem gb_candidate_subset_target {f : ℝ} (hf : 2 ≤ f) :
    (aTileGB (baseLen 1 f - 2 * f) f (by linarith)).carrier
      ⊆ (baseBetaTarget 1 f one_pos (by linarith)).carrier := by
  refine convexHull_min ?_ (Tri.convex _)
  rintro _ ⟨k, rfl⟩
  exact gb_candidate_pts_mem hf k

/-- **`BG` then `GB` on the base is impossible in a dissection** — `MarchKill.bg_gb_dies` with its
eight component hypotheses discharged by the coordinate tiles.  This closes the note in
`MarchCoords`' header that turning the straddle into "two `Dissection` tiles' interiors meet" was
"not done here", *for tiles given in these coordinates*. -/
theorem no_bg_then_gb {N : ℕ} (D : Dissection N) {f : ℝ} (hf : 1 < f) {i j : Fin N}
    (hij : i ≠ j) {t s : ℝ} (hts : s = t + f)
    (hi : D.tile i = aTileBG t f hf) (hj : D.tile j = aTileGB s f hf) : False := by
  subst hts
  have hshare : (D.tile i).pts 0 = (D.tile j).pts 0 := by rw [hi, hj]; rfl
  have hA0 : ((D.tile i).pts (0 + 1) - (D.tile i).pts 0) 0 = -f := by
    rw [hi]; show (mkPt t 0 - mkPt (t + f) 0) 0 = -f
    simp only [PiLp.sub_apply, mkPt_zero]; ring
  have hA1 : ((D.tile i).pts (0 + 1) - (D.tile i).pts 0) 1 = 0 := by
    rw [hi]; show (mkPt t 0 - mkPt (t + f) 0) 1 = 0
    simp only [PiLp.sub_apply, mkPt_one]; ring
  have hC0 : ((D.tile i).pts (0 + 2) - (D.tile i).pts 0) 0 = dBG f - f := by
    rw [hi]; show (mkPt (t + dBG f) (apexH f) - mkPt (t + f) 0) 0 = dBG f - f
    simp only [PiLp.sub_apply, mkPt_zero]; ring
  have hC1 : ((D.tile i).pts (0 + 2) - (D.tile i).pts 0) 1 = apexH f := by
    rw [hi]; show (mkPt (t + dBG f) (apexH f) - mkPt (t + f) 0) 1 = apexH f
    simp only [PiLp.sub_apply, mkPt_one]; ring
  have hD0 : ((D.tile j).pts (0 + 1) - (D.tile j).pts 0) 0 = f := by
    rw [hj]; show (mkPt (t + f + f) 0 - mkPt (t + f) 0) 0 = f
    simp only [PiLp.sub_apply, mkPt_zero]; ring
  have hD1 : ((D.tile j).pts (0 + 1) - (D.tile j).pts 0) 1 = 0 := by
    rw [hj]; show (mkPt (t + f + f) 0 - mkPt (t + f) 0) 1 = 0
    simp only [PiLp.sub_apply, mkPt_one]; ring
  have hE0 : ((D.tile j).pts (0 + 2) - (D.tile j).pts 0) 0 = dGB f := by
    rw [hj]; show (mkPt (t + f + dGB f) (apexH f) - mkPt (t + f) 0) 0 = dGB f
    simp only [PiLp.sub_apply, mkPt_zero]; ring
  have hE1 : ((D.tile j).pts (0 + 2) - (D.tile j).pts 0) 1 = apexH f := by
    rw [hj]; show (mkPt (t + f + dGB f) (apexH f) - mkPt (t + f) 0) 1 = apexH f
    simp only [PiLp.sub_apply, mkPt_one]; ring
  exact Erdos634.MarchKill.bg_gb_dies D hij hshare f (apexH f) hf (apexH_pos hf)
    hA0 hA1 hC0 hC1 hD0 hD1 hE0 hE1

/-- **The far-corner kill, conditional on rigidity.**  Let `D` dissect the base-`β` target at
`e = 1` in normal position, and suppose (**R**) some tile of `D` is the march's `BG` `a`-tile on
base letter `f`, the interval `[L−3f, L−2f]`.  Then no tile of `D` lays an `a`-edge on the
second-to-last letter `[L−2f, L−f]` in either orientation: the `BG` placement leaves the target
(`bg_apex_second_to_last_outside`) and the `GB` placement overlaps the march tile
(`no_bg_then_gb`).

R is the open content — `rem:marchobl` (i)–(iii): that a hypothetical tiling's base layer is the
march at all.  Everything after R is this theorem.  The hypotheses are satisfiable one at a time
(`march_tile_apex_inside`, `gb_candidate_subset_target`); the last letter plays no role. -/
theorem far_corner_kill {N : ℕ} (D : Dissection N) {f : ℝ} (hf : 1 < f)
    (htgt : D.target = baseBetaTarget 1 f one_pos hf)
    {iM j : Fin N} (hne : iM ≠ j)
    (hiM : D.tile iM = aTileBG (baseLen 1 f - 3 * f) f hf)
    (hj : D.tile j = aTileBG (baseLen 1 f - 2 * f) f hf ∨
          D.tile j = aTileGB (baseLen 1 f - 2 * f) f hf) : False := by
  rcases hj with hj | hj
  · have hmem : (aTileBG (baseLen 1 f - 2 * f) f hf).pts 2 ∈ (D.tile j).carrier := by
      rw [hj]; exact subset_convexHull ℝ _ ⟨2, rfl⟩
    have h2 := Erdos634.Geometry.tile_subset_target D j hmem
    rw [htgt] at h2
    exact bg_apex_second_to_last_outside hf h2
  · exact no_bg_then_gb D hf hne (by ring) hiM hj

/-- **The far corner at `f = 3`, in numbers.**  `L = 26`; the `BG` apex on `[20, 23]` sits at
`x = 73/3`, the right side at the march's level at `x = 65/3`: outside by `8/3 = f − 1/f`.  The
march tile's apex on `[17, 20]` sits at `x = 64/3`, inside by `1/3 = 1/f`. -/
theorem far_corner_f3 :
    baseLen 1 3 - 2 * 3 + dBG 3 = 73 / 3 ∧ baseLen 1 3 - baseLen 1 3 / (2 * 3) = 65 / 3 ∧
    baseLen 1 3 - 3 * 3 + dBG 3 = 64 / 3 := by
  unfold dBG baseLen Nq; norm_num

/-! ## 4. Axiom audit -/

#print axioms apexH_sq
#print axioms overshootH_lt_strip
#print axioms offsetFiller_sides
#print axioms cSlotTile_sides
#print axioms bSlotTile_sides
#print axioms slot_apex_heights
#print axioms march_confined
#print axioms rightFunctional_carrier
#print axioms bg_apex_second_to_last_outside
#print axioms bg_apex_last_outside
#print axioms gb_candidate_subset_target
#print axioms no_bg_then_gb
#print axioms far_corner_kill

end Erdos634.MarchKills
