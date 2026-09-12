import Erdos634.ThickJunctionCoords
import Erdos634.MarchInduction

/-!
# The Gram-extremality core of the `a|a` junction step, at `(e,f) = (2,3)`

Room `e2b`, Hilbert seat, 2026-09-12.  `ThickJunctionCoords.lean` built the `a|a` junction filler at
the thick member `(a,b,c) = (6,5,9)` and discharged `JunctionWedge.junction_step`'s `hcorner`
hypothesis from real coordinates (S1 of the room's rung ladder).  It explicitly left S2 —
`junction_step`'s own bookkeeping — as untouched, citing `JunctionWedge.junction_step`'s abstract
`hu/hφ/hψ` (`Orientation.oangle`) hypotheses.

**That citation misidentifies the actual bottleneck.**  `JunctionWedge.junction_step` is *not* what
closed the `a|a` step at `e = 1`: `MarchInduction.junction_step` did, by an entirely different,
coordinate-level route that never mentions `Orientation.oangle` — `edge_in_wedge` (an overlap-kill
argument, `combo_dies_pts`, general to any `Dissection`) places a candidate third tile's edge in a
closed wedge `p·w ≤ h·u ≤ q·w`, and `gram_extremal` (a fully abstract Gram-determinant lemma, `e,f`-
and even shape-independent — its statement mentions no tile at all) forces two vectors of the tile's
own side lengths inside that wedge to be its rays or their reflection.  `wedge_extremal_coords`
is the wrapper that feeds `gram_extremal` the wedge's own Gram numbers, computed from `dBG f`,
`apexH f` via the *general* law-of-cosines facts `bg_left`/`bg_right`.

**What this file does.**  `MarchInduction.wedge_extremal_coords` is literally parametrised by `f`
under the `(f, f² − 1, f²)` convention, so it does not apply at `(2,3)` where the tile is `(6,5,9)`
(`b ≠ f² − 1`, `c ≠ f²`).  This file redoes exactly that wrapper — line for line the same algebra,
`gram_extremal` reused verbatim, unmodified — using `ThickJunctionCoords`'s own `bg_left63`/
`bg_right63` in place of `bg_left f`/`bg_right f`.  This is the genuinely `(e,f) = (2,3)`-specific
half of S2: the Gram data of the wedge (`B = b² = 25`, `C = c² = 81`, `κ = 35`) and its
nondegeneracy (`BC − κ² = 800 > 0`, so the two wedge rays are not parallel — the geometric content
that makes the tile nondegenerate at all), then `wedge_extremal_coords63`, the exact analogue of
`MarchInduction.wedge_extremal_coords` at this tile: two vectors of lengths `b`, `c` inside the
closed wedge, at mutual distance `a`, are the wedge's own rays or the swapped-and-scaled pair.

**What this does NOT close.**  `wedge_extremal_coords63` takes wedge-membership (`hw1,hw2,hw1',
hw2'`) as *hypotheses*, exactly as `MarchInduction.wedge_extremal_coords` does.  Supplying them from
an actual `CongruentDissection` of `baseBetaTarget 2 3` needs the analogue of `edge_in_wedge` — the
overlap-kill argument applied to `aTileBG63`/`aTileGB63` embedded in `baseBetaTarget 2 3`'s
coordinates, using `MarchInduction.target_height_nonneg` (already `(e,f)`-general, so it transfers
with **no** new work) plus `combo_dies_pts` (also fully general).  That embedding and overlap-kill
instantiation is real, unbuilt work — the actual content of S2 — not attempted here.  So this file
closes the *algebraic* half of S2 (the Gram-extremal step itself, and its nondegeneracy hypothesis)
and leaves the *geometric* half (wedge membership from the dissection) exactly where the room's brief
found it, now named precisely instead of mis-cited as an `oangle` gap.

Novelty checked by grep (`κ63`, `gram`, `wedge_extremal_coords63`, `nondegenerate`): no match in
`lean/`, `paper/`, or `private/`.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.ThickWedgeGram

open Erdos634.ThickJunctionCoords Erdos634.MarchInduction

/-! ## 1. The wedge's two rays, at `(2,3)` -/

/-- The left ray's horizontal offset: the `BG` tile's own apex offset from the junction,
`dBG63 − a63`. -/
noncomputable def p63 : ℝ := dBG63 - a63

/-- The right ray's horizontal offset: `dBG63` itself. -/
noncomputable def q63 : ℝ := dBG63

theorem p63_eq : p63 = 5 / 3 := by unfold p63 dBG63 a63; norm_num
theorem q63_eq : q63 = 23 / 3 := by unfold q63 dBG63; norm_num

/-- The two rays are `a63` apart in their horizontal offset — the two `a`-tile apexes sit at the
same height, `a63` apart, exactly as at `e = 1`. -/
theorem q63_sub_p63 : q63 - p63 = a63 := by unfold p63 q63; ring

theorem p63_pos : 0 < p63 := by rw [p63_eq]; norm_num
theorem q63_pos : 0 < q63 := by rw [q63_eq]; norm_num

/-! ## 2. The Gram data of the wedge -/

/-- **The left ray has length `b63`.**  `p63² + apexH63² = b63²` — `bg_right63` converted from
`h2_63` to `apexH63²` via `apexH63_sq`. -/
theorem B63 : p63 ^ 2 + apexH63 ^ 2 = b63 ^ 2 := by
  rw [apexH63_sq]; unfold p63; exact bg_right63

/-- **The right ray has length `c63`.**  `q63² + apexH63² = c63²` — `bg_left63`, likewise
converted. -/
theorem C63 : q63 ^ 2 + apexH63 ^ 2 = c63 ^ 2 := by
  rw [apexH63_sq]; unfold q63; exact bg_left63

/-- **The inner product of the two rays.**  From `B63`, `C63` and `q63 − p63 = a63` alone (the same
derivation as `MarchInduction.wedge_extremal_coords`'s `hκ`, general to any three reals with this
shape — no tile-specific fact beyond `B63`/`C63`/`q63_sub_p63` is used). -/
noncomputable def kappa63 : ℝ := p63 * q63 + apexH63 ^ 2

theorem kappa63_eq_formula : kappa63 = (b63 ^ 2 + c63 ^ 2 - a63 ^ 2) / 2 := by
  unfold kappa63
  rw [← B63, ← C63, ← q63_sub_p63]; ring

theorem kappa63_eq : kappa63 = 35 := by
  rw [kappa63_eq_formula]; unfold b63 c63 a63; norm_num

theorem kappa63_pos : 0 < kappa63 := by rw [kappa63_eq]; norm_num

/-- **The wedge is nondegenerate at `(2,3)`.**  `B·C − κ² = 25·81 − 35² = 800 > 0`: the two rays
are not parallel, so `gram_extremal`'s hypothesis `hdet` is satisfiable at this thick instance —
the necessary Gram-determinant condition for the `a|a` junction argument to run at all holds here,
exactly as it (trivially, by the same formula) holds at every `e = 1` member. -/
theorem wedge_nondegenerate_63 : 0 < b63 ^ 2 * c63 ^ 2 - kappa63 ^ 2 := by
  rw [kappa63_eq]; unfold b63 c63; norm_num

/-! ## 3. The Gram-extremal step, transcribed for `(6,5,9)` -/

/-- **S2's algebraic core, at `(2,3)`.**  The exact analogue of `MarchInduction.wedge_extremal_
coords`: two vectors `(u,w)`, `(u',w')` in the closed wedge `p63·w ≤ h·u ≤ q63·w` (`h := apexH63`),
of lengths `b63` and `c63`, at mutual distance `a63`, are the wedge's own rays `(p63,h)`, `(q63,h)`
— the flush filler's edges — or the swapped-and-scaled pair `((b/c)·q63, (b/c)·h)`,
`((c/b)·p63, (c/b)·h)` — the (as yet unbuilt, `ThickJunctionCoords`'s own header flags this) offset
filler's edges.  Proved by feeding `gram_extremal` (`MarchInduction.lean`, fully abstract, reused
verbatim, unmodified) the Gram data `B63`/`C63`/`kappa63`/`wedge_nondegenerate_63` above — the same
route as `wedge_extremal_coords`, with `p, q, h, f²−1, f², f` replaced by `p63, q63, apexH63, b63,
c63, a63`.  Wedge membership (`hw1,hw2,hw1',hw2'`) remains a hypothesis, exactly as in the `e = 1`
original: this theorem is the algebraic half of S2, not the geometric half (see the file header). -/
theorem wedge_extremal_coords63 {u w u' w' : ℝ}
    (hw1 : p63 * w ≤ apexH63 * u) (hw2 : apexH63 * u ≤ q63 * w)
    (hw1' : p63 * w' ≤ apexH63 * u') (hw2' : apexH63 * u' ≤ q63 * w')
    (hb : u ^ 2 + w ^ 2 = b63 ^ 2) (hc : u' ^ 2 + w' ^ 2 = c63 ^ 2)
    (ha : (u - u') ^ 2 + (w - w') ^ 2 = a63 ^ 2) :
    (u = p63 ∧ w = apexH63 ∧ u' = q63 ∧ w' = apexH63) ∨
    (u = b63 / c63 * q63 ∧ w = b63 / c63 * apexH63 ∧
     u' = c63 / b63 * p63 ∧ w' = c63 / b63 * apexH63) := by
  have hh : 0 < apexH63 := apexH63_pos
  have hp := p63_pos
  have hq := q63_pos
  have hqp := q63_sub_p63
  have hB := B63
  have hC := C63
  -- the wedge coordinates of `(u, w)` and `(u', w')`
  obtain ⟨a₁, ha₁⟩ : ∃ a, a = (q63 * w - apexH63 * u) / (apexH63 * a63) := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b, b = (apexH63 * u - p63 * w) / (apexH63 * a63) := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a, a = (q63 * w' - apexH63 * u') / (apexH63 * a63) := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b, b = (apexH63 * u' - p63 * w') / (apexH63 * a63) := ⟨_, rfl⟩
  have ha63pos : (0:ℝ) < a63 := by unfold a63; norm_num
  have ha₁0 : 0 ≤ a₁ := by rw [ha₁]; exact div_nonneg (by linarith) (by positivity)
  have hb₁0 : 0 ≤ b₁ := by rw [hb₁]; exact div_nonneg (by linarith) (by positivity)
  have ha₂0 : 0 ≤ a₂ := by rw [ha₂]; exact div_nonneg (by linarith) (by positivity)
  have hb₂0 : 0 ≤ b₂ := by rw [hb₂]; exact div_nonneg (by linarith) (by positivity)
  have hha : apexH63 * a63 ≠ 0 := by positivity
  have eu : u = a₁ * p63 + b₁ * q63 := by
    rw [ha₁, hb₁]; field_simp; rw [← hqp]; ring
  have ew : w = (a₁ + b₁) * apexH63 := by
    rw [ha₁, hb₁]; field_simp; rw [← hqp]; ring
  have eu' : u' = a₂ * p63 + b₂ * q63 := by
    rw [ha₂, hb₂]; field_simp; rw [← hqp]; ring
  have ew' : w' = (a₂ + b₂) * apexH63 := by
    rw [ha₂, hb₂]; field_simp; rw [← hqp]; ring
  have hb' := hb; rw [eu, ew] at hb'
  have hc' := hc; rw [eu', ew'] at hc'
  have hinner : u * u' + w * w' = (b63 ^ 2 + c63 ^ 2 - a63 ^ 2) / 2 := by
    linear_combination (1/2 : ℝ) * hb + (1/2 : ℝ) * hc - (1/2 : ℝ) * ha
  rw [eu, ew, eu', ew'] at hinner
  have G1 : a₁ ^ 2 * (p63 ^ 2 + apexH63 ^ 2) + 2 * a₁ * b₁ * (p63 * q63 + apexH63 ^ 2)
      + b₁ ^ 2 * (q63 ^ 2 + apexH63 ^ 2) = p63 ^ 2 + apexH63 ^ 2 := by
    have key : a₁ ^ 2 * (p63 ^ 2 + apexH63 ^ 2) + 2 * a₁ * b₁ * (p63 * q63 + apexH63 ^ 2)
        + b₁ ^ 2 * (q63 ^ 2 + apexH63 ^ 2)
        = (a₁ * p63 + b₁ * q63) ^ 2 + ((a₁ + b₁) * apexH63) ^ 2 := by ring
    rw [key, hb']; exact hB.symm
  have G2 : a₂ ^ 2 * (p63 ^ 2 + apexH63 ^ 2) + 2 * a₂ * b₂ * (p63 * q63 + apexH63 ^ 2)
      + b₂ ^ 2 * (q63 ^ 2 + apexH63 ^ 2) = q63 ^ 2 + apexH63 ^ 2 := by
    have key : a₂ ^ 2 * (p63 ^ 2 + apexH63 ^ 2) + 2 * a₂ * b₂ * (p63 * q63 + apexH63 ^ 2)
        + b₂ ^ 2 * (q63 ^ 2 + apexH63 ^ 2)
        = (a₂ * p63 + b₂ * q63) ^ 2 + ((a₂ + b₂) * apexH63) ^ 2 := by ring
    rw [key, hc']; exact hC.symm
  have G3 : a₁ * a₂ * (p63 ^ 2 + apexH63 ^ 2) + (a₁ * b₂ + a₂ * b₁) * (p63 * q63 + apexH63 ^ 2)
      + b₁ * b₂ * (q63 ^ 2 + apexH63 ^ 2) = p63 * q63 + apexH63 ^ 2 := by
    have key : a₁ * a₂ * (p63 ^ 2 + apexH63 ^ 2) + (a₁ * b₂ + a₂ * b₁) * (p63 * q63 + apexH63 ^ 2)
        + b₁ * b₂ * (q63 ^ 2 + apexH63 ^ 2)
        = (a₁ * p63 + b₁ * q63) * (a₂ * p63 + b₂ * q63)
          + (a₁ + b₁) * apexH63 * ((a₂ + b₂) * apexH63) := by ring
    rw [key, hinner]
    exact kappa63_eq_formula.symm
  have hκpos' : 0 < p63 ^ 2 + apexH63 ^ 2 := by rw [hB]; unfold b63; positivity
  have hκpos'' : 0 < q63 ^ 2 + apexH63 ^ 2 := by rw [hC]; unfold c63; positivity
  have hdet : 0 < (p63 ^ 2 + apexH63 ^ 2) * (q63 ^ 2 + apexH63 ^ 2)
      - (p63 * q63 + apexH63 ^ 2) ^ 2 := by
    rw [hB, hC, show p63 * q63 + apexH63 ^ 2 = kappa63 from rfl, kappa63_eq]
    unfold b63 c63; norm_num
  have hκpos : 0 < p63 * q63 + apexH63 ^ 2 := by
    rw [show p63 * q63 + apexH63 ^ 2 = kappa63 from rfl]; exact kappa63_pos
  rcases gram_extremal hκpos' hκpos'' hκpos hdet ha₁0 hb₁0 ha₂0 hb₂0 G1 G2 G3 with
    ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    rw [eu, ew, eu', ew', h1, h2, h3, h4]
    refine ⟨by ring, by ring, by ring, by ring⟩
  · right
    have hc63sq : (c63:ℝ) ^ 2 ≠ 0 := by unfold c63; norm_num
    have hb63sq : (b63:ℝ) ^ 2 ≠ 0 := by unfold b63; norm_num
    have hb₁v : b₁ = b63 / c63 := by
      have hsq : b₁ ^ 2 = (b63 / c63) ^ 2 := by
        rw [hB, hC] at h3; rw [div_pow, eq_div_iff hc63sq]; exact h3
      exact (sq_eq_sq₀ hb₁0 (by unfold b63 c63; norm_num)).mp hsq
    have ha₂v : a₂ = c63 / b63 := by
      have hsq : a₂ ^ 2 = (c63 / b63) ^ 2 := by
        rw [hB, hC] at h4; rw [div_pow, eq_div_iff hb63sq]; exact h4
      exact (sq_eq_sq₀ ha₂0 (by unfold b63 c63; norm_num)).mp hsq
    rw [eu, ew, eu', ew', h1, h2, hb₁v, ha₂v]
    refine ⟨by ring, by ring, by ring, by ring⟩

/-- **Non-vacuity: the flush ray pair itself satisfies every hypothesis of
`wedge_extremal_coords63`.**  `(u,w) = (p63, h)`, `(u',w') = (q63, h)` trivially lies in the closed
wedge (with equality) and has the right lengths and mutual distance — the theorem is not
`False → False`. -/
theorem wedge_extremal_coords63_nonvacuous :
    p63 * apexH63 ≤ apexH63 * p63 ∧ apexH63 * p63 ≤ q63 * apexH63 ∧
    p63 * apexH63 ≤ apexH63 * q63 ∧ apexH63 * q63 ≤ q63 * apexH63 ∧
    p63 ^ 2 + apexH63 ^ 2 = b63 ^ 2 ∧ q63 ^ 2 + apexH63 ^ 2 = c63 ^ 2 ∧
    (p63 - q63) ^ 2 + (apexH63 - apexH63) ^ 2 = a63 ^ 2 := by
  have hh := apexH63_pos
  have hlt : p63 < q63 := by have := q63_sub_p63; unfold a63 at this; linarith
  refine ⟨le_of_eq (by ring), ?_, ?_, le_of_eq (by ring), B63, C63, ?_⟩
  · nlinarith
  · nlinarith
  · have h1 : p63 - q63 = -a63 := by have := q63_sub_p63; linarith
    rw [h1, sub_self]; ring

/-! ## 4. Axiom audit -/

#print axioms p63_eq
#print axioms q63_eq
#print axioms q63_sub_p63
#print axioms B63
#print axioms C63
#print axioms kappa63_eq_formula
#print axioms kappa63_eq
#print axioms wedge_nondegenerate_63
#print axioms wedge_extremal_coords63
#print axioms wedge_extremal_coords63_nonvacuous

end Erdos634.ThickWedgeGram
