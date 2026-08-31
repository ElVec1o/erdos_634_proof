import Mathlib.Tactic
import Erdos634.FillerGeneral

/-!
# Coordinates for the `a`-run: apex offsets, equal heights, and the transition gap

Erdős #634, `e = 1`, tile `(a,b,c) = (f, f²-1, f²)`.  This is the first coordinate model of the
march's run, and it is what obligations (ii) and (iii) of `rem:marchobl` need in order to be stated
about an actual configuration rather than about an abstract "advance function".

Put an `a`-edge on the `x`-axis from `(t,0)` to `(t+f,0)`.  The apex is the corner opposite `a`,
carrying `α`.  At a `γ`-corner the flanking sides are `a` and `b`; at a `β`-corner they are `a` and
`c`.  So the apex sits at distance `b` from the `γ`-end and `c` from the `β`-end, and there are two
orientations:

* `GB` (`γ` at the left end): horizontal offset `dGB = (1 - f²)/(2f)` from the left end — negative,
  so the apex overhangs to the left;
* `BG` (`β` at the left end): offset `dBG = (3f² - 1)/(2f)`, which is `c·cos β`, matching
  `Rigidity`'s `x_w` and the closed form `cos β = (3f²-1)/(2f³)` of `lem:anglethreshold`.

Both orientations give the **same** apex height, which is `FillerGeneral.filler_b_general` in
disguise.  Consecutive `a`-tiles of the same orientation therefore have apexes exactly `a = f`
apart; at an orientation change the apex spacing is `(3f²-1)/f`, which is never a tile side.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchCoords

/-- The apex's horizontal offset from the left end, `γ` at the left end. -/
noncomputable def dGB (f : ℝ) : ℝ := (1 - f ^ 2) / (2 * f)

/-- The apex's horizontal offset from the left end, `β` at the left end.  Equals `c·cos β`. -/
noncomputable def dBG (f : ℝ) : ℝ := (3 * f ^ 2 - 1) / (2 * f)

/-- The squared apex height, common to both orientations. -/
noncomputable def h2 (f : ℝ) : ℝ := (f ^ 2 - 1) ^ 2 * (4 * f ^ 2 - 1) / (4 * f ^ 2)

/-- **`GB` places the apex at distance `b` from the left end.** -/
theorem gb_left (f : ℝ) (hf : f ≠ 0) : dGB f ^ 2 + h2 f = (f ^ 2 - 1) ^ 2 := by
  unfold dGB h2; field_simp; ring

/-- **`GB` places the apex at distance `c` from the right end.** -/
theorem gb_right (f : ℝ) (hf : f ≠ 0) : (dGB f - f) ^ 2 + h2 f = (f ^ 2) ^ 2 := by
  unfold dGB h2; field_simp; ring

/-- **`BG` places the apex at distance `c` from the left end.** -/
theorem bg_left (f : ℝ) (hf : f ≠ 0) : dBG f ^ 2 + h2 f = (f ^ 2) ^ 2 := by
  unfold dBG h2; field_simp; ring

/-- **`BG` places the apex at distance `b` from the right end.** -/
theorem bg_right (f : ℝ) (hf : f ≠ 0) : (dBG f - f) ^ 2 + h2 f = (f ^ 2 - 1) ^ 2 := by
  unfold dBG h2; field_simp; ring

/-- **The two orientations have the same apex height.**  This is the content of
`FillerGeneral.filler_b_general`: `(f²-1)² + 4f⁶ - (3f²-1)² = 4f²(f²-1)²`.  It is why the march's
fillers are horizontal, and why the branch is a chirality rather than a change of level. -/
theorem apex_height_common (f : ℝ) (hf : f ≠ 0) :
    (f ^ 2 - 1) ^ 2 - dGB f ^ 2 = (f ^ 2) ^ 2 - dBG f ^ 2 := by
  have h := gb_left f hf
  have h' := bg_left f hf
  linarith

/-! ## Apex spacing along the run

Consecutive `a`-edges occupy `[t, t+f]` and `[t+f, t+2f]`.  The apex spacing is the difference of
the apexes' `x`-coordinates. -/

/-- **Same orientation: the apexes are exactly `a = f` apart.**  So the segment joining them is a
horizontal edge of length `a`, which is a tile side. -/
theorem spacing_same (f t : ℝ) :
    ((t + f) + dGB f) - (t + dGB f) = f ∧ ((t + f) + dBG f) - (t + dBG f) = f := by
  constructor <;> ring

/-- **At an orientation change `GB → BG` the apexes are `(3f²-1)/f` apart.** -/
theorem spacing_gb_bg (f t : ℝ) (hf : f ≠ 0) :
    ((t + f) + dBG f) - (t + dGB f) = (3 * f ^ 2 - 1) / f := by
  unfold dGB dBG; field_simp; ring

/-- **The transition spacing is never a tile side.**  `(3f²-1)/f = s` for `s ∈ {f, f²-1, f²}` would
force `2f² = 1`, `f³ - 3f² - f + 1 = 0`, or `f³ - 3f² + 1 = 0` respectively.  Over the integers with
`f ≥ 2` the first is impossible outright and the other two have no root, since any integer root of a
monic cubic with constant term `±1` divides `1`.

So at an orientation change the two apexes cannot be joined by a single tile edge: the march's
horizontal filler exists only where the orientation is constant.  This is the local, coordinate-side
counterpart of `prop:orientmono`'s conclusion that the run carries at most one transition. -/
theorem transition_not_a_side (f : ℤ) (hf : 2 ≤ f) :
    3 * f ^ 2 - 1 ≠ f * f ∧ 3 * f ^ 2 - 1 ≠ f * (f ^ 2 - 1) ∧ 3 * f ^ 2 - 1 ≠ f * f ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; nlinarith
  · intro h
    have hd : f ∣ 1 := ⟨3 * f + 1 - f ^ 2, by linarith [h]⟩
    have := Int.le_of_dvd one_pos hd; omega
  · intro h
    have hd : f ∣ 1 := ⟨3 * f - f ^ 2, by linarith [h]⟩
    have := Int.le_of_dvd one_pos hd; omega

/-! ## The filler at the junction

The two `a`-tiles occupy `[t, t+f]` and `[t+f, t+2f]`, so their junction is at `t+f`, and their
apexes are at `t+d` and `t+f+d` at the common height.  The filler is the tile with those two apexes
and the junction as its three vertices. -/

/-- **The two offsets are complementary.**  `dGB + dBG = f`.  Equivalently `f - dBG = dGB` and
`f - dGB = dBG`: the horizontal distance from the junction back to one apex is the other
orientation's offset.  This is why the filler's `α`-corner lands exactly on the junction. -/
theorem offsets_complementary (f : ℝ) (hf : f ≠ 0) : dGB f + dBG f = f := by
  unfold dGB dBG; field_simp; ring

/-- **The filler's side to the near apex is `b`,** when the `a`-tiles are `BG`-oriented. -/
theorem junction_to_apex_bg (f : ℝ) (hf : f ≠ 0) :
    (f - dBG f) ^ 2 + h2 f = (f ^ 2 - 1) ^ 2 := by
  have h : f - dBG f = dGB f := by
    have := offsets_complementary f hf; linarith
  rw [h]; exact gb_left f hf

/-- **The filler's side to the far apex is `c`,** in the same orientation. -/
theorem junction_to_apex_gb (f : ℝ) (hf : f ≠ 0) :
    (f - dGB f) ^ 2 + h2 f = (f ^ 2) ^ 2 := by
  have h : f - dGB f = dBG f := by
    have := offsets_complementary f hf; linarith
  rw [h]; exact bg_left f hf

/-- **The chirality is the `a`-tiles' orientation.**  From the junction, the distances to the two
apexes are `b` and `c` in one order under `BG` and in the other under `GB`.  Both fit, and they are
the two placements of `MarchStep.two_placements` realised in coordinates: the filler is the same
triangle, reflected.  This is the geometric content of the branch — not a change of level, since
`apex_height_common` makes both apex heights equal. -/
theorem chirality_swaps_sides (f : ℝ) (hf : f ≠ 0) :
    ((f - dBG f) ^ 2 + h2 f = (f ^ 2 - 1) ^ 2 ∧ dBG f ^ 2 + h2 f = (f ^ 2) ^ 2)
    ∧ ((f - dGB f) ^ 2 + h2 f = (f ^ 2) ^ 2 ∧ dGB f ^ 2 + h2 f = (f ^ 2 - 1) ^ 2) :=
  ⟨⟨junction_to_apex_bg f hf, bg_left f hf⟩, ⟨junction_to_apex_gb f hf, gb_left f hf⟩⟩

/-! ## The filler is forced

Once the two `a`-tiles are placed, the filler's three vertices are determined — the junction and the
two apexes — so there is no choice of filler at all.  What has to be checked is that the triangle on
those three points is congruent to the tile; otherwise the configuration would be inadmissible
rather than forced.  Its three squared side lengths are computed above: `(f - d)² + h²` and
`d² + h²` from the junction to the two apexes, and `f²` between the apexes. -/

/-- **The filler is congruent to the tile, `BG` orientation.**  Squared sides `b², c², a²`. -/
theorem filler_congruent_bg (f : ℝ) (hf : f ≠ 0) :
    ({(f - dBG f) ^ 2 + h2 f, dBG f ^ 2 + h2 f, f ^ 2} : Multiset ℝ)
      = {(f ^ 2 - 1) ^ 2, (f ^ 2) ^ 2, f ^ 2} := by
  rw [junction_to_apex_bg f hf, bg_left f hf]

/-- **The filler is congruent to the tile, `GB` orientation.**  The same three lengths, with `b`
and `c` exchanged — which is the chirality. -/
theorem filler_congruent_gb (f : ℝ) (hf : f ≠ 0) :
    ({(f - dGB f) ^ 2 + h2 f, dGB f ^ 2 + h2 f, f ^ 2} : Multiset ℝ)
      = {(f ^ 2) ^ 2, (f ^ 2 - 1) ^ 2, f ^ 2} := by
  rw [junction_to_apex_gb f hf, gb_left f hf]

/-- **The filler is forced.**  In either orientation the triangle on the junction and the two apexes
has squared sides `{a², b², c²}` as a multiset, so it is congruent to the tile.  Its vertices are
determined by the two `a`-tiles, so the filler is not a branch: the branch is the `a`-tiles' common
orientation, and nothing else.

This is the "consecutive spine steps abut" half of the run-wide forcing.  What it does **not** fix
is which `a`-tile the *next* step begins from — that is the displacement along the run, still open
as obligation (ii). -/
theorem filler_forced (f : ℝ) (hf : f ≠ 0) :
    ({(f - dBG f) ^ 2 + h2 f, dBG f ^ 2 + h2 f, f ^ 2} : Multiset ℝ)
      = ({(f ^ 2 - 1) ^ 2, (f ^ 2) ^ 2, f ^ 2} : Multiset ℝ)
    ∧ ({(f - dGB f) ^ 2 + h2 f, dGB f ^ 2 + h2 f, f ^ 2} : Multiset ℝ)
      = ({(f ^ 2 - 1) ^ 2, (f ^ 2) ^ 2, f ^ 2} : Multiset ℝ) := by
  refine ⟨filler_congruent_bg f hf, ?_⟩
  rw [filler_congruent_gb f hf]
  exact Multiset.cons_swap _ _ _

/-! ## The derived run, and where the advance comes from

The fillers' top edges are `[A₁,A₂]`, `[A₂,A₃], …`, each of length `a = f` (`spacing_same`), lying
at the common height `h` (`apex_height_common`).  So the fillers form a **new `a`-run one level up**:
the configuration is self-similar, which is the mechanism behind the recursion.

The derived run starts at the first apex, whose `x`-coordinate is `dGB` or `dBG` according to the
chirality.  So the chirality does not change the derived run's shape — it translates it.  The shift
is `2f - 1/f`: within `1/f` of exactly two positions of the original run, whose spacing is `f`. -/

/-- **The chirality shifts the derived run by `2f - 1/f`.** -/
theorem derived_run_shift (f : ℝ) (hf : f ≠ 0) : dBG f - dGB f = 2 * f - 1 / f := by
  unfold dGB dBG; field_simp; ring

/-- **The shift falls short of two positions by exactly `1/f`.**  Two positions of the original run
measure `2f`. -/
theorem derived_shift_defect (f : ℝ) (hf : f ≠ 0) :
    2 * f - (dBG f - dGB f) = 1 / f := by
  rw [derived_run_shift f hf]; ring

/-- **The defect scales to the residue `1`.**  Measured in units where the run's `a`-edges are
integers — multiply by `f` — the shortfall is exactly `1`.  That is the residue killed by
`FanKill.one_is_gap`, and it is what `MarchStep.offset_terminal_dies` consumes at the end of the
march: of the two chiralities only the flush one survives there, because the other has accumulated a
stub of length `1`, and `1` is a gap of `⟨f, f²-1, f²⟩`.

So the two chiralities are: the one that advances flush, and the one that advances by two positions
less `1/f`.  The `1/f` is not lost — it is the defect that the terminal argument kills. -/
theorem defect_scales_to_one (f : ℝ) (hf : f ≠ 0) :
    f * (2 * f - (dBG f - dGB f)) = 1 := by
  rw [derived_shift_defect f hf]; field_simp

/-- **The other transition, `BG → GB`, has spacing `(1-f²)/f`.**  Together with `spacing_gb_bg`
this completes the spacing analysis: at an orientation change in *either* direction the apexes are
`(3f²-1)/f` or `(f²-1)/f` apart in absolute value, and neither is a tile side. -/
theorem spacing_bg_gb (f t : ℝ) (hf : f ≠ 0) :
    ((t + f) + dGB f) - (t + dBG f) = (1 - f ^ 2) / f := by
  unfold dGB dBG; field_simp; ring

/-- **Neither transition direction admits a joining edge.**  `(f²-1)/f = s` for
`s ∈ {f, f²-1, f²}` forces `f² - 1 = f²`, `f = 1`, or `f² - 1 = f³`, all impossible for `f ≥ 2`.

**Scope, stated because it is easy to overread.**  This says a transition in *either* direction
lacks a joining tile edge.  It therefore does **not** prove `prop:orientmono`'s asymmetry — that
`BG` is never followed by `GB` while `GB → BG` is permitted once.  The apex-joining criterion is
symmetric in the two directions, so the asymmetry comes from elsewhere and this is not a route to
it. -/
theorem bg_gb_not_a_side (f : ℤ) (hf : 2 ≤ f) :
    f ^ 2 - 1 ≠ f * f ∧ f ^ 2 - 1 ≠ f * (f ^ 2 - 1) ∧ f ^ 2 - 1 ≠ f * f ^ 2 := by
  refine ⟨?_, ?_, by intro h; nlinarith⟩
  · intro h; rw [show f * f = f ^ 2 by ring] at h; omega
  · intro h
    have hd : f ∣ 1 := ⟨f + 1 - f ^ 2, by linarith [h]⟩
    have := Int.le_of_dvd one_pos hd; omega

/-! ## Regression against the engine's exact arithmetic

The engine's trace (`CENGINE_TRACE=2`) prints each placement's vertices as exact
`(p + q√D)/d` pairs.  At `f = 12` it places the march's first `a`-tile as
`(0,0) → (12,0) → (431/24, 143√575/24)`, the second as
`(12,0) → (24,0) → (719/24, 143√575/24)`, and then the filler as
`(12,0) → (719/24, ·) → (431/24, ·)` — the junction and the two apexes.

Every number there is this model: `dBG 12 = 431/24`, the apex height squared is `h2 12`, and the
engine's radicand `D = 575` is `4f² - 1`.  So the model is not a reconstruction, it is what the
search actually does. -/

/-- **The model reproduces the engine's placement at `f = 12`.** -/
theorem model_matches_trace_f12 :
    dBG 12 = 431 / 24 ∧ h2 12 = (143 : ℝ) ^ 2 * 575 / 576 ∧ (4 : ℝ) * 12 ^ 2 - 1 = 575 := by
  refine ⟨?_, ?_, by norm_num⟩
  · unfold dBG; norm_num
  · unfold h2; norm_num

/-- **The second apex is one `a`-step along**, as the trace's `719/24 = 12 + 431/24` shows. -/
theorem second_apex_f12 : (12 : ℝ) + dBG 12 = 719 / 24 := by unfold dBG; norm_num

end Erdos634.MarchCoords
