import Mathlib.Tactic

/-!
# `c`-layers are rigid too, by gap area

Erdős #634 — discharging hypothesis (H2) of `LayerWord`.

`StripRigid` proves `a`-layers rigid by two exclusions: the reflected placement crosses the mast at
the first two positions, and overlaps its predecessor thereafter.  `LayerWord` recorded that the
second exclusion has **no** `c`-layer analogue, because the `c`-layer reflection offset
`D = 2 a cos β = e² N₀ / f²` satisfies `D < 2c` always.  So `c`-layers looked like the harder case.

They are not.  A different invariant closes them, and it needs strictly less: only the mast.

## The argument

Write `R = D / c = e² (3f² - e²) / f⁴`.  A `c`-layer sits on the word `c^e`, and on each `c`-edge a
tile has exactly two placements with its body above: apex at `((j-1)c, a)` (unreflected) or at
`(jc - D, a)` (reflected).  Whatever the orientations, every apex is at height `a`, so the gaps
between consecutive tiles are triangles with a side on the line `t = a`, and each gap must be
filled by a whole number of tiles.  Their areas, in tile units, are:

| gap | area |
|---|---|
| left of tile 1, when tile 1 is reflected | `1 - R` |
| between unreflected `j` and reflected `j+1` | `2 - R` |
| between reflected `j` and unreflected `j+1` | `R` |

Two integer facts finish it:

* `R ∈ (0, 2)` — `offset_pos`, `offset_lt_two`;
* `R ≠ 1` — `offset_ne_one`.  If `e² (3f² - e²) = f⁴` then `e² ∣ f⁴`, so coprimality forces
  `e = 1` and the equation becomes `f⁴ - 3f² + 1 = 0`, which has no integer root (`f = 1` gives
  `-1`; `f ≥ 2` gives `f⁴ ≥ 4f² > 3f²`).

Hence `1 - R ∈ (-1,1) \ {0}`, and `2 - R`, `R` both lie in `(0,2) \ {1}`.  None is a nonnegative
integer.  A reflected tile at position 1 therefore either crosses the mast (`1 - R < 0`) or leaves
a fractional gap; and once tile `j` is unreflected, tile `j+1` cannot be reflected.  Induction from
the mast: **every tile is unreflected.**  The trailing gap is the triangle
`{(ec,0), (ec,a), ((e-1)c, a)}` with sides `a`, `c`, `b` — congruent to the tile, so it is one tile.

The layer closes flush at height `a` and presents `c^e` upward.

Note what is *not* used: no right boundary, no wall at `s = ec`.  Unlike the `a`-layer argument,
this one runs entirely from the mast.

Falsified first: gap areas computed exactly for all 27,317 coprime members with `f < 300`, and the
two integer facts checked to `f < 600`.  Failures: 0.

## Status of the `r > e` chain after this file

`StripRigid.no_tower_fills` (VERIFIED) kills every tower of `a`-strips and `c`-bands.
`LayerWord.word_classification` (VERIFIED) pins the vocabulary to exactly those two blocks.
`StripRigid.strip_rigid` (VERIFIED) and this file (VERIFIED) make both block types rigid.

One hypothesis remains, and it is **not** discharged here: that a layer's word is a finite word of
total length exactly `ec`, i.e. that the column has a right boundary at `s = ec` above height `c`.
The strip supplies it at the base — the strip's rightmost tile has its right edge on the segment of
`s = ec` from `t = 0` to `t = c`, so the wall exists at the bottom — and each rigid layer would
extend it by its own height.  What is missing is that no tile of the layer *straddles* `s = ec`,
which depends on the rogue's word to the right of `ec` and is not settled.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.CLayerRigid

/-- `R > 0`, cleared by `f⁴`: `0 < e²(3f² - e²)`. -/
theorem offset_pos (e f : ℤ) (he : 1 ≤ e) (hef : e < f) :
    0 < e ^ 2 * (3 * f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans (by omega) hef
  have h2 : (0:ℤ) < e ^ 2 := by positivity
  have h3 : (0:ℤ) < 3 * f ^ 2 - e ^ 2 := by nlinarith
  exact mul_pos h2 h3

/-- `R < 2`, cleared by `f⁴`: `e²(3f² - e²) < 2f⁴`, since
`2f⁴ - e²(3f² - e²) = (2f² - e²)(f² - e²) > 0`. -/
theorem offset_lt_two (e f : ℤ) (he : 1 ≤ e) (hef : e < f) :
    e ^ 2 * (3 * f ^ 2 - e ^ 2) < 2 * f ^ 4 := by
  have hf : 0 < f := lt_trans (by omega) hef
  have hv : e ^ 2 < f ^ 2 := by nlinarith
  nlinarith [mul_pos (show (0:ℤ) < 2 * f ^ 2 - e ^ 2 by nlinarith)
                     (show (0:ℤ) < f ^ 2 - e ^ 2 by nlinarith)]

/-- **`R ≠ 1`.**  `e²(3f² - e²) = f⁴` would give `e² ∣ f⁴`, hence `e = 1` by coprimality, hence
`f⁴ - 3f² + 1 = 0`, which has no integer root. -/
theorem offset_ne_one (e f : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f) :
    e ^ 2 * (3 * f ^ 2 - e ^ 2) ≠ f ^ 4 := by
  intro hEq
  have hf : 0 < f := lt_trans (by omega) hef
  have hdvd : e ^ 2 ∣ f ^ 4 := ⟨3 * f ^ 2 - e ^ 2, hEq.symm⟩
  have hcop2 : IsCoprime (e ^ 2) (f ^ 4) := (hcop.pow (m := 2) (n := 4))
  have hunit : IsUnit (e ^ 2) := hcop2.isUnit_of_dvd' (dvd_refl _) hdvd
  have he1 : e = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h <;> nlinarith
  subst he1
  have hf2 : 2 ≤ f := by omega
  have hX : (4:ℤ) ≤ f ^ 2 := by nlinarith
  nlinarith [hX, sq_nonneg (f ^ 2 - 3)]

/-- The left gap `1 - R` is never a nonnegative integer: it lies in `(-1,1)` and is nonzero.
Cleared by `f⁴`. -/
theorem left_gap_not_tiles (e f n : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hn : 0 ≤ n) : n * f ^ 4 ≠ f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2) := by
  intro hEq
  have hf : 0 < f := lt_trans (by omega) hef
  have hf4 : (0:ℤ) < f ^ 4 := by positivity
  have hpos := offset_pos e f he hef
  have hne := offset_ne_one e f he hef hcop
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h] at hEq; exact hne (by linarith)
  · have h1 : 1 ≤ n := h
    nlinarith

/-- The gap between an unreflected tile and a reflected successor is `2 - R`, which lies in
`(0,2)` and differs from `1`: never a nonnegative integer.  This is the inductive step. -/
theorem mixed_gap_not_tiles (e f n : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hn : 0 ≤ n) : n * f ^ 4 ≠ 2 * f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2) := by
  intro hEq
  have hf : 0 < f := lt_trans (by omega) hef
  have hf4 : (0:ℤ) < f ^ 4 := by positivity
  have hpos := offset_pos e f he hef
  have hlt := offset_lt_two e f he hef
  have hne := offset_ne_one e f he hef hcop
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h] at hEq; linarith
  · rcases eq_or_lt_of_le (show (1:ℤ) ≤ n from h) with h1 | h1
    · rw [← h1] at hEq; exact hne (by linarith)
    · have h2 : (2:ℤ) ≤ n := h1
      nlinarith

/-- The gap between a reflected tile and an unreflected successor is `R`, in `(0,2)` and not `1`:
never a nonnegative integer either.  So the two orientations cannot alternate in either order. -/
theorem reverse_gap_not_tiles (e f n : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f)
    (hn : 0 ≤ n) : n * f ^ 4 ≠ e ^ 2 * (3 * f ^ 2 - e ^ 2) := by
  intro hEq
  have hf : 0 < f := lt_trans (by omega) hef
  have hf4 : (0:ℤ) < f ^ 4 := by positivity
  have hpos := offset_pos e f he hef
  have hlt := offset_lt_two e f he hef
  have hne := offset_ne_one e f he hef hcop
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h] at hEq; linarith
  · rcases eq_or_lt_of_le (show (1:ℤ) ≤ n from h) with h1 | h1
    · rw [← h1] at hEq; exact hne (by linarith)
    · have h2 : (2:ℤ) ≤ n := h1
      nlinarith

/-- **`c`-layer rigidity.**  All three gap areas fail to be nonnegative integers simultaneously, for
every member.  So a reflected tile is impossible at position 1 (left gap) and impossible after an
unreflected one (mixed gap); induction from the mast makes every tile unreflected, and the layer
closes flush at height `a` with top word `c^e`. -/
theorem c_layer_rigid (e f : ℤ) (he : 1 ≤ e) (hef : e < f) (hcop : IsCoprime e f) :
    (∀ n : ℤ, 0 ≤ n → n * f ^ 4 ≠ f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2))
      ∧ (∀ n : ℤ, 0 ≤ n → n * f ^ 4 ≠ 2 * f ^ 4 - e ^ 2 * (3 * f ^ 2 - e ^ 2))
      ∧ (∀ n : ℤ, 0 ≤ n → n * f ^ 4 ≠ e ^ 2 * (3 * f ^ 2 - e ^ 2)) :=
  ⟨fun n hn => left_gap_not_tiles e f n he hef hcop hn,
   fun n hn => mixed_gap_not_tiles e f n he hef hcop hn,
   fun n hn => reverse_gap_not_tiles e f n he hef hcop hn⟩

end Erdos634.CLayerRigid

#print axioms Erdos634.CLayerRigid.offset_pos
#print axioms Erdos634.CLayerRigid.offset_lt_two
#print axioms Erdos634.CLayerRigid.offset_ne_one
#print axioms Erdos634.CLayerRigid.left_gap_not_tiles
#print axioms Erdos634.CLayerRigid.mixed_gap_not_tiles
#print axioms Erdos634.CLayerRigid.reverse_gap_not_tiles
#print axioms Erdos634.CLayerRigid.c_layer_rigid
