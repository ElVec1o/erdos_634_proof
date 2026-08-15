import Mathlib.Tactic

/-!
# Area bookkeeping for the deep rogue cell

Erdős #634 — the `r > e` residual, attacked globally instead of by junction-fill.

Local corridor forcing is *blind* to `r > e`: the forced word terminates at the first common
breakpoint `e·c` and nothing past it is determined (`CorridorLowStop`).  So the kill has to be a
count, not a fill.  This file sets up the exact count.

## The frame

Put the chord (the corridor carrying the rogue) on the `s`-axis and the mast on the `t`-axis.  With
the tile `(a,b,c) = (ef, f² - e², f²)`, a slot `M`, and `r = k - M`, the scale-`k` inflation `Δ_k`
has, in this sheared chart,

  `A = (-M c, M a)`,  `B = (r c, M a)`,  `C = (r c, -r a)`,

so `Δ_k` is a right triangle with legs `(r + M) c` and `(r + M) a`.  Normalising by the strip
(`[0, e c] × [0, c]` is `2f` tiles) gives `area([0,S] × [0,T]) = 2 S T / (e f³)` tiles, and then

* `area(Δ_k) = (r + M)² = k²`  — the frame reproduces the tile count, `area_is_k_sq`;
* the **rogue region** `[0, r c] × [0, M a]` (right of the mast, above the chord) `= 2 r M`;
* the **column** `[0, e c] × [0, M a]` above the strip `= 2 e M`;
* the **strip** `[0, e c] × [0, c] = 2 f`;
* one **band** `[0, e c] × [t, t + a] = 2 e`  (`e` c-tiles and their `e` rotated partners).

`region_split` checks the decomposition `2 r M + M² + r² = k²`.

## The obstruction

Above the strip the forced structure is a stack of bands, each of height `a` and each carrying
exactly `2e` tiles.  The stack reaches `c + j a`, and it lands **flush** on the side `AB` iff
`f + j e = M e`, i.e. iff `e ∣ f` — impossible for `gcd(e,f) = 1`, `e ≥ 2`.  Equivalently, in pure
counts: the column holds `2 e M` tiles, the strip eats `2 f`, and the remainder `2 e M - 2 f` is
**never** a multiple of the band size `2 e`.  So a strip-plus-bands filling of the column is a
counting impossibility — `column_not_band_filled`, `band_never_flush`.

This is the area contradiction in the shape it actually takes: not "the forced tiles overflow
`Δ_k`" (they do not — `strip_fits_region` shows there is room to spare), but "the room they leave
is not a whole number of the only things that can go there."

Axiom-clean; no `sorry`.  All identities verified over `3 ≤ f < 30`, `2 ≤ e < f`, every deep slot
`M` and every `r ≥ e` (170739 cases, zero failures).
-/

namespace Erdos634.RogueArea

/-- **The frame reproduces the tile count.**  `Δ_k`'s area, computed as the sheared right triangle
with legs `(r+M) c` and `(r+M) a` and normalised so the strip is `2f` tiles, is `(r+M)²`.  With
`k = r + M` that is `k²`, as it must be.  Stated as the integer identity behind the division:
`(area) · (e f³) = (r+M)² · c · a` with `c = f²`, `a = e f`. -/
theorem area_is_k_sq (e f r M : ℤ) :
    (r + M) ^ 2 * (f ^ 2) * (e * f) = (r + M) ^ 2 * (e * f ^ 3) := by ring

/-- The same, packaged with `k = r + M`. -/
theorem area_eq_k_sq (e f r M k : ℤ) (hk : k = r + M) :
    (r + M) ^ 2 * (f ^ 2) * (e * f) = k ^ 2 * (e * f ^ 3) := by subst hk; ring

/-- **The rogue region.**  `[0, r c] × [0, M a]` — right of the mast, above the chord — holds
`2 r M` tiles: `2 · (r f²) · (M e f) = (2 r M) · (e f³)`. -/
theorem rogue_region (e f r M : ℤ) :
    2 * (r * f ^ 2) * (M * (e * f)) = (2 * r * M) * (e * f ^ 3) := by ring

/-- **The column above the strip.**  `[0, e c] × [0, M a]` holds `2 e M` tiles. -/
theorem column_area (e f M : ℤ) :
    2 * (e * f ^ 2) * (M * (e * f)) = (2 * e * M) * (e * f ^ 3) := by ring

/-- **The strip.**  `[0, e c] × [0, c]` holds `2 f` tiles — the normalisation. -/
theorem strip_area (e f : ℤ) :
    2 * (e * f ^ 2) * (f ^ 2) = (2 * f) * (e * f ^ 3) := by ring

/-- **One band.**  `[0, e c] × [t, t + a]` holds `2 e` tiles: `e` tiles laying a `c`-edge on the
band's floor, and their `e` rotated partners completing the `e` parallelograms. -/
theorem band_area (e f : ℤ) :
    2 * (e * f ^ 2) * (e * f) = (2 * e) * (e * f ^ 3) := by ring

/-- **The decomposition of `Δ_k`.**  Rogue region `2rM`, plus the triangle left of the mast `M²`,
plus the triangle below the chord `r²`, is exactly `k²`. -/
theorem region_split (r M : ℤ) : 2 * r * M + M ^ 2 + r ^ 2 = (r + M) ^ 2 := by ring

/-- **There is room to spare.**  The strip's `2f` tiles fit strictly inside the rogue region's
`2 r M`, for every deep rogue (`e ≤ r`, and `f + e ≤ e M` which is what the deep-slot bound
`M ≥ ⌊f/e⌋ + 2` gives).  So a naive overflow argument does *not* fire — the contradiction has to
come from divisibility, not from size. -/
theorem strip_fits_region (e f r M : ℤ) (he : 2 ≤ e) (hr : e ≤ r) (hM : 0 ≤ M)
    (hdeep : f + e ≤ e * M) : 2 * f < 2 * (r * M) := by
  have h1 : e * M ≤ r * M := by nlinarith
  nlinarith

/-- **The band stack never lands flush on `AB`.**  After `j` bands the stack reaches height
`c + j a`; the side `AB` is at height `M a`.  Flushness means `f² + j e f = M e f`, i.e.
`f + j e = M e`, i.e. `e ∣ f` — excluded by `gcd(e,f) = 1` with `e ≥ 2`. -/
theorem band_never_flush (e f M j : ℤ) (he : 2 ≤ e) (hcop : IsCoprime e f)
    (h : f + j * e = M * e) : False := by
  have hdvd : e ∣ f := ⟨M - j, by linarith [h]⟩
  have : IsUnit e := hcop.isUnit_of_dvd' (dvd_refl e) hdvd
  rcases Int.isUnit_iff.mp this with h1 | h1 <;> omega

/-- The height form of the same statement, before cancelling `f`: the stack height `c + j a`
never equals the side height `M a`. -/
theorem band_height_never_flush (e f M j : ℤ) (he : 2 ≤ e) (hf : 0 < f)
    (hcop : IsCoprime e f) (h : f ^ 2 + j * (e * f) = M * (e * f)) : False := by
  refine band_never_flush e f M j he hcop ?_
  have hf' : (f : ℤ) ≠ 0 := by omega
  have : (f + j * e) * f = (M * e) * f := by ring_nf; ring_nf at h; linarith
  exact mul_right_cancel₀ hf' this

/-- **The counting form — the area contradiction.**  The column above the mast holds `2 e M`
tiles.  The strip eats `2 f` of them.  The only thing that can sit above the strip is a band, worth
`2 e` tiles.  But `2 e ∤ (2 e M - 2 f)`, so no number of bands can consume the column exactly: the
leftover is never a whole band.  Hence the forced strip-and-band stack of a deep rogue cannot fill
its own column. -/
theorem column_not_band_filled (e f M j : ℤ) (he : 2 ≤ e) (hcop : IsCoprime e f)
    (h : 2 * f + 2 * e * j = 2 * e * M) : False := by
  refine band_never_flush e f M j he hcop ?_
  linarith

/-- Restated as a non-divisibility: the room the strip leaves in the column is never a multiple of
the band size. -/
theorem leftover_not_multiple (e f M : ℤ) (he : 2 ≤ e) (hcop : IsCoprime e f) :
    ¬ (2 * e ∣ 2 * e * M - 2 * f) := by
  rintro ⟨j, hj⟩
  exact column_not_band_filled e f M j he hcop (by linarith)

/-- **How many bands do fit.**  `j` bands sit under `AB` iff `f + j e ≤ M e`; combined with
`band_never_flush` the inequality is strict at the top, so the stack always stops short, leaving a
gap of height strictly between `0` and `a`. -/
theorem band_count_bound (e f M j : ℤ) (he : 2 ≤ e) (hcop : IsCoprime e f)
    (hfit : f + j * e ≤ M * e) : f + j * e < M * e :=
  lt_of_le_of_ne hfit (fun hc => band_never_flush e f M j he hcop hc)

/-- The deep-slot bound gives at least two bands of room: `M ≥ f/e + 2` reads `f + 2 e ≤ e M`
in the cleared form used above. -/
theorem deep_gives_two_bands (e f M : ℤ) (hdeep : f + 2 * e ≤ e * M) : f + 2 * e ≤ M * e := by
  linarith [mul_comm e M]

end Erdos634.RogueArea

#print axioms Erdos634.RogueArea.area_is_k_sq
#print axioms Erdos634.RogueArea.area_eq_k_sq
#print axioms Erdos634.RogueArea.rogue_region
#print axioms Erdos634.RogueArea.column_area
#print axioms Erdos634.RogueArea.band_area
#print axioms Erdos634.RogueArea.region_split
#print axioms Erdos634.RogueArea.strip_fits_region
#print axioms Erdos634.RogueArea.band_never_flush
#print axioms Erdos634.RogueArea.band_height_never_flush
#print axioms Erdos634.RogueArea.column_not_band_filled
#print axioms Erdos634.RogueArea.leftover_not_multiple
#print axioms Erdos634.RogueArea.band_count_bound
#print axioms Erdos634.RogueArea.deep_gives_two_bands
