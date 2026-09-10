import Erdos634.EpredBaseColumns

/-!
# The geometric residual on `e = f − 1`: corner clearance halves the base columns, and two
# recorded bounds are too strong

Erdős #634.  Written 2026-09-11 against the closing sentence of `EpredBaseColumns.lean`:
*"Any exclusion of these columns must be geometric."*  This file supplies the first genuinely
geometric filter on the `k`-family, computes it in closed form for every member, and corrects two
places in the record where the same idea was applied too aggressively.

## Rule 0.5 — the mechanism is NOT new; the closed form, the family theorem and the corrections are

The idea *"at a close pair the base corner angle `β` is small, so a tall tile cannot sit near the
corner"* is **already in the corpus**: `private/RESEARCH_LOG.md` (2026-08-13, "The wedge kill")
applies it to `N = 83` by hand, and `lean/Erdos634/WedgeBound.lean` carries its arithmetic shadow
(`second_edge_quartic`, `b_count_bound`).  That entry is the headline, not a footnote.  What this
file adds:

1. **The clearance in closed form, rationally, with no trigonometry and no square roots.**  A tile
   laying edge `ℓ` on the base has its far vertex at height `2A/ℓ`; containment in the corner wedge
   of angle `β` puts that vertex at horizontal distance at least `L²/(2Nℓ)` from either corner
   (`xmin`), because the target is isosceles of area `N·A` on a base of length `L`, so
   `cot β = (L/2)/H` and `H/(2A/ℓ) = Nℓ/L`.  Subtracting the apex's own horizontal offset
   `(ℓ² + p² − q²)/(2ℓ)` gives the constraint on the **edge**, and the whole thing collapses:

   * `clearNum_b` — for `ℓ = b` the clearance is exactly **`(a² − b²)/b`**;
   * `clearNum_a`, `clearNum_c` — for `ℓ = a` and `ℓ = c` it is exactly **`0`**.

   So only `b`-edges are pushed away from a base corner, and by an amount that is positive **iff
   `b < a`, i.e. iff the member is sub-golden** (`clearance_pos_iff_subGolden`).  This is the exact
   dual of `N1GapSubGolden.not_separated`: the filter that is vacuous on the separated regime is the
   one that bites here.

2. **The bound on the whole family `e = f − 1`.**  The `b`-edges are disjoint subintervals of
   `[d, L − d]`, so `y·b ≤ L − 2d` (`packing`), which on `e = f − 1` reads

       `y·(2f−1)² ≤ 2f⁴ + 2f³ − 3f + 1`   (`epred_window`),

   and on the `k`-family `y = (k+1)f − 1` this is **`2k ≤ f`**, i.e. `k ≤ ⌊f/2⌋`
   (`epred_k_le_half`, and `epred_k_half_sharp` for the converse).  Against
   `EpredBaseColumns.epred_after_gamma_trap`'s `k ≤ f − 3`, the surviving count drops from `f − 2`
   to `⌊f/2⌋ + 2`: **asymptotically half**.  Verified against brute enumeration for `4 ≤ f ≤ 5000`:
   the clearance bound on `k` is `⌊f/2⌋` with no exceptions.

3. **Two corrections.**  Both recorded versions of the kill are *too strong*, and both are refuted
   here by explicit rational witnesses.

   * `WedgeBound.b_count_bound`'s docstring says the `b`-edges "must fit in the part of the base
     outside both corner zones", i.e. `y·b ≤ eN(b−e)/b`, giving `y ≤ 20` at `N = 83`.  That confines
     the **edge** to the zone computed for the far **vertex** and drops the apex offset
     `(b²+c²−a²)/(2b) = 517/22`.  The true clearance at `(5,6)` is `779/11`, not `2075/22`, and the
     true bound is `y ≤ 24` (`witness_83_true_bound`, `wedgeBound_docstring_refuted`).  A `b`-edge
     on `[71, 82]` clears both corners (`witness_83_left_placement`) although `71 < 2075/22`.
   * The research log's `N = 83` table confines the `b`-edges to a band of width `237.4` and
     concludes `(3,23,2)` is **DEAD**, leaving "three base words".  That band is **asymmetric about
     the midpoint** — it fixes one chirality of the tile.  `Congruence.Tri.Congruent` is congruence
     up to an arbitrary isometry and `Tri.Unreflected`/`Tri.Reflected` is a dichotomy with no extra
     hypothesis, so the mirrored tile is admissible: a `b`-edge on `[333, 344]` clears both corners
     (`witness_83_reflected_placement`) although `344 > 6780/22 = 308.18…`, the log's right limit.
     The correct band is `273.36…` and **`(3,23,2)` survives**: `N = 83` has **four** base words
     after the wedge, not three.  (The engine instance was built with five words — `BaseWord.lean`
     line 58 — so nothing downstream consumed the wrong count.)

## The distance, stated honestly

Not one of the three outcomes.  The clearance is a real, uniform, geometric filter and it halves an
unbounded set — it does not bound it.  `f/2 + 2` columns still grow like `√(N/8)`.  And **at
`N = 83`, the one open base-β row below `N = 110`, the corrected filter kills nothing that
`cornerpara_filter` had not already killed** (`witness_83_wedge_adds_nothing`): the only column it
excludes there is `(2,29,1)`, whose `x + z = 3`.  The filter first bites at `f = 7`
(`witness_f7_new_kill`), and the first prime member it advances is `N = 179` (`f = 9`, `8 → 6`
columns).

## The geometric input, named once (the `WedgeBound` convention)

> A tile laying edge `ℓ` on the base, whose far vertex has horizontal coordinate `X` measured from
> the left base corner, lies inside the target only if `L² ≤ 2·N·ℓ·X` and `L² ≤ 2·N·ℓ·(L − X)`.

That is one containment statement about a triangle in an isosceles target, not a chain, and it is
*equivalent* to the two side half-planes (the two base vertices are on the base, hence inside).  It
is carried as `ClearsLeft`/`ClearsRight` and everything below is its arithmetic shadow — which is
why the two witnesses above genuinely refute the recorded bounds rather than merely failing to
reproduce them.
-/

namespace Erdos634.EpredWedgeClearance

/-! ## 1.  Tile data, and the two numerators -/

/-- Tile sides `a = ef`, `b = f² − e²`, `c = f²`; `N = 3f² − e²`; base length `L = eN`.

Scope: the **`m = 1`** base-β target `(f³, f³, eN)`, which is the prime case (`N` prime forces
`m = 1`).  At `m > 1` the tile count is `m²N` and the base `meN`, and every formula below would
carry the extra factor. -/
def sa (e f : ℤ) : ℤ := e * f
def sb (e f : ℤ) : ℤ := f ^ 2 - e ^ 2
def sc (e f : ℤ) : ℤ := f ^ 2
def NN (e f : ℤ) : ℤ := 3 * f ^ 2 - e ^ 2
def baseLen (e f : ℤ) : ℤ := e * NN e f

/-- **The corner-zone numerator.**  `xmin ℓ = L²/(2Nℓ)`, and on a base-β target `L = eN`, so
`L²/(2Nℓ) = e²N/(2ℓ)`.  This lemma is the identity that makes it a tile quantity:
`e²N = a² + c² − b²`. -/
theorem xmin_numerator (e f : ℤ) :
    e ^ 2 * NN e f = sa e f ^ 2 + sc e f ^ 2 - sb e f ^ 2 := by
  simp only [sa, sb, sc, NN]; ring

/-- The apex's horizontal offset from the `p`-end of a base edge of length `ℓ`, doubled:
`2ℓ · offset = ℓ² + p² − q²`.  Both chiralities are available (swap `p` and `q`); the *weaker*
corner constraint uses the larger offset, i.e. the longer of the two remaining sides. -/
def projNum (l p q : ℤ) : ℤ := l ^ 2 + p ^ 2 - q ^ 2

/-- **Clearance numerator**: `2ℓ · (clearance of an `ℓ`-edge) = e²N − projNum ℓ p q`. -/
def clearNum (e f l p q : ℤ) : ℤ := e ^ 2 * NN e f - projNum l p q

/-- **A `b`-edge's clearance is `(a² − b²)/b`.**  The longer of the two remaining sides is `c`. -/
theorem clearNum_b (e f : ℤ) :
    clearNum e f (sb e f) (sc e f) (sa e f) = 2 * (sa e f ^ 2 - sb e f ^ 2) := by
  simp only [clearNum, projNum, sa, sb, sc, NN]; ring

/-- **An `a`-edge's clearance is exactly `0`.**  The longer remaining side is `c`. -/
theorem clearNum_a (e f : ℤ) : clearNum e f (sa e f) (sc e f) (sb e f) = 0 := by
  simp only [clearNum, projNum, sa, sb, sc, NN]; ring

/-- **A `c`-edge's clearance is exactly `0`.**  The longer remaining side is `a`. -/
theorem clearNum_c (e f : ℤ) : clearNum e f (sc e f) (sa e f) (sb e f) = 0 := by
  simp only [clearNum, projNum, sa, sb, sc, NN]; ring

/-- **The filter exists exactly on the sub-golden regime.**  The `b`-clearance is positive iff
`b < a`, which is `N1GapSubGolden`'s defining inequality `f² < ef + e²`.  On a separated member
(`b > a`, `Frontier.separated_b_gt_two_a`) it is negative and the whole argument is vacuous — which
is why the log's own first attempt at this (2026-08-13, "no corner of a base-β target is narrow")
found nothing on the thin members it sampled. -/
theorem clearance_pos_iff_subGolden {e f : ℤ} (ha : 0 < sa e f) (hb : 0 < sb e f) :
    0 < sa e f ^ 2 - sb e f ^ 2 ↔ sb e f < sa e f := by
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ## 2.  The geometric input, and what it forces on a `b`-edge -/

/-- The left-corner containment for a base tile whose far vertex has horizontal coordinate `X`
and whose base edge has length `ℓ`.  See the header: this is the wedge condition
`height ≤ X · tan β`, cleared of `A` and of `tan`. -/
def ClearsLeft (e f l : ℤ) (X : ℚ) : Prop := ((baseLen e f : ℚ)) ^ 2 ≤ 2 * (NN e f : ℚ) * l * X

/-- The right-corner containment, by the mirror. -/
def ClearsRight (e f l : ℤ) (X : ℚ) : Prop :=
  ((baseLen e f : ℚ)) ^ 2 ≤ 2 * (NN e f : ℚ) * l * ((baseLen e f : ℚ) - X)

/-- **The clearance, derived.**  A `b`-edge with left endpoint `s`, laid in the chirality whose
apex offset is the larger one `projNum b c a / (2b) = (b² + c² − a²)/(2b)`, clears the left corner
only if `2·b·s ≥ clearNum`, i.e. (by `clearNum_b`) only if `s ≥ (a² − b²)/b`.  Everything is
rational: the tile's area and the angle `β` both cancel. -/
theorem b_edge_left_clearance {e f : ℤ} (hN : 0 < NN e f) (hb : 0 < sb e f) (s : ℚ)
    (h : ClearsLeft e f (sb e f)
          (s + (projNum (sb e f) (sc e f) (sa e f) : ℚ) / (2 * (sb e f : ℚ)))) :
    ((clearNum e f (sb e f) (sc e f) (sa e f) : ℤ) : ℚ) ≤ 2 * (sb e f : ℚ) * s := by
  have hbQ : (0:ℚ) < (sb e f : ℚ) := by exact_mod_cast hb
  have hNQ : (0:ℚ) < (NN e f : ℚ) := by exact_mod_cast hN
  unfold ClearsLeft baseLen at h
  push_cast at h
  have hexp : 2 * (NN e f : ℚ) * (sb e f : ℚ)
      * (s + (projNum (sb e f) (sc e f) (sa e f) : ℚ) / (2 * (sb e f : ℚ)))
      = (NN e f : ℚ) * (2 * (sb e f : ℚ) * s + (projNum (sb e f) (sc e f) (sa e f) : ℚ)) := by
    field_simp
    try ring
  have h2 : (NN e f : ℚ) * ((e:ℚ) ^ 2 * (NN e f : ℚ))
      ≤ (NN e f : ℚ) * (2 * (sb e f : ℚ) * s + (projNum (sb e f) (sc e f) (sa e f) : ℚ)) := by
    nlinarith [h, hexp]
  have h3 := le_of_mul_le_mul_left h2 hNQ
  simp only [clearNum]
  push_cast
  linarith [h3]

/-- The same on the right, by the mirror: a `b`-edge with **right** endpoint `r`, laid in the
mirrored chirality, needs `L − r ≥ (a² − b²)/b`.  This is the half the research log's `N = 83`
band omits. -/
theorem b_edge_right_clearance {e f : ℤ} (hN : 0 < NN e f) (hb : 0 < sb e f) (r : ℚ)
    (h : ClearsRight e f (sb e f)
          (r - (projNum (sb e f) (sc e f) (sa e f) : ℚ) / (2 * (sb e f : ℚ)))) :
    ((clearNum e f (sb e f) (sc e f) (sa e f) : ℤ) : ℚ)
      ≤ 2 * (sb e f : ℚ) * ((baseLen e f : ℚ) - r) := by
  have hbQ : (0:ℚ) < (sb e f : ℚ) := by exact_mod_cast hb
  have hNQ : (0:ℚ) < (NN e f : ℚ) := by exact_mod_cast hN
  unfold ClearsRight baseLen at h
  push_cast at h
  have hexp : 2 * (NN e f : ℚ) * (sb e f : ℚ)
      * ((e:ℚ) * (NN e f : ℚ)
          - (r - (projNum (sb e f) (sc e f) (sa e f) : ℚ) / (2 * (sb e f : ℚ))))
      = (NN e f : ℚ) * (2 * (sb e f : ℚ) * ((e:ℚ) * (NN e f : ℚ) - r)
          + (projNum (sb e f) (sc e f) (sa e f) : ℚ)) := by
    field_simp
    try ring
  have h2 : (NN e f : ℚ) * ((e:ℚ) ^ 2 * (NN e f : ℚ))
      ≤ (NN e f : ℚ) * (2 * (sb e f : ℚ) * ((e:ℚ) * (NN e f : ℚ) - r)
          + (projNum (sb e f) (sc e f) (sa e f) : ℚ)) := by
    nlinarith [h, hexp]
  have h3 := le_of_mul_le_mul_left h2 hNQ
  simp only [clearNum, baseLen]
  push_cast
  linarith [h3]

/-! ## 3.  Packing: `y` disjoint `b`-edges inside a window of width `W − d` -/

/-- **The packing bound.**  If `y ≥ 1` intervals of length `b`, listed left to right by their left
endpoints `s 0 < s 1 < …`, all start at or after `d`, are pairwise non-overlapping (`s i + b ≤
s (i+1)`), and the last one ends at or before `W`, then `y·b ≤ W − d`.

This is the only place the *disjointness* of the base edges is used, and it is what turns a
per-edge clearance into a bound on the `b`-count. -/
theorem packing {b d W : ℚ} (hb : 0 < b) {y : ℕ} (hy : 0 < y) (s : ℕ → ℚ)
    (h0 : ∀ i, i < y → d ≤ s i)
    (hstep : ∀ i, i + 1 < y → s i + b ≤ s (i + 1))
    (hlast : s (y - 1) + b ≤ W) :
    (y : ℚ) * b ≤ W - d := by
  have main : ∀ i, i < y → d + (i : ℚ) * b ≤ s i := by
    intro i
    induction i with
    | zero => intro h; simpa using h0 0 h
    | succ n ih =>
      intro hn
      have hn' : n < y := by omega
      have h1 := ih hn'
      have h2 := hstep n (by omega)
      push_cast
      linarith [h1, h2]
  have hlt : y - 1 < y := by omega
  have h3 := main (y - 1) hlt
  have hcast : ((y - 1 : ℕ) : ℚ) = (y : ℚ) - 1 := by
    have : (1:ℕ) ≤ y := hy
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast] at h3
  linarith [h3, hlast]

/-- **Either chirality clears by at least `(a² − b²)/b`.**  The mirrored tile's clearance numerator
is `e²N − (b² + a² − c²) = 2(c² − b²)`, and `2(a² − b²) ≤ 2(c² − b²)` because `a < c`.  So the
weaker of the two chiralities is the `c`-offset one, and **both** ends of a `b`-edge are pushed in
by at least `(a² − b²)/b` no matter how the tile is reflected.  This is precisely what the research
log's 2026-08-13 band drops. -/
theorem chirality_min (e f : ℤ) (h : sa e f ^ 2 ≤ sc e f ^ 2) :
    clearNum e f (sb e f) (sc e f) (sa e f) ≤ clearNum e f (sb e f) (sa e f) (sc e f) := by
  simp only [clearNum, projNum]; linarith [h]

/-- `a < c` at every member with `0 < e < f`, so `chirality_min` is never vacuous. -/
theorem a_lt_c {e f : ℤ} (he : 0 < e) (hef : e < f) : sa e f < sc e f := by
  simp only [sa, sc]; nlinarith

/-! ### The assembled `b`-count bound -/

/-- **The `b`-count bound, assembled.**  `y` disjoint `b`-edges, each clearing both corners by
`d = (a² − b²)/b`, force `y·b ≤ L − 2d`. -/
theorem b_count_bound {e f : ℤ} (hb : 0 < sb e f) {y : ℕ} (hy : 0 < y) (s : ℕ → ℚ)
    (h0 : ∀ i, i < y → ((sa e f ^ 2 - sb e f ^ 2 : ℤ) : ℚ) / (sb e f : ℚ) ≤ s i)
    (hstep : ∀ i, i + 1 < y → s i + (sb e f : ℚ) ≤ s (i + 1))
    (hlast : s (y - 1) + (sb e f : ℚ)
      ≤ (baseLen e f : ℚ) - ((sa e f ^ 2 - sb e f ^ 2 : ℤ) : ℚ) / (sb e f : ℚ)) :
    (y : ℚ) * (sb e f : ℚ)
      ≤ (baseLen e f : ℚ) - 2 * (((sa e f ^ 2 - sb e f ^ 2 : ℤ) : ℚ) / (sb e f : ℚ)) := by
  have hbQ : (0:ℚ) < (sb e f : ℚ) := by exact_mod_cast hb
  have := packing (b := (sb e f : ℚ))
    (d := ((sa e f ^ 2 - sb e f ^ 2 : ℤ) : ℚ) / (sb e f : ℚ))
    (W := (baseLen e f : ℚ) - ((sa e f ^ 2 - sb e f ^ 2 : ℤ) : ℚ) / (sb e f : ℚ))
    hbQ hy s h0 hstep hlast
  linarith [this]

/-- The same, cleared of denominators, over `ℤ`: **`y·b² ≤ L·b − 2(a² − b²)`.** -/
theorem b_count_bound_int {e f : ℤ} (hb : 0 < sb e f) {y : ℕ}
    (h : (y : ℚ) * (sb e f : ℚ)
      ≤ (baseLen e f : ℚ) - 2 * (((sa e f ^ 2 - sb e f ^ 2 : ℤ) : ℚ) / (sb e f : ℚ))) :
    (y : ℤ) * sb e f ^ 2 ≤ baseLen e f * sb e f - 2 * (sa e f ^ 2 - sb e f ^ 2) := by
  have hbQ : (0:ℚ) < (sb e f : ℚ) := by exact_mod_cast hb
  rw [← @Int.cast_le ℚ]
  push_cast
  have hmul : (y : ℚ) * (sb e f : ℚ) * (sb e f : ℚ)
      ≤ ((baseLen e f : ℚ) - 2 * (((sa e f ^ 2 - sb e f ^ 2 : ℤ) : ℚ) / (sb e f : ℚ)))
        * (sb e f : ℚ) := by
    exact mul_le_mul_of_nonneg_right h (le_of_lt hbQ)
  have hclear : ((baseLen e f : ℚ) - 2 * (((sa e f ^ 2 - sb e f ^ 2 : ℤ) : ℚ) / (sb e f : ℚ)))
      * (sb e f : ℚ)
      = (baseLen e f : ℚ) * (sb e f : ℚ)
        - 2 * ((sa e f : ℚ) ^ 2 - (sb e f : ℚ) ^ 2) := by
    push_cast
    field_simp
    try ring
  rw [hclear] at hmul
  nlinarith [hmul]

/-! ## 4.  The bound on the family `e = f − 1` -/

/-- **The window, in closed form.**  On `e = f − 1` the tile is `(f²−f, 2f−1, f²)` and the base is
`L = (f−1)(2f²+2f−1)`.  The available window for `b`-edges is `L − 2·(a²−b²)/b`, so the bound
`y·b ≤ L − 2(a²−b²)/b` cleared of denominators is `y·b² ≤ Lb − 2(a²−b²)`, and

    `L·b − 2(a² − b²) = 2f⁴ + 2f³ − 3f + 1`.

(`f = 6`, `N = 83`: `415·11 − 2·779 = 3007`, so `y ≤ 3007/121 = 24.85…`, i.e. `y ≤ 24`.) -/
theorem epred_window (f : ℤ) :
    ((f - 1) * (2 * f ^ 2 + 2 * f - 1)) * (2 * f - 1)
      - 2 * ((f ^ 2 - f) ^ 2 - (2 * f - 1) ^ 2) = 2 * f ^ 4 + 2 * f ^ 3 - 3 * f + 1 := by
  ring

/-- **The bound on the family, in the file's own coordinates.**  At `e = f − 1`,
`b_count_bound_int` reads `y·(2f−1)² ≤ 2f⁴ + 2f³ − 3f + 1`. -/
theorem epred_b_count_bound {f : ℤ} {y : ℕ}
    (h : (y : ℤ) * sb (f - 1) f ^ 2
      ≤ baseLen (f - 1) f * sb (f - 1) f - 2 * (sa (f - 1) f ^ 2 - sb (f - 1) f ^ 2)) :
    (y : ℤ) * (2 * f - 1) ^ 2 ≤ 2 * f ^ 4 + 2 * f ^ 3 - 3 * f + 1 := by
  simp only [sa, sb, baseLen, NN] at h
  nlinarith [h]

/-- Sanity: at `e = f − 1` the three `sX` really are `(f²−f, 2f−1, f²)` and `L` is the base. -/
theorem epred_tile (f : ℤ) :
    sa (f - 1) f = f ^ 2 - f ∧ sb (f - 1) f = 2 * f - 1 ∧ sc (f - 1) f = f ^ 2 ∧
      baseLen (f - 1) f = (f - 1) * (2 * f ^ 2 + 2 * f - 1) := by
  refine ⟨by simp only [sa]; ring, by simp only [sb]; ring, rfl, by simp only [baseLen, NN]; ring⟩

/-- **The clearance bound is `2k ≤ f`.**  On the `k`-family of `EpredBaseColumns` the `b`-count is
`y = (k+1)f − 1`, and `y·b² ≤ 2f⁴ + 2f³ − 3f + 1` forces `k ≤ ⌊f/2⌋`.

Against `epred_after_gamma_trap`'s `k ≤ f − 3` this is a strict improvement for every `f ≥ 7`. -/
theorem epred_k_le_half {f k : ℤ} (hf : 4 ≤ f) (hk0 : 0 ≤ k)
    (h : ((k + 1) * f - 1) * (2 * f - 1) ^ 2 ≤ 2 * f ^ 4 + 2 * f ^ 3 - 3 * f + 1) :
    2 * k ≤ f := by
  by_contra hc
  push_neg at hc
  have hk : f + 1 ≤ 2 * k := by omega
  have hcube : 0 ≤ (f - 4) * (4 * f ^ 2 - 3 * f + 5) :=
    mul_nonneg (by omega) (by nlinarith [hf])
  have hkey : 0 ≤ (2 * k - (f + 1)) * (f * (2 * f - 1) ^ 2) :=
    mul_nonneg (by omega) (by positivity)
  have hid : 2 * (((k + 1) * f - 1) * (2 * f - 1) ^ 2)
      = ((f + 3) * f - 2) * (2 * f - 1) ^ 2 + (2 * k - (f + 1)) * (f * (2 * f - 1) ^ 2) := by
    ring
  have hid2 : ((f + 3) * f - 2) * (2 * f - 1) ^ 2
      = 2 * (2 * f ^ 4 + 2 * f ^ 3 - 3 * f + 1) + ((f - 4) * (4 * f ^ 2 - 3 * f + 5) + 16) := by
    ring
  linarith [h, hkey, hid, hid2, hcube]

/-- **Sharp**: `k = ⌊f/2⌋` really does satisfy the bound, so `⌊f/2⌋` is the exact cut and the
theorem above is not an over-estimate.  Stated for even and odd `f` separately. -/
theorem epred_k_half_sharp_even {g : ℤ} (hg : 2 ≤ g) :
    ((g + 1) * (2 * g) - 1) * (2 * (2 * g) - 1) ^ 2
      ≤ 2 * (2 * g) ^ 4 + 2 * (2 * g) ^ 3 - 3 * (2 * g) + 1 := by
  nlinarith [hg, sq_nonneg g, sq_nonneg (g - 2)]

theorem epred_k_half_sharp_odd {g : ℤ} (hg : 2 ≤ g) :
    ((g + 1) * (2 * g + 1) - 1) * (2 * (2 * g + 1) - 1) ^ 2
      ≤ 2 * (2 * g + 1) ^ 4 + 2 * (2 * g + 1) ^ 3 - 3 * (2 * g + 1) + 1 := by
  nlinarith [hg, sq_nonneg g, sq_nonneg (g - 2)]

/-- **The count.**  Combining with `EpredBaseColumns.epred_after_gamma_trap`, the surviving
`k`-range is `0 ≤ k ≤ min (f − 3) ⌊f/2⌋`, which for `f ≥ 6` is `⌊f/2⌋`.  So the base carries
`⌊f/2⌋ + 2` columns rather than `f − 2`. -/
theorem epred_min_is_half {f : ℤ} (hf : 6 ≤ f) : 2 * (f - 3) ≥ f := by omega

/-! ## 5.  Non-vacuity at `N = 83`, and the sharp negative there -/

/-- The window at `f = 6` is `3007/121`, so the true `b`-count bound at `N = 83` is `y ≤ 24`. -/
theorem witness_83_true_bound :
    (23 : ℤ) * (2 * 6 - 1) ^ 2 ≤ 2 * 6 ^ 4 + 2 * 6 ^ 3 - 3 * 6 + 1 ∧
    (24 : ℤ) * (2 * 6 - 1) ^ 2 ≤ 2 * 6 ^ 4 + 2 * 6 ^ 3 - 3 * 6 + 1 ∧
    ¬ ((25 : ℤ) * (2 * 6 - 1) ^ 2 ≤ 2 * 6 ^ 4 + 2 * 6 ^ 3 - 3 * 6 + 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **`WedgeBound`'s docstring bound is strictly stronger than the truth, and wrongly so.**  It
reads `y·b² ≤ eN(b−e)`, i.e. `121y ≤ 2490`, hence `y ≤ 20`.  The true clearance gives `121y ≤ 3007`,
hence `y ≤ 24`.  The gap is exactly the apex offset the docstring drops,
`2b · (b²+c²−a²)/(2b) = b² + c² − a² = 517`; numerically `3007 − 2490 = 517`. -/
theorem wedgeBound_docstring_refuted :
    (5 : ℤ) * (3 * 6 ^ 2 - 5 ^ 2) * ((6 ^ 2 - 5 ^ 2) - 5) = 2490 ∧
    (2 * 6 ^ 4 + 2 * 6 ^ 3 - 3 * 6 + 1 : ℤ) = 3007 ∧
    (3007 : ℤ) - 2490 = ((6 ^ 2 - 5 ^ 2) ^ 2 + (6 ^ 2) ^ 2 - (5 * 6) ^ 2) ∧
    ¬ ((23 : ℤ) * (6 ^ 2 - 5 ^ 2) ^ 2 ≤ 5 * (3 * 6 ^ 2 - 5 ^ 2) * ((6 ^ 2 - 5 ^ 2) - 5)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The refuting placement, left end.**  A `b`-edge on `[71, 82]` at `(e,f) = (5,6)`, in the
chirality whose apex sits at `X = 71 + 517/22 = 2079/22`, clears **both** corners.  Since
`71 < 2075/22 = 94.3…`, the `b`-edge genuinely reaches into the zone that
`WedgeBound.b_count_bound`'s docstring declares forbidden. -/
theorem witness_83_left_placement :
    ClearsLeft 5 6 (sb 5 6) (2079 / 22) ∧ ClearsRight 5 6 (sb 5 6) (2079 / 22) ∧
    (71 : ℚ) < 2075 / 22 := by
  refine ⟨?_, ?_, by norm_num⟩ <;>
    · simp only [ClearsLeft, ClearsRight, sb, baseLen, NN]; norm_num

/-- **The refuting placement, right end — this is the correction to the research log.**  The log's
2026-08-13 band fixes one chirality and so is asymmetric about the base's midpoint `415/2`; the
mirrored tile is admissible (`Congruence.Tri.Congruent` is congruence under an arbitrary isometry).
A `b`-edge on `[333, 344]`, in the chirality that puts the apex at `X = 344 − 517/22 = 7051/22`,
clears both corners, yet its right endpoint `344` exceeds the log's limit `6780/22 = 308.18…`. -/
theorem witness_83_reflected_placement :
    ClearsLeft 5 6 (sb 5 6) (7051 / 22) ∧ ClearsRight 5 6 (sb 5 6) (7051 / 22) ∧
    (6780 : ℚ) / 22 < 344 := by
  refine ⟨?_, ?_, by norm_num⟩ <;>
    · simp only [ClearsLeft, ClearsRight, sb, baseLen, NN]; norm_num

/-- The two placements are mirror images: `2079/22 + 7051/22 = 415`, the base length.  This is the
symmetry the log's band violates. -/
theorem witness_83_mirror : (2079 : ℚ) / 22 + 7051 / 22 = 415 := by norm_num

/-- **`(3,23,2)` survives.**  It is a genuine solution of the base equation at `f = 6`, it passes
the `γ`-trap (`z = 2 ≥ 1`), it passes `cornerpara_filter` (`x + z = 5 ≥ 4`), and its `b`-count
`23` satisfies the true clearance bound.  So `N = 83` carries **four** base words after the wedge —
`(0,5,10)`, `(6,5,5)`, `(5,11,4)`, `(4,17,3)`, `(3,23,2)` minus whatever the corner rule removes —
not the three the log records. -/
theorem witness_83_23_survives :
    EpredBaseColumns.BaseEq 6 3 23 2 ∧ (1 : ℤ) ≤ 2 ∧ (4 : ℤ) ≤ 3 + 2 ∧
    (23 : ℤ) * (2 * 6 - 1) ^ 2 ≤ 2 * 6 ^ 4 + 2 * 6 ^ 3 - 3 * 6 + 1 := by
  refine ⟨by unfold EpredBaseColumns.BaseEq; norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The sharp negative at `N = 83`.**  The only column the corrected clearance excludes there is
`(2,29,1)` — and `cornerpara_filter` had already excluded it, since `x + z = 3 < 4`.  So at the one
genuinely open base-β row below `N = 110` the geometric filter adds **nothing**. -/
theorem witness_83_wedge_adds_nothing :
    ¬ ((29 : ℤ) * (2 * 6 - 1) ^ 2 ≤ 2 * 6 ^ 4 + 2 * 6 ^ 3 - 3 * 6 + 1) ∧
    ¬ ((4 : ℤ) ≤ 2 + 1) ∧
    ¬ ((35 : ℤ) * (2 * 6 - 1) ^ 2 ≤ 2 * 6 ^ 4 + 2 * 6 ^ 3 - 3 * 6 + 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## 6.  Non-vacuity of the *gain*: the first column the filter removes on its own -/

/-- **`f = 7` (`N = 111`), the column `k = 4`, i.e. `(x,y,z) = (3, 34, 2)`.**  It solves the base
equation, `z = 2 ≥ 1` passes the `γ`-trap, `x + z = 5 ≥ 4` passes `cornerpara_filter`, and
`k = 4 ≤ f − 3 = 4` passes `epred_after_gamma_trap` — so **every** filter in the corpus admits it.
Its `b`-count `34` violates the clearance bound (`34·169 = 5746 > 5468`), so the clearance kills it.
This is the witness that the new filter is not subsumed. -/
theorem witness_f7_new_kill :
    EpredBaseColumns.BaseEq 7 3 34 2 ∧ (1 : ℤ) ≤ 2 ∧ (4 : ℤ) ≤ 3 + 2 ∧ (4 : ℤ) ≤ 7 - 3 ∧
    ¬ ((34 : ℤ) * (2 * 7 - 1) ^ 2 ≤ 2 * 7 ^ 4 + 2 * 7 ^ 3 - 3 * 7 + 1) := by
  refine ⟨by unfold EpredBaseColumns.BaseEq; norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- And `k = 3` at `f = 7` survives, so the cut really is at `⌊7/2⌋ = 3`. -/
theorem witness_f7_k3_survives :
    EpredBaseColumns.BaseEq 7 4 27 3 ∧
    ((27 : ℤ) * (2 * 7 - 1) ^ 2 ≤ 2 * 7 ^ 4 + 2 * 7 ^ 3 - 3 * 7 + 1) := by
  refine ⟨by unfold EpredBaseColumns.BaseEq; norm_num, by norm_num⟩

/-- **The first prime member the filter advances**: `f = 9`, `N = 2·81 + 18 − 1 = 179`.  The old cut
is `k ≤ 6` (`f − 3`), the new one `k ≤ 4` (`⌊f/2⌋`), so the surviving column count falls from `8` to
`6`.  `k = 5` is the witness: it passes every previous filter and fails the clearance. -/
theorem witness_179 :
    (2 * 9 ^ 2 + 2 * 9 - 1 : ℤ) = 179 ∧
    EpredBaseColumns.BaseEq 9 4 53 3 ∧ (1 : ℤ) ≤ 3 ∧ (4 : ℤ) ≤ 4 + 3 ∧ (5 : ℤ) ≤ 9 - 3 ∧
    ¬ ((53 : ℤ) * (2 * 9 - 1) ^ 2 ≤ 2 * 9 ^ 4 + 2 * 9 ^ 3 - 3 * 9 + 1) := by
  refine ⟨by norm_num, by unfold EpredBaseColumns.BaseEq; norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-! ## 7.  Non-vacuity of every hypothesis used above

Rule: exhibit a witness for each hypothesis, so that no theorem here is a `False → False`. -/

/-- `ClearsLeft`'s hypothesis in the exact shape `b_edge_left_clearance` consumes it: at `(5,6)`
with left endpoint `s = 71` and apex offset `projNum b c a / (2b) = 517/22`. -/
theorem witness_clearsLeft_instantiated :
    ClearsLeft 5 6 (sb 5 6)
      ((71 : ℚ) + (projNum (sb 5 6) (sc 5 6) (sa 5 6) : ℚ) / (2 * (sb 5 6 : ℚ))) := by
  simp only [ClearsLeft, projNum, sa, sb, sc, baseLen, NN]; norm_num

/-- And the conclusion it yields is consistent and tight: `clearNum = 1558 ≤ 2·11·71 = 1562`. -/
theorem witness_clearance_conclusion :
    clearNum 5 6 (sb 5 6) (sc 5 6) (sa 5 6) = 1558 ∧ (1558 : ℤ) ≤ 2 * 11 * 71 ∧
    ¬ ((1558 : ℤ) ≤ 2 * 11 * 70) := by
  refine ⟨by simp only [clearNum, projNum, sa, sb, sc, NN]; norm_num, by norm_num, by norm_num⟩

/-- `packing`'s hypotheses are satisfiable: two `b`-edges of length `11` at `0` and `11`, window
`[0, 22]`, giving `2·11 ≤ 22 − 0`. -/
theorem witness_packing :
    ((2 : ℕ) : ℚ) * 11 ≤ 22 - 0 := by
  have := packing (b := (11:ℚ)) (d := (0:ℚ)) (W := (22:ℚ)) (by norm_num) (y := 2) (by norm_num)
    (fun i => 11 * (i : ℚ)) (by intro i _; positivity)
    (by intro i _; push_cast; ring_nf; linarith)
    (by norm_num)
  linarith [this]

/-- `b_edge_right_clearance`'s hypothesis, instantiated at the mirrored placement `[333, 344]`. -/
theorem witness_clearsRight_instantiated :
    ClearsRight 5 6 (sb 5 6)
      ((344 : ℚ) - (projNum (sb 5 6) (sc 5 6) (sa 5 6) : ℚ) / (2 * (sb 5 6 : ℚ))) := by
  simp only [ClearsRight, projNum, sa, sb, sc, baseLen, NN]; norm_num

/-- `chirality_min`'s hypothesis holds at `(5,6)`: `a² = 900 ≤ 1296 = c²`. -/
theorem witness_chirality : sa 5 6 ^ 2 ≤ sc 5 6 ^ 2 := by
  simp only [sa, sc]; norm_num

end Erdos634.EpredWedgeClearance
