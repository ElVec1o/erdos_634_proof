-- ChordDecomp.lean — the arithmetic core of the chord decomposition at the last junction of an
-- equal side at (3,7).
--
-- The companion's `prop:chorddecomp` says: let `C` be the chord through the last junction `J`, and
-- let `𝒰` be the tiles whose interiors meet the open half-plane above `C`. Each such tile either
-- STRADDLES `C` or is FLUSH from above; a flush tile meets the line of `C` in a full tile edge; the
-- traces cover `C` with pairwise disjoint interiors. From that data the flush total is confined to
-- `{0,21,40,42,49}`, at most two tiles are flush, at least one straddles, and at least two straddle
-- when none is flush.
--
-- SCOPE. The geometry — that the traces cover `C`, that they have disjoint interiors, and that a
-- flush trace is a whole tile edge — is NOT proved here. It is carried as the fields of
-- `ChordTrace`, in the style of `ChordInterface.FarSide`: the obligation is named rather than
-- hidden, and the corpus keeps its zero-`sorry` property. The supporting-line step behind "a flush
-- trace is a whole edge" is `Erdos634.Geometry.contact_is_edge`, already proved in `Dissection.lean`.
-- STATUS UPDATE (2026-08-15): the one-dimensional covering statement is now proved for WALL
-- segments (`WallChain.wall_partition` / `wall_two_sided`), and flush-flush disjointness is
-- `EdgeChain.Dissection.sameside_edges_subsingleton` (two tiles flush from the same side cannot
-- overlap on the line). What remains named for THIS chord — which is straddled, not a wall — is
-- the mixed flush/straddle covering: the dichotomy (a tile meeting the line either straddles,
-- with its trace's relative interior inside the tile's interior, or contacts in a face) and the
-- one-dimensional additivity across straddler traces.
--
-- Per the project rule the corpus was surveyed first. `ChordInterface.lean` carries the far side of a
-- BLOCKED chord (a run of edges laid end to end from a blocked end, with no relation asserted between
-- the run's total and the edge length); this file carries the trace of a HORIZONTAL chord, where the
-- total is pinned to the chord length `414/7`. The two data are different and neither subsumes the
-- other. `Dissection.lean` has the supporting-line lemma but no chord arithmetic.

import Mathlib.Tactic

namespace Erdos634.ChordDecomp

/-! ## The area defect

The chord through a junction at distance `d = 21i + 49j` from the apex cuts off a triangle similar to
the target with ratio `ρ = (3i+7j)/49`, of area `138 ρ²` in tile units. Writing `n = 3i+7j`, this is
`138 n² / 2401`, and it is never a whole number of tiles for a junction strictly inside the side. -/

/-- **The area above a junction chord is never an integral number of tiles.**  `2401 = 7⁴` and
`138 = 2·3·23` are coprime, so `2401 ∣ 138 n²` forces `7⁴ ∣ n²`, i.e. `49 ∣ n`, which is impossible
for `1 ≤ n ≤ 48`.  This is the companion's `prop:straddle`. -/
theorem area_not_integral (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 48) : ¬ (2401 ∣ 138 * n ^ 2) := by
  interval_cases n <;> decide

/-- The admissible junction heights are `n = 3i + 7j`; every one of them strictly between the apex
and the base satisfies the hypotheses of `area_not_integral`. -/
theorem admissible_range {i j : ℕ} (hi : i ≤ 7) (hj : j ≤ 4)
    (hpos : 1 ≤ 3 * i + 7 * j) (hlt : 3 * i + 7 * j < 49) :
    ¬ (2401 ∣ 138 * (3 * i + 7 * j) ^ 2) :=
  area_not_integral _ hpos (by omega)

/-! ## The trace of the chord

`414/7` is the length of the chord through the last junction: the junction sits at height fraction
`6/7` of the way up an equal side, so the chord is `(1 - 6/7)` of the base `414`. -/

/-- **The trace datum of the chord at the last junction.**  `flush` records the lengths of the traces
of the tiles lying weakly above the chord — each a whole tile edge — and `straddle` the lengths of the
cross-sections of the tiles meeting both open sides.  Together they tile the chord.

The three side lengths at `(3,7)` are `a = 21`, `b = 40`, `c = 49`; `49` is also the diameter of the
tile, so it bounds every segment contained in a tile. -/
structure ChordTrace where
  /-- lengths of the flush traces, each a whole tile edge -/
  flush : List ℕ
  /-- lengths of the straddling cross-sections -/
  straddle : List ℚ
  /-- a flush trace is a whole tile edge -/
  isSide : ∀ l ∈ flush, l = 21 ∨ l = 40 ∨ l = 49
  /-- a straddling cross-section has positive length -/
  straddle_pos : ∀ x ∈ straddle, 0 < x
  /-- a segment inside a tile is at most the tile's diameter, its longest side -/
  straddle_le : ∀ x ∈ straddle, x ≤ 49
  /-- the traces are disjoint and cover the chord -/
  covers : (flush.sum : ℚ) + straddle.sum = 414 / 7

/-- Every entry of a flush list is at least `21`, so the list is short. -/
theorem sum_ge_len (L : List ℕ) (h : ∀ l ∈ L, l = 21 ∨ l = 40 ∨ l = 49) :
    21 * L.length ≤ L.sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons, List.length_cons]
    rcases ha with rfl | rfl | rfl <;> omega

/-- The flush total is a natural number bounded by the chord length. -/
theorem flush_sum_le (C : ChordTrace) : C.flush.sum ≤ 59 := by
  have hs : (0 : ℚ) ≤ C.straddle.sum := by
    refine List.sum_nonneg ?_
    exact fun x hx => (C.straddle_pos x hx).le
  have hle : (C.flush.sum : ℚ) ≤ 414 / 7 := by
    have := C.covers; linarith
  by_contra hcon
  push_neg at hcon
  have : (60 : ℚ) ≤ (C.flush.sum : ℚ) := by exact_mod_cast hcon
  linarith

/-- **At most two tiles are flush, and the flush total is one of five values.**  This is parts (c)
of the companion's `prop:chorddecomp`: already `21 + 40 = 61` and `21+21+21 = 63` exceed the chord. -/
theorem flush_classification (C : ChordTrace) :
    C.flush.length ≤ 2 ∧
      (C.flush.sum = 0 ∨ C.flush.sum = 21 ∨ C.flush.sum = 40 ∨ C.flush.sum = 42
        ∨ C.flush.sum = 49) := by
  have hsum := flush_sum_le C
  have hlen : C.flush.length ≤ 2 := by
    have := sum_ge_len C.flush C.isSide; omega
  refine ⟨hlen, ?_⟩
  rcases hfl : C.flush with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp
  · have ha := C.isSide a (by simp [hfl])
    rw [hfl] at hsum
    simp only [List.sum_cons, List.sum_nil] at hsum ⊢
    rcases ha with rfl | rfl | rfl <;> omega
  · have ha := C.isSide a (by simp [hfl])
    have hb := C.isSide b (by simp [hfl])
    rw [hfl] at hsum
    simp only [List.sum_cons, List.sum_nil] at hsum ⊢
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> omega
  · rw [hfl] at hlen; simp at hlen

/-- **At least one tile straddles.**  A second proof of `prop:straddle`, by length rather than area:
the flush total is an integer and the chord length `414/7` is not, so the straddling part is nonzero. -/
theorem straddle_ne_nil (C : ChordTrace) : C.straddle ≠ [] := by
  intro h
  have hc := C.covers
  rw [h] at hc
  simp only [List.sum_nil, add_zero] at hc
  have h7 : (7 : ℚ) * (C.flush.sum : ℚ) = 414 := by rw [hc]; ring
  have hnat : 7 * C.flush.sum = 414 := by exact_mod_cast h7
  omega

/-- **If no tile is flush, at least two straddle.**  The cross-sections then have to cover the whole
chord `414/7 = 59.14…`, and each is at most the tile's diameter `49`. -/
theorem two_straddlers_of_no_flush (C : ChordTrace) (hf : C.flush = []) :
    2 ≤ C.straddle.length := by
  have hc := C.covers
  rw [hf] at hc
  simp only [List.sum_nil, Nat.cast_zero, zero_add] at hc
  by_contra hcon
  push_neg at hcon
  rcases hst : C.straddle with _ | ⟨x, _ | ⟨y, t⟩⟩
  · rw [hst] at hc; simp at hc; linarith
  · have hx := C.straddle_le x (by simp [hst])
    rw [hst] at hc
    simp only [List.sum_cons, List.sum_nil, add_zero] at hc
    rw [hc] at hx; linarith
  · rw [hst] at hcon; simp at hcon

/-- **The straddling total, given the flush total.**  Packaged for the S4 rung: the cross-sections
must sum to exactly the chord minus an element of `{0,21,40,42,49}`. -/
theorem straddle_sum_values (C : ChordTrace) :
    C.straddle.sum = 414 / 7 ∨ C.straddle.sum = 414 / 7 - 21 ∨ C.straddle.sum = 414 / 7 - 40
      ∨ C.straddle.sum = 414 / 7 - 42 ∨ C.straddle.sum = 414 / 7 - 49 := by
  have hc := C.covers
  rcases (flush_classification C).2 with h | h | h | h | h <;> rw [h] at hc <;> push_cast at hc
  · left; linarith
  · right; left; linarith
  · right; right; left; linarith
  · right; right; right; left; linarith
  · right; right; right; right; linarith


/-! ## The general form

The `(3,7)` statement above is a special case. A junction at distance `d = i·a + j·c = f(ie+jf)` from
the apex has height fraction `ρ = m/f²` with `m = ie + jf`, so the area above its chord is `N·m²/f⁴`
tile areas. If `gcd(N,f) = 1` this is an integer only when `f² ∣ m`, which fails for `1 ≤ m < f²`.

For a base-β member `gcd(N,f) = gcd(3f²−e², f) = gcd(e², f)`, so coprimality of `e` and `f` suffices —
and on the tight subfamily `f = 2e+1` it is automatic, since `gcd(e, 2e+1) = 1`. -/

/-- **The area above an interior junction chord is never an integral number of tiles.**  General form:
`N` coprime to `f`, and `1 ≤ m < f²`. -/
theorem area_never_integral {N f m : ℕ} (hf : 0 < f) (hcop : Nat.Coprime N f)
    (h1 : 1 ≤ m) (h2 : m < f ^ 2) : ¬ (f ^ 4 ∣ N * m ^ 2) := by
  intro hdvd
  have hcop4 : Nat.Coprime (f ^ 4) N := (hcop.symm.pow_left 4)
  have hdvd2 : f ^ 4 ∣ m ^ 2 := (Nat.Coprime.dvd_of_dvd_mul_left hcop4 hdvd)
  have hsq : (f ^ 2) ^ 2 ∣ m ^ 2 := by
    have : (f ^ 2) ^ 2 = f ^ 4 := by ring
    rwa [this]
  have hfm : f ^ 2 ∣ m := (Nat.pow_dvd_pow_iff (by norm_num)).mp hsq
  have : f ^ 2 ≤ m := Nat.le_of_dvd (by omega) hfm
  omega

/-- On the tight subfamily the coprimality hypothesis is automatic. -/
theorem coprime_tight (e : ℕ) : Nat.Coprime e (2 * e + 1) := by
  have h : Nat.Coprime e (1 + 2 * e) :=
    (Nat.coprime_add_mul_right_right e 1 2).mpr (Nat.coprime_one_right e)
  have heq : 1 + 2 * e = 2 * e + 1 := by ring
  rwa [heq] at h

end Erdos634.ChordDecomp
