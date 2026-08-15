import Mathlib.Tactic

/-!
# The corridor below `e`: no stop, and a single flush that the exit kills

Erdős #634, base-`β` branch, the deep-scale rogue obstruction.

Setting.  Tile `(a,b,c) = (ef, f²−e², f²)`, `2 ≤ e < f`, `gcd(e,f) = 1`.  At a deep slot the rogue
forces a two-sided corridor of length `r·c` along chord 2, whose rogue side is an edge-union
starting with an `a` (the leftmost-rogue reduction).  The corridor can end in exactly two ways: it
**flushes** at the exit `E` (the far end, on the `a`-side `BC`), or it **stops** at an interior
point where *both* sides break.  Either way the terminating height `h` satisfies

    (x+1)·a + y·b + z·c = h,   x, y, z ≥ 0,

with `h = r·c` for the flush and `h = m·c` for a stop at a row breakpoint (the row side of the
corridor reads its `c`-edges, so its breakpoints are the multiples of `c`).

`corridor_low` decides that equation for every `m ≤ e`:

* **no solution for `m < e`** — nothing below `e·c` is reachable from an `a`;
* **exactly one solution at `m = e`**, namely `a^f` (`x+1 = f`, `y = z = 0`).

The proof is a two-step descent with a squeeze that needs no size hypothesis beyond `e < f`.
Reducing mod `f` gives `y = fY`; reducing the quotient mod `f` again gives `x+1 = Ye − tf`, and the
equation then forces `z = m − Yf + te`.  Non-negativity plus `m ≤ e` gives `Yf ≤ e(1+t)` and
`Ye ≥ tf+1`.  If `Y ≥ 1` then `t ≥ 1` (else `z < 0`), and the two bounds read `t < Y` and `Y < 1+t`
simultaneously — impossible for integers.  So `Y = 0`, `f ∣ x+1`, and `e·j ≤ m ≤ e` pins `j = 1`.

**Consequence (the `r = e` cell kill).**  At a deep slot with `r = e` and `k < f`:

* the only reachable multiple of `c` in `(0, r·c]` is `m = e = r` — the exit itself, so the corridor
  has **no interior stop**;
* the unique flush word there is `a^f`, which has no trailing `c`, and every `c`-free flush dies at
  `E` against `Inflation.a_side_rigid` (the exit fan puts an `α`-tile on `BC`, whose flanks are
  `{b,c}`, contradicting the `a^k` reading of `BC`) — `code/strip_exit.py`, 963/963.

A corridor with neither a stop nor a surviving flush cannot terminate, so the rogue configuration
does not exist.  The kill is uniform in `(e, f, M)`: no member hypothesis, no scale bound beyond
`k < f`, and in particular it does not stop at `f ≤ 12`.

Numerics before proving: `code/strip_exit.py` (963/963 over 36 deep cells, `f ∈ [13,30]`) and the
classification sweep in this session — 2 915 triples `(e,f,m)`, all coprime `(e,f)` with `f ≤ 25`
and `e ≥ 2`, zero failures.

Axiom-clean.
-/

namespace Erdos634.CorridorLowStop

/-- **The descent.**  Reducing the corridor equation mod `f` twice produces the parametrisation
`y = fY`, `x+1 = Ye − tf`, `z = m − Yf + te`.  This lemma records that the parametrisation *solves*
the equation, i.e. the descent is exact. -/
theorem descent_solves (e f m Y t : ℤ) :
    ((Y * e - t * f) * (e * f) + (f * Y) * (f ^ 2 - e ^ 2)
      + (m - Y * f + t * e) * f ^ 2) = m * f ^ 2 := by ring

/-- **The squeeze — general form.**  Non-negativity of the three counts forces `Y = 0` for every
`m < f`.  No size hypothesis beyond `e < f` is used.

`Y ≥ 1` forces `t ≥ 1` (else `z < 0`, since `Yf ≥ f > m`).  Then `Ye ≥ tf+1 > te` gives `Y > t`,
so `Y ≥ t+1` and `Yf ≥ tf + f`; but `z ≥ 0` with `m < f` gives `Yf ≤ m + te < f + te`.  Together
`tf < te`, i.e. `f < e` — contradiction. -/
theorem squeeze_Y_zero (e f m Y t : ℤ) (he : 2 ≤ e) (hef : e < f) (hmf : m < f)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ m - Y * f + t * e) : Y = 0 := by
  by_contra hne
  have hY1 : 1 ≤ Y := by omega
  have hf0 : 0 < f := by omega
  -- Yf < f + te, from z ≥ 0 and m < f
  have hub : Y * f < f + t * e := by nlinarith
  -- t ≥ 1: else te ≤ 0 and Yf ≥ f contradict hub
  have ht1 : 1 ≤ t := by nlinarith
  -- Y > t: from Ye ≥ tf + 1 and f > e
  have hgt : t < Y := by nlinarith
  -- Y ≥ t+1 gives Yf ≥ tf + f; with hub, tf < te, i.e. f < e
  nlinarith

/-- **The classification below `e`.**  For `m ≤ e`, the only solution of the corridor equation is
`m = e` with the word `a^f`.  In particular nothing is reachable below height `e·c`. -/
theorem corridor_low (e f m Y t : ℤ) (he : 2 ≤ e) (hef : e < f) (hm : 0 < m) (hme : m ≤ e)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ m - Y * f + t * e) :
    m = e ∧ Y * e - t * f = f ∧ Y = 0 ∧ m - Y * f + t * e = 0 := by
  have hY0 : Y = 0 := squeeze_Y_zero e f m Y t he hef (by omega) hY hx hz
  subst hY0
  -- x+1 = −tf ≥ 1 forces t ≤ −1; write j = −t ≥ 1
  have ht : t ≤ -1 := by nlinarith
  -- z = m + te ≥ 0 with m ≤ e forces t = −1 and m = e
  have hj : t = -1 := by nlinarith
  subst hj
  refine ⟨by omega, by ring_nf, rfl, by omega⟩

/-- **The full classification.**  For every `m < f`, the solutions of the corridor equation are
exactly the family `a^{jf} c^{m-je}` with `j ≥ 1` and `je ≤ m`: the `b`-count vanishes, `f ∣ x+1`,
and the `c`-tail is `m - je`.  Uniform in `(e,f)` — the only hypotheses are `2 ≤ e < f` and `m < f`.

This is the arithmetic backbone of the corridor analysis: it gives the flush words (`m = r`), the
reachable stop heights (`m·c` for `e ≤ m`), and hence the fact that nothing below `e·c` is
reachable from an `a` at all. -/
theorem classification (e f m Y t : ℤ) (he : 2 ≤ e) (hef : e < f) (hmf : m < f)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ m - Y * f + t * e) :
    Y = 0 ∧ 1 ≤ -t ∧ (-t) * e ≤ m ∧ Y * e - t * f = (-t) * f
      ∧ m - Y * f + t * e = m - (-t) * e := by
  have hY0 : Y = 0 := squeeze_Y_zero e f m Y t he hef hmf hY hx hz
  subst hY0
  have hf0 : 0 < f := by omega
  have ht : t ≤ -1 := by nlinarith
  refine ⟨rfl, by omega, by nlinarith, by ring, by ring⟩

/-- **Nothing below `e·c` is reachable.**  `m < e` admits no solution — a direct corollary of the
classification, since `je ≤ m < e` with `j ≥ 1` is impossible. -/
theorem unreachable_below_e (e f m Y t : ℤ) (he : 2 ≤ e) (hef : e < f) (hme : m < e)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ m - Y * f + t * e) : False := by
  have h := classification e f m Y t he hef (by omega) hY hx hz
  nlinarith [h.2.1, h.2.2.1]

/-- **No stop below the exit at `r = e`.**  Taking `m < e`: the equation has no solution at all,
so the corridor cannot stop at any interior multiple of `c`. -/
theorem no_stop_below_e (e f m Y t : ℤ) (he : 2 ≤ e) (hef : e < f) (hm : 0 < m) (hme : m < e)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ m - Y * f + t * e) : False := by
  have := corridor_low e f m Y t he hef hm (by omega) hY hx hz
  omega

/-- **The unique flush at `r = e` is `c`-free.**  Its trailing `c`-count is `0`, which is the
hypothesis of the exit kill: the exit fan then puts an `α`-tile against `BC`, and `α`'s flanks are
`{b, c}`, contradicting `Inflation.a_side_rigid`'s `a^k` reading of `BC` for `k < f`. -/
theorem flush_at_e_is_c_free (e f Y t : ℤ) (he : 2 ≤ e) (hef : e < f)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ e - Y * f + t * e) :
    e - Y * f + t * e = 0 ∧ Y * e - t * f = f :=
  ⟨(corridor_low e f e Y t he hef (by omega) le_rfl hY hx hz).2.2.2,
   (corridor_low e f e Y t he hef (by omega) le_rfl hY hx hz).2.1⟩

/-! ## The cell kill

Assembling: at a deep slot with `r = e` and `k < f`, the corridor's terminating height `h` is a
multiple of `c`, say `h = m·c` with `1 ≤ m ≤ r = e`.

* `m < e` — impossible by `no_stop_below_e`;
* `m = e` — the flush, whose unique word is `c`-free by `flush_at_e_is_c_free`, and dies at the
  exit against `a_side_rigid`.

No terminating height survives, so the rogue slot does not occur.  Uniform in `(e,f,M)`.

The geometric inputs, all named and all standing: the corridor's two sides are edge-unions of the
same segment with equal totals (`WallChain.wall_two_sided`, **proved**); the row side's breakpoints
are the multiples of `c` (the forced row, `sub:forcedrow`); the rogue side begins with an `a`
(leftmost-rogue reduction); and the exit fan at `E` (`code/strip_exit.py`, 963/963), which consumes
`Inflation.a_side_rigid` and `Inflation.a_side_no_b`. -/

/-- The scale range in which the kill applies: `k < f`, so `a_side_rigid` licenses the `a^k`
reading of `BC` that the exit fan contradicts. -/
theorem kill_scope (k f : ℤ) (h : k < f) : k ≤ f - 1 := by omega

/-! ## The forced `a`-run, and the room it needs

The classification decides the corridor's *first* common breakpoint, uniformly in `(e,f)` and for
every `r ≥ e`.  The row side of the corridor breaks exactly at the multiples of `c` (the forced
row, `sub:forcedrow`), so a common breakpoint sits at a height `m·c`; `unreachable_below_e` rules
out every `m < e`, and `corridor_low` says the unique word at `m = e` is `a^f`.  Moreover every
flush word `a^{jf} c^{r-je}` *does* break at `e·c`, because `f·a = e·c` — after exactly `f` of its
`a`-edges.  Hence:

> **For every deep rogue with `r ≥ e`, the first common breakpoint is at height `e·c`, and the
> rogue word begins with exactly `f` consecutive `a`-edges.**

Verified before proving: 13 119 flush words over all coprime `(e,f)` with `f ≤ 40`, `e ≥ 2`, every
`r` and `j` in range — the minimum multiple-of-`c` prefix is `e·c` in every case, reached after
exactly `f` letters, zero failures.

That `a`-run forces the strip `[0, e·c] × [0, c]` (the `R_i D_i` parallelogram chain).  Its room in
the `AB` direction is `M·a`, so the strip fits iff `c ≤ M·a`, i.e. `f ≤ M·e` — always true at a
deep slot.  A **second** strip needs `2c ≤ M·a`, i.e. `2f ≤ M·e`, and at `e = 2` that reads
`f ≤ M`, which a deep slot (`M ≤ f-2`) never satisfies. -/

/-- The `a`-run spans exactly `e` units of `c`: `f·a = e·c`.  This is why the run's far end is a row
breakpoint, and why the strip it forces has width `e·c`. -/
theorem a_run_span (e f : ℤ) : f * (e * f) = e * f ^ 2 := by ring

/-- **The first common breakpoint.**  No multiple of `c` below `e·c` is reachable, and at `e·c` the
word is exactly `a^f`.  Uniform in `(e,f)`; the two halves are `unreachable_below_e` and
`corridor_low`. -/
theorem first_stop_is_ec (e f m Y t : ℤ) (he : 2 ≤ e) (hef : e < f) (hm : 0 < m) (hme : m ≤ e)
    (hY : 0 ≤ Y) (hx : 1 ≤ Y * e - t * f) (hz : 0 ≤ m - Y * f + t * e) :
    m = e ∧ Y * e - t * f = f ∧ Y = 0 ∧ m - Y * f + t * e = 0 :=
  corridor_low e f m Y t he hef hm hme hY hx hz

/-- **The strip fits.**  `c ≤ M·a ↔ f ≤ M·e`, and a deep slot has `M·e > f`: with
`M ≥ ⌊f/e⌋ + 2 ≥ (f - e + 1)/e + 2` one gets `M·e ≥ f + e + 1`. -/
theorem strip_fits (e f M : ℤ) (hf : 0 < f) : f ^ 2 ≤ M * (e * f) ↔ f ≤ M * e := by
  constructor <;> intro h <;> nlinarith

/-- **No second strip at `e = 2`.**  `2c ≤ M·a` reads `f ≤ M`, which a deep slot never satisfies:
`M ≤ f - 2 < f`.  So at every `e = 2` member and every deep slot, the strip tower cannot reach a
second level — the second strip would cross `AB`. -/
theorem no_second_strip_e2 (f M : ℤ) (hf : 0 < f) (hM : M ≤ f - 2) :
    ¬ (2 * f ^ 2 ≤ M * (2 * f)) := by
  intro h; nlinarith

/-- The same obstruction in its general shape: a second strip needs `2f ≤ M·e`, so with `M ≤ f-2`
it needs `2(f + e) ≤ e·f`.  At `e = 2` the left side exceeds the right for every `f`. -/
theorem second_strip_needs (e f M : ℤ) (he : 0 ≤ e) (hM : M ≤ f - 2) (h : 2 * f ≤ M * e) :
    2 * f + 2 * e ≤ e * f := by nlinarith [mul_le_mul_of_nonneg_right hM he]

/-! ## The level-1 corridor: a strict dichotomy

The forced `a`-run carries a strip `[0, e·c] × [0, c]` whose **top** reads `a^f`.  That top is a
two-sided wall of its own — the *level-1 corridor* — of the same length `e·c = f·a`, but its lower
side now breaks at the multiples of `a`, not of `c`.  Its upper word `W` begins at the mast with the
forced tile `T₁`, whose flanks are `{a, c}`, so `W` starts with an `a` or with a `c`.

* `W` starts with `a`: its first partial sum is `a`, already on the `a`-grid — the corridor stops
  immediately and nothing is forced.
* `W` starts with `c`: `level1_dichotomy` below says it meets the `a`-grid **only at the far end**,
  and the word is then exactly `c^e`.

So the level-1 corridor admits no interior stop in the `c`-branch: it runs the full `e·c` and reads
`c^e`.  Verified before proving: all 450 coprime members with `f ≤ 40`, `e ≥ 2`; in every one the
only `i ∈ [1,f]` with `c + xa + yb + zc = i·a` solvable is `i = f`, zero failures.

The descent is the same as before — `y = fY`, `z+1 = eT - Yf`, `x = i + Ye - Tf` — and the squeeze
is sharper: `T = 1` forces `Y = 0` (since `Yf ≤ e-1 < f`), while `T ≥ 2` forces `Y ≥ T` (from
`Ye ≥ (T-1)f > (T-1)e`) and hence `Tf ≤ Yf ≤ eT - 1`, i.e. `T(f-e) ≤ -1`, impossible. -/

/-- **The level-1 dichotomy.**  A `c`-started word on the level-1 corridor meets the `a`-grid only
at the far end `i = f`, where it reads `c^e` (`x = y = 0`, `z = e-1`).  Uniform in `(e,f)`. -/
theorem level1_dichotomy (e f i Y T : ℤ) (he : 2 ≤ e) (hef : e < f) (hi1 : 1 ≤ i) (hif : i ≤ f)
    (hY : 0 ≤ Y) (hz : 1 ≤ e * T - Y * f) (hx : 0 ≤ i + Y * e - T * f) :
    Y = 0 ∧ T = 1 ∧ i = f ∧ e * T - Y * f = e := by
  have hf0 : 0 < f := by omega
  have hT1 : 1 ≤ T := by nlinarith
  rcases eq_or_lt_of_le hT1 with hT | hT2
  · -- T = 1 : Yf ≤ e - 1 < f forces Y = 0, then x ≥ 0 with i ≤ f pins i = f
    have hTeq : T = 1 := hT.symm
    subst hTeq
    have hYf : Y * f ≤ e - 1 := by linarith
    have hY0 : Y = 0 := by nlinarith
    subst hY0
    refine ⟨rfl, rfl, by omega, by ring⟩
  · -- T ≥ 2 : Y ≥ T, so Tf ≤ Yf ≤ eT - 1, i.e. T(f-e) ≤ -1
    exfalso
    have hT2' : 2 ≤ T := hT2
    have hlo : (T - 1) * f ≤ Y * e := by nlinarith
    have hYT : T ≤ Y := by nlinarith
    nlinarith

/-- The far-end word of the `c`-branch has exactly `e` letters, all `c`: its total is `e·c = f·a`,
the full length of the level-1 corridor. -/
theorem level1_word_span (e f : ℤ) : e * f ^ 2 = f * (e * f) := by ring

/-! ## The mast's room forces the branch at `e = 2`

The mast is the wall at `s = 0` rising from `Y`, of length at most the `AB`-room `M·a`.  Its right
side reads the rogue's `c`-edge, then `T₁, T₂, …`, each laying an `a` or a `c`; its left side opens
with `P_M`'s riser `a`-edge.  A common stop at height `h` needs `h ∈ a + ⟨a,b,c⟩`, and the
classification decides which multiples of `c` qualify: `h = m·c` is reachable iff `m ≥ e`, while
`h = n·c + a` is always reachable (`a + n·c`).

So if the mast's right side reads `c^n` before its first `a`, the first common stop sits at `n·c`
when `n ≥ e`, and at `n·c + a` otherwise.  Either way it must fit under `AB`.

At **`e = 2`** this decides the branch outright.  `n ≥ 2` means `n ≥ e`, so the stop is at `2c`,
needing `2c ≤ M·a`, i.e. `f ≤ M` — false at a deep slot (`M ≤ f-2`).  And `n = 1` puts the stop at
`c + a`, which does fit.  Hence `n = 1`: **`T₁` lays its `a` on the mast and its `c` on the level-1
corridor**, so by `level1_dichotomy` the level-1 word is forced to `c²`.

Verified before proving: every odd `f` from 5 to 59 and every deep `M` — `n ≥ 2` never fits, `n = 1`
always does; zero violations. -/

/-- **The mast stop must fit.**  A first common stop at `n·c` (the `n ≥ e` case) needs
`n·f ≤ M·e`; at `n·c + a` (the `n < e` case) it needs `n·f + e ≤ M·e`. -/
theorem mast_stop_room (e f M n : ℤ) (hf : 0 < f) :
    (n * f ^ 2 ≤ M * (e * f) ↔ n * f ≤ M * e)
      ∧ (n * f ^ 2 + e * f ≤ M * (e * f) ↔ n * f + e ≤ M * e) := by
  constructor <;> constructor <;> intro h <;> nlinarith

/-- **At `e = 2` a `c`-run of length `≥ 2` on the mast is impossible.**  Its stop would sit at `2c`,
demanding `f ≤ M`, which a deep slot never allows. -/
theorem mast_c_run_le_one (f M n : ℤ) (hf : 0 < f) (hM : M ≤ f - 2) (hn : 2 ≤ n) :
    ¬ (n * f ^ 2 ≤ M * (2 * f)) := by
  intro h; nlinarith

/-- **The `n = 1` stop fits.**  `c + a ≤ M·a` at `e = 2` reads `f + 2 ≤ 2M`, which every deep slot
satisfies since `M ≥ ⌊f/2⌋ + 2`. -/
theorem mast_n_one_fits (f M : ℤ) (hf : 0 < f) (hM : f + 2 ≤ 2 * M) :
    f ^ 2 + 2 * f ≤ M * (2 * f) := by nlinarith

/-- **The branch is forced at `e = 2`.**  Combining: the mast's `c`-run before its first `a` has
length exactly one, so `T₁` lays `a` on the mast and `c` on the level-1 corridor.  With
`level1_dichotomy` the level-1 word is then `c²`, with no interior stop. -/
theorem branch_forced_e2 (f M n : ℤ) (hf : 0 < f) (hM : M ≤ f - 2) (hn1 : 1 ≤ n)
    (hfit : n * f ^ 2 ≤ M * (2 * f)) : n = 1 := by
  by_contra hne
  exact mast_c_run_le_one f M n hf hM (by omega) hfit

end Erdos634.CorridorLowStop

#print axioms Erdos634.CorridorLowStop.mast_stop_room
#print axioms Erdos634.CorridorLowStop.mast_c_run_le_one
#print axioms Erdos634.CorridorLowStop.branch_forced_e2
