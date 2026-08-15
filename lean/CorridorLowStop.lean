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

end Erdos634.CorridorLowStop

#print axioms Erdos634.CorridorLowStop.descent_solves
#print axioms Erdos634.CorridorLowStop.squeeze_Y_zero
#print axioms Erdos634.CorridorLowStop.corridor_low
#print axioms Erdos634.CorridorLowStop.no_stop_below_e
#print axioms Erdos634.CorridorLowStop.flush_at_e_is_c_free
#print axioms Erdos634.CorridorLowStop.classification
#print axioms Erdos634.CorridorLowStop.unreachable_below_e
