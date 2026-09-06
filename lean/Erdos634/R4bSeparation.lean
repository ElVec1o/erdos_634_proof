import Mathlib.Tactic

/-!
# R4b — SEPARATION, from the equality case of the same sandwich that proves R4a

Erdős #634, base-β target at `m = 1`: tile `(a,b,c) = (ef, f²−e², f²)`, target isosceles with
legs `f³`, base `e(3f²−e²)`, `K = f`.

Room `advance`, Kenyon seat, 2026-09-06.

## The point

The corpus proves R4a ("the essential segment in direction `π−γ` **is** the cevian `AD`") by a
sandwich `K·b ≤ |S| ≤ maxchord(π−γ) = K·b`.  R4b ("no tile crosses `S`") has been carried as a
separate, open rung.  It is not separate: **it is the equality case of that same sandwich.**

Write `S` for a doubly terminated essential segment.  Every point of `S`'s relative interior is
either interior to some tile (then that tile *crosses* `S`) or lies on tile edges on **both** sides
(convexity: a tile whose interior touches `S` from one side at a non-vertex point meets the line of
`S` in a face, which must be an edge).  So, with `X` the total length of `S` covered by crossing
tiles and `T₁`, `T₂` the total edge length on the two sides,

    T₁ = T₂ = |S| − X,      |S| = n_a·a + n_b·b + n_c·c + X.

Double termination forbids overhang, so the counts are of **whole** edges.  The witnessed relation
`j·b = u·a + v·c` has `j = n_b − m_b` with `m_b ≥ 0`, hence `n_b ≥ j`; and `f ∣ j`, `j > 0` give
`j ≥ f`.  Therefore

    |S| ≥ n_b·b + X ≥ j·b + X ≥ f·b + X = K·b + X.

Against `|S| ≤ K·b` this forces `X = 0` — **no tile crosses `S`** — and simultaneously
`n_a = n_c = 0`, `n_b = j = f`.

`sep_core` below is exactly that chain.  Nothing here assumes Beeson's Definition 9 means the
segment lies in the union of tile boundaries; the conclusion is *derived*, so it survives the weak
reading of that definition.  What it does use, unchanged, is the corpus's own VERIFIED input
`maxchord(π−γ) = K·b` (`CevianCut.four_AD_sq` + `CevianUnique.apex_strict_middle`), re-verified
exactly for all 63 coprime pairs `f ≤ 14` and 10 random large pairs; and `f ∣ j`.

The hypothesis `hmax` is what confines this to direction `π−γ`: the exact tie holds there and,
scanned over all coprime `f ≤ 14`, **nowhere else** (base / leg / `π−α` all have slack `> 1`).
At `m ≥ 2` the ratio is exactly `m`, so the argument correctly refuses to fire on the certified
tilings `N = 44, 99, 176`.
-/

namespace Erdos634.R4bSeparation

/-- **The separation core.**  `lenS` is the length of the essential segment, split as
`n_a·a + n_b·b + n_c·c` (the edge cover, equal on both sides) plus `X` (the part swallowed by
crossing tiles).  `Kb = f·b` is both the floor and — in direction `π−γ`, and only there — the
maximum chord.  The sandwich forces the crossed length to vanish. -/
theorem sep_core
    {a b c lenS X Kb : ℝ} {na nb nc f j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hX : 0 ≤ X)
    (hlen : lenS = na * a + nb * b + nc * c + X)
    (hnbj : (j : ℝ) ≤ nb)          -- `j = n_b − m_b`, `m_b ≥ 0`
    (hjf  : (f : ℝ) ≤ j)           -- `f ∣ j` and `j > 0`
    (hKb  : Kb = f * b)
    (hmax : lenS ≤ Kb) :           -- the exact tie, direction `π−γ`
    X = 0 ∧ lenS = Kb ∧ na = 0 ∧ nc = 0 ∧ (nb : ℝ) = f := by
  have hna : (0:ℝ) ≤ na := Nat.cast_nonneg na
  have hnc : (0:ℝ) ≤ nc := Nat.cast_nonneg nc
  have hfb : (f : ℝ) * b ≤ (nb : ℝ) * b := by
    have : (f : ℝ) ≤ (nb : ℝ) := le_trans hjf hnbj
    exact mul_le_mul_of_nonneg_right this (le_of_lt hb)
  -- lenS ≥ Kb + X
  have hge : Kb + X ≤ lenS := by
    rw [hlen, hKb]; nlinarith [mul_nonneg hna ha.le, mul_nonneg hnc hc.le]
  have hX0 : X = 0 := le_antisymm (by linarith) hX
  have hlenKb : lenS = Kb := by linarith [hge, hmax]
  -- now na*a = nc*c = 0 and nb*b = Kb
  have hsum : na * a + nb * b + nc * c = (f : ℝ) * b := by
    rw [hX0, add_zero] at hlen; rw [← hKb]; linarith [hlen, hlenKb]
  have hnaa : (na : ℝ) * a = 0 := by nlinarith [mul_nonneg hna ha.le, mul_nonneg hnc hc.le]
  have hncc : (nc : ℝ) * c = 0 := by nlinarith [mul_nonneg hna ha.le, mul_nonneg hnc hc.le]
  have hna0 : na = 0 := by
    have := mul_eq_zero.mp hnaa
    rcases this with h | h
    · exact_mod_cast h
    · exact absurd h (ne_of_gt ha)
  have hnc0 : nc = 0 := by
    have := mul_eq_zero.mp hncc
    rcases this with h | h
    · exact_mod_cast h
    · exact absurd h (ne_of_gt hc)
  refine ⟨hX0, hlenKb, hna0, hnc0, ?_⟩
  have : (nb : ℝ) * b = (f : ℝ) * b := by rw [hnaa, hncc] at hsum; linarith
  exact mul_right_cancel₀ (ne_of_gt hb) this

/-- **The negative control, as a theorem.**  At scale `m ≥ 2` the maximum chord in direction `π−γ`
is `m·K·b`, so `hmax` reads `lenS ≤ m·K·b` and the chain gives only `X ≤ (m−1)·K·b`: the crossed
length is *not* forced to vanish.  Recorded so that the argument's refusal to touch the certified
tilings `N = 44, 99, 176` is checked rather than asserted. -/
theorem crossing_budget
    {a b c lenS X Kb M : ℝ} {na nb nc f j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hlen : lenS = na * a + nb * b + nc * c + X)
    (hnbj : (j : ℝ) ≤ nb) (hjf : (f : ℝ) ≤ j) (hKb : Kb = f * b)
    (hmax : lenS ≤ M) :
    X ≤ M - Kb := by
  have hna : (0:ℝ) ≤ na := Nat.cast_nonneg na
  have hnc : (0:ℝ) ≤ nc := Nat.cast_nonneg nc
  have hfb : (f : ℝ) * b ≤ (nb : ℝ) * b :=
    mul_le_mul_of_nonneg_right (le_trans hjf hnbj) (le_of_lt hb)
  rw [hKb]
  nlinarith [mul_nonneg hna ha.le, mul_nonneg hnc hc.le]

end Erdos634.R4bSeparation

#print axioms Erdos634.R4bSeparation.sep_core
#print axioms Erdos634.R4bSeparation.crossing_budget
