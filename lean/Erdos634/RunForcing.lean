import Erdos634.MidTriangleGeneral

/-!
# When is a run forced to be all-`b`? — exactly below the essential-segment floor

Erdős #634, base-β family, tile `(a,b,c) = (ef, f²−e², f²)`, `gcd(e,f) = 1`, `0 < e < f`.

`MidTriangleGeneral.base_partition` showed that a segment of length `e·b` admits only the all-`b`
edge partition, which is what let the orientation march (this project's
`RunOrientation.corner_anchored_run_all_BG` technique, there applied to `a`-runs) run along `T_mid`'s
base and kill it.  The obvious next question is which *other* segments are forced this way.  The
answer is sharp:

> **A segment of length `k·b` is forced to be `k` whole `b`-edges if and only if `k < f`.**

`run_all_b` is the forward half (the mod-`f` argument, with `k` in place of `e`), and
`run_not_forced_at_f` is the sharpness: at `k = f` there is a second partition, and it is
**`f·b = (f−e)·a + (f−e)·c`** — containing no `b` at all.

**Why this matters, and it is a negative result.**  The essential-segment length floor is exactly
`K·b` with `K = f` (from `j b = u a + v c` ⟹ `f ∣ j`).  So the threshold at which all-`b` forcing
fails is *exactly* the floor at which essential segments begin.  The march can never reach an
essential segment: it is confined to `k < f`, and every essential segment has `k ≥ f`.  This is not
a coincidence of small cases — `run_not_forced_at_f` exhibits the escaping partition in closed form,
and it is precisely the minimal essential edge relation.

So: the technique that killed `T_mid` is structurally barred from attacking the crossing question
directly.  Recorded here as "where not to look", proved rather than observed.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RunForcing

/-- **Forced all-`b` run.**  A segment of length `k·b` with `0 < k < f` admits only `k` whole
`b`-edges.  (`MidTriangleGeneral.base_partition` is the case `k = e`.) -/
theorem run_all_b {e f k u v w : ℤ} (he : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f) (hk : 0 < k) (hkf : k < f)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h : u * (e * f) + v * (f ^ 2 - e ^ 2) + w * f ^ 2 = k * (f ^ 2 - e ^ 2)) :
    u = 0 ∧ v = k ∧ w = 0 := by
  have hf0 : 0 < f := lt_trans he hef
  have hb0 : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have huf : 0 ≤ u * (e * f) := mul_nonneg hu (by positivity)
  have hwf : 0 ≤ w * f ^ 2 := mul_nonneg hw (by positivity)
  have hdvd : f ∣ e ^ 2 * (v - k) := ⟨u * e + v * f + w * f - k * f, by linarith [h]⟩
  have hcop2 : IsCoprime f (e ^ 2) := hcop.symm.pow_right
  have hfv : f ∣ (v - k) := hcop2.dvd_of_dvd_mul_left hdvd
  have hvle : v ≤ k := by nlinarith [huf, hwf, hb0]
  have hvk : v = k := by
    obtain ⟨t, ht⟩ := hfv
    have hub : f * t ≤ 0 := by linarith
    have hlb : -f < f * t := by linarith
    have ht0 : t ≤ 0 := by nlinarith
    have ht1 : 0 ≤ t := by nlinarith
    rw [le_antisymm ht0 ht1, mul_zero] at ht
    linarith
  refine ⟨?_, hvk, ?_⟩
  · have hz : u * (e * f) = 0 := by rw [hvk] at h; linarith [h]
    rcases mul_eq_zero.mp hz with h' | h'
    · exact h'
    · exfalso; nlinarith
  · have hz : w * f ^ 2 = 0 := by rw [hvk] at h; linarith [h]
    rcases mul_eq_zero.mp hz with h' | h'
    · exact h'
    · exfalso; nlinarith

/-- **Sharpness at `k = f`: the forcing fails, and the escaping partition contains no `b`.**
`f·b = (f−e)·a + (f−e)·c`, i.e. `f(f²−e²) = (f−e)(ef) + (f−e)f²`. -/
theorem run_not_forced_at_f (e f : ℤ) :
    (f - e) * (e * f) + (0 : ℤ) * (f ^ 2 - e ^ 2) + (f - e) * f ^ 2 = f * (f ^ 2 - e ^ 2) := by
  ring

/-- **The escaping partition is a genuine second solution**: it is not the all-`b` one, whenever
`e < f` (so `f − e ≠ 0`). -/
theorem run_not_forced_at_f_ne (e f : ℤ) (hef : e < f) : (f - e) ≠ 0 := by omega

/-- **The minimal essential edge relation, in closed form.**  Every essential segment satisfies
`j b = u a + v c` with `f ∣ j`; the smallest case `j = f` is realised by `u = v = f − e`. -/
theorem minimal_essential_relation (e f : ℤ) :
    f * (f ^ 2 - e ^ 2) = (f - e) * (e * f) + (f - e) * f ^ 2 := by ring

/-- **The march is barred from essential segments.**  A forced all-`b` run has `k < f`; every
essential segment has `k ≥ f`.  Stated as the disjointness of the two ranges. -/
theorem march_cannot_reach_essential {k f : ℤ} (hforced : k < f) (hessential : f ≤ k) : False := by
  omega

end Erdos634.RunForcing
