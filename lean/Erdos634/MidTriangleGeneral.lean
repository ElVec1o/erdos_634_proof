import Mathlib.Tactic

/-!
# The middle triangle `T_mid` is untileable for **every** `e`, not only `e = 1`

Erdős #634, base-β family at `m = 1`, `N = 3f² − e²`.  Tile `(a,b,c) = (ef, f²−e², f²)`, angles
`α, β, γ = 2α+β` with `3α + 2β = π`.  The forced double cut leaves the middle triangle `T_mid` with

* base `DD'` of length `e·b`,  legs `f·b`,  apex `α`,  base angles `α+β`,  and exactly `b` tiles.

`MidTriangleE1` killed this at `e = 1` only, and the file recorded the reason the argument stopped
there: *"at `e ≥ 2` the base carries `e` distinct `b`-sides and the two extreme tiles differ"*.  That
reason was wrong — it looked only at the two ends and never at the **junctions between consecutive
base tiles**, where the orientation propagates.  The kill is general:

1.  `base_partition`: the base, of length `e·b`, admits exactly one edge partition — `e` whole
    `b`-sides.  (Mod `f`: `f ∣ e²(v−e)`, and `gcd(e,f) = 1` with `0 ≤ v ≤ e < f` forces `v = e`.)
    So there are exactly `e` base tiles, meeting at `e−1` interior junctions.
2.  Each base tile presents `α` at one end of its `b`-side and `γ` at the other (`β` is opposite `b`).
3.  At `D` the corner angle is `α+β`, and `γ = 2α+β > α+β`, so the **first** tile presents `α` at
    `D`, hence `γ` at the first junction.
4.  `junction_forces_alpha`: at a junction the angles sum to `π`; a tile presenting `γ` there leaves
    `π − γ = α+β`, and a second `γ` cannot fit since `2γ = π + α > π`.  So the next tile presents `α`.
5.  Induction along the base: **every** tile presents `α` on its left and `γ` on its right.
6.  The last tile therefore presents `γ` at `D'` — where the corner angle is `α+β < γ`.  ∎

At `e = 1` steps 4–5 are empty and this degenerates to `MidTriangleE1`'s argument.

**Scope unchanged.** This removes the `e = 1` restriction *from `T_mid`*.  It does **not** close
`e ≥ 2`: `T_mid` only arises once the double cut is forced, which is Theorem R, and Theorem R is
established only at `e = 1` (and is itself conditional on Beeson's Theorem 2).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MidTriangleGeneral

/-! ## 1. The base carries exactly `e` whole `b`-sides -/

/-- **The base partition, general in `(e,f)`.**  With `a = ef`, `b = f²−e²`, `c = f²` and
`gcd(e,f) = 1`, `0 < e < f`, the only nonnegative solution of `ua + vb + wc = e·b` is `(0, e, 0)`. -/
theorem base_partition {e f u v w : ℤ} (he : 0 < e) (hef : e < f)
    (hcop : IsCoprime e f) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h : u * (e * f) + v * (f ^ 2 - e ^ 2) + w * f ^ 2 = e * (f ^ 2 - e ^ 2)) :
    u = 0 ∧ v = e ∧ w = 0 := by
  have hf0 : 0 < f := lt_trans he hef
  have hb0 : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have huf : 0 ≤ u * (e * f) := mul_nonneg hu (by positivity)
  have hwf : 0 ≤ w * f ^ 2 := mul_nonneg hw (by positivity)
  -- `f ∣ e² (v − e)`
  have hdvd : f ∣ e ^ 2 * (v - e) := ⟨u * e + v * f + w * f - e * f, by linarith [h]⟩
  have hcop2 : IsCoprime f (e ^ 2) := hcop.symm.pow_right
  have hfv : f ∣ (v - e) := hcop2.dvd_of_dvd_mul_left hdvd
  -- `0 ≤ v ≤ e < f`, so `v = e`
  have hvle : v ≤ e := by nlinarith [huf, hwf, hb0]
  have hve : v = e := by
    obtain ⟨t, ht⟩ := hfv
    have hub : f * t ≤ 0 := by linarith
    have hlb : -f < f * t := by linarith
    have ht0 : t ≤ 0 := by nlinarith
    have ht1 : 0 ≤ t := by nlinarith
    have : t = 0 := le_antisymm ht0 ht1
    rw [this, mul_zero] at ht
    linarith
  refine ⟨?_, hve, ?_⟩
  · have hrest : u * (e * f) + w * f ^ 2 = 0 := by rw [hve] at h; linarith [h]
    have hz : u * (e * f) = 0 := by linarith
    rcases mul_eq_zero.mp hz with h' | h'
    · exact h'
    · exfalso; nlinarith
  · have hrest : u * (e * f) + w * f ^ 2 = 0 := by rw [hve] at h; linarith [h]
    have hz : w * f ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp hz with h' | h'
    · exact h'
    · exfalso; nlinarith

/-! ## 2. The junction step -/

variable (α β γ : ℝ)

/-- **A second `γ` cannot fit at a junction.**  `2γ = π + α > π`. -/
theorem two_gamma_gt_pi (hα : 0 < α) (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi) :
    Real.pi < γ + γ := by rw [hγ]; linarith

/-- **The junction step.**  At an interior junction of the base the angles sum to `π`; if the tile on
the left presents `γ`, the tile on the right cannot also present `γ`, so — its angle at that vertex
being `α` or `γ` — it presents `α`. -/
theorem junction_forces_alpha (hα : 0 < α) (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (R L : ℝ) (hR : R = γ) (hL : L = α ∨ L = γ) (hsum : R + L ≤ Real.pi) : L = α := by
  rcases hL with h | h
  · exact h
  · exfalso; rw [hR, h] at hsum; linarith [two_gamma_gt_pi α β γ hα hγ hrel]

/-- **A corner of angle `α+β` cannot receive `γ`.** -/
theorem no_gamma_at_corner (hα : 0 < α) (hγ : γ = 2 * α + β) (θ : ℝ) (hθ : θ = γ)
    (hfit : θ ≤ α + β) : False := by rw [hθ, hγ] at hfit; linarith

/-! ## 3. The march along the base, and the contradiction -/

/-- **`T_mid` is untileable, for every `e ≥ 1`.**

`L j`, `R j` are the angles the `j`-th base tile presents at the two ends of its `b`-side; `n = e`
is the number of base tiles (`base_partition`).  The hypotheses are exactly the six facts listed in
the header: each tile shows `α` at one end and `γ` at the other (`hends`), the corner at `D` admits
at most `α+β` (`hD`), the junctions sum to at most `π` (`hjunction`), and the corner at `D'` admits
at most `α+β` (`hD'`). -/
theorem midTriangle_untileable_general (hα : 0 < α) (hβ : 0 < β) (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi)
    (n : ℕ) (hn : 0 < n) (L R : ℕ → ℝ)
    (hends : ∀ j < n, (L j = α ∧ R j = γ) ∨ (L j = γ ∧ R j = α))
    (hD : L 0 ≤ α + β)
    (hjunction : ∀ j, j + 1 < n → R j + L (j + 1) ≤ Real.pi)
    (hD' : R (n - 1) ≤ α + β) : False := by
  -- every tile presents `α` on the left, hence `γ` on the right
  have key : ∀ j, j < n → L j = α ∧ R j = γ := by
    intro j
    induction j with
    | zero =>
        intro _
        rcases hends 0 hn with h | h
        · exact h
        · exact absurd hD (by rw [h.1, hγ]; push_neg; linarith)
    | succ i ih =>
        intro hlt
        have hi : i < n := by omega
        obtain ⟨_, hRi⟩ := ih hi
        have hLi1 : L (i + 1) = α :=
          junction_forces_alpha α β γ hα hγ hrel (R i) (L (i + 1)) hRi
            (by rcases hends (i + 1) hlt with h | h
                · exact Or.inl h.1
                · exact Or.inr h.1)
            (hjunction i hlt)
        rcases hends (i + 1) hlt with h | h
        · exact h
        · exact absurd hLi1 (by rw [h.1, hγ]; intro hc; linarith)

  obtain ⟨_, hRlast⟩ := key (n - 1) (by omega)
  exact no_gamma_at_corner α β γ hα hγ (R (n - 1)) hRlast hD'

end Erdos634.MidTriangleGeneral
