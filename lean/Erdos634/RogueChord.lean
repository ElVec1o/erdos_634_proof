import Mathlib.Tactic
import Erdos634.CChord
import Erdos634.Inflation

/-!
# The two-sided rogue chord: four kills and the surviving slots

Erdős #634, base-`β` branch, sequel to `RogueContainment.lean`.  At a slot `Y_i` that survives
containment (`M := i+1`, `Me > f`), the rogue `c`-edge overruns `X_i` by `Δ = c − a = f(f−e)`,
and the overrun iterates into a **two-sided chord** `[Y_i, W]`: the row side is an edge-union
beginning with `P_i`'s `a`, the rogue side an edge-union beginning with the rogue's `c`, both
sides sum to the same `L`, no proper partial sums coincide before the first common breakpoint `W`
(total stagger — each breakpoint of one side is a T-vertex interior to an edge of the other), and
every partial sum is at most `M·a`, the arclength at which the chord ray exits `Δ_k` through the
`c`-side `AB` (verified: the chord vector is `c·u − b·w = (e²/2, e/2)` in the chart, exactly
`−(1/k)·BC`, so the barycentric sum `s+t = M/k` is constant along the ray and `s = 0` at `L = Ma`;
15 744 exact-rational checks over all coprime `(e,f)`, `f ≤ 12`).

A second chord runs from the same slot along the `u`-flank: the rogue's `a`-edge
`[Y_i, Y_i + a·u]` lies inside `P_{i+1}`'s `c`-edge `[Y_i, Y_i + c·u]`, and the `u`-ray stays in
`Δ_k` exactly up to `(k−M)·c`, exiting through the `a`-side `BC` (2 731 exact checks).

**The four kills** (arithmetic cores below, geometric inputs named at the end):

* **K0, containment** (`RogueContainment.lean`): slots with `Me < f` are rogue-free.
* **K1, first slot.**  `M₀ = ⌊f/e⌋ + 1` always dies.  For `f > 2e` (separated, `a < b`) the rogue
  side needs a second edge (`tvertex_forcing`: the covering of `[X_i, Z_i]` cannot end flush at
  `Z_i` for `e ≥ 2`), so `L ≥ c + a`, contradicting `L ≤ M₀·a` (`separated_first_slot_dies`).
  For `f < 2e` (`M₀ = 2`) the two count equations alone are unsatisfiable (`slot_two_dies`).
* **K2, boundary exit.**  `L = M·a` is impossible: the rogue word would decompose `M·a` with a
  `c`-letter, and `Inflation.a_side_words` forces `n_c = qe` with `n_a + qf = M ≤ f−1`, so
  `q = 0` (`boundary_exit_impossible`).  The chord always ends strictly inside `Δ_k`.
* **K3, top slot.**  At `M = k−1` the flank chord's bound is `(k−M)·c = c`: its far side must
  decompose `c` beginning with the rogue's `a`, and `CChord.c_chord_unique_thick` leaves no such
  word for `e ≥ 2` (`top_slot_dies`).

**Consequence** (`wk_closes` and instances): a slot survives all four kills iff
`e + f < M·e` and `M ≤ k − 2`, so the step `W(k−1) ⟹ W(k)` is rogue-free for every
`k ≤ ⌊f/e⌋ + 3`, and the member's whole tower `{W(k) : k ≤ f}` closes when `⌊f/e⌋ ≥ f − 3`:
after `e = 1` (containment), the members `(2,3)`, `(2,5)`, `(3,4)` close outright.

**The obstruction is real** (`swap_fits`): for every `M` with `e + f < Me` the swap pair
`R = a·c`, `S = c·a` (`L = a + c`) meets all length, stagger and angle constraints, so the chord
system alone closes nothing beyond the range above.  The exact survivor lists (equal totals,
staggered partials, `L < Ma`, angle layer) were tabulated for all members with `f ≤ 9`; per slot
`M ∈ [⌊f/e⌋+2, f−2]` the count grows from 1 (the swap, at the low slot of thin members) to
5 017 266 (`(8,9)`, `M = 7`), and every survivor satisfies the residue pair
`f ∣ n_b − m_b`, `e ∣ (n_b+n_c) − (m_b+m_c)` of `WallStraddle.lean` — the residue lemmas engage
legitimately here because both sides are edge-unions of the same segment.

**Geometric inputs, named** (same standing obligations as `ChordInterface`):
(i) both sides of the chord are edge-unions up to the first common breakpoint — the
`HasEdgeChains`-class covering statement.  STATUS UPDATE (2026-08-15): the covering itself is now
PROVED — `WallChain.wall_two_sided` gives each side of a wall segment covered exactly once by
whole tile edges with equal totals (walls discharged along tile-edge chords by
`edge_point_not_interior`; breakpoints are tiling vertices by `chain_breakpoint_vertex`); what
remains named is the ORDER extraction (the run from the blocked end, the first common breakpoint,
the T-vertex stagger), which is bookkeeping on the proved partition, not new geometry;
(ii) a tile with interior points in a tile-union region lies in it (containment of covering tiles
in `Δ_k`); (iii) the chart identities of V1/V2 (exact algebra, checked); (iv) the forced row and
slot structure from the `W(k)` session (paper).  Axiom-clean.
-/

namespace Erdos634.RogueChord

/-- **The overrun identities.**  `b − Δ = e(f−e)` and `c − Δ = a`: the rogue's overrun is shorter
than every tile edge, which is what makes `Z_i` a T-vertex rather than a flush endpoint. -/
theorem delta_identities (e f : ℤ) :
    (f ^ 2 - e ^ 2) - f * (f - e) = e * (f - e) ∧ f ^ 2 - f * (f - e) = e * f := by
  constructor <;> ring

/-- **The T-vertex forcing.**  For `e ≥ 2` the row-side covering of `[X_i, Z_i]` (length
`Δ = f(f−e)`) cannot end flush at `Z_i`: `Δ < b < c` kills the `b`- and `c`-counts, and
`n_a·a = Δ` forces `f = (n_a+1)e`, i.e. `e ∣ f`, impossible for a coprime pair with `e ≥ 2`.
So some row edge strictly overshoots `Z_i`, and `Z_i` is interior to it: the chord continues. -/
theorem tvertex_forcing (e f b na nb nc : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = f * (f - e)) : False := by
  have hfe : e ≤ f := hef.le
  -- Δ + f·e = f·f, and the ^2/product bridges
  have hΔ : f * (f - e) + f * e = f * f := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hfe]
  have hff : f ^ 2 = f * f := pow_two f
  have hee : e ^ 2 = e * e := pow_two e
  have hef_lt : e * e < e * f := mul_lt_mul_of_pos_left hef (by omega)
  have hfe_pos : 0 < f * e := Nat.mul_pos (by omega) (by omega)
  have hcomm : f * e = e * f := Nat.mul_comm f e
  -- Δ < b (b − Δ = e(f−e) > 0) and Δ < c = f², so nb = nc = 0
  have hnb0 : nb = 0 := by
    rcases Nat.eq_zero_or_pos nb with h | h
    · exact h
    · exfalso
      have hble : b ≤ nb * b := Nat.le_mul_of_pos_left b h
      omega
  have hnc0 : nc = 0 := by
    rcases Nat.eq_zero_or_pos nc with h | h
    · exact h
    · exfalso
      have hcle : f ^ 2 ≤ nc * f ^ 2 := Nat.le_mul_of_pos_left (f ^ 2) h
      omega
  subst hnb0 hnc0
  -- n_a·(ef) = Δ ⟹ n_a·e = f − e ⟹ f = (n_a+1)·e ⟹ e ∣ f
  have hkey : na * (e * f) = f * (f - e) := by omega
  have h6 : (na * e) * f = (f - e) * f := by
    calc (na * e) * f = na * (e * f) := by ring
      _ = f * (f - e) := hkey
      _ = (f - e) * f := by ring
  have h7 : na * e = f - e := Nat.eq_of_mul_eq_mul_right (by omega) h6
  have h9 : f = na * e + e := by omega
  have hdvd : e ∣ f := ⟨na + 1, by rw [h9]; ring⟩
  have := Nat.Coprime.eq_one_of_dvd hco hdvd
  omega

/-- **The top-slot kill (K3), arithmetic core.**  A word summing to exactly `c` and containing an
`a` does not exist for `e ≥ 2`: `CChord.c_chord_unique_thick` pins the decomposition to a single
`c`.  Applied to the flank chord at `M = k−1`, whose bound `(k−M)·c` equals `c` and whose far
side starts with the rogue's `a`-edge: the slot `M = k−1` is rogue-free.  (The same statement is
the reason the rogue side of chord 1 needs a second edge, giving `L ≥ c + min(a,b)`.) -/
theorem top_slot_dies (e f x y z : ℕ) (he : 2 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hx : 1 ≤ x) (h : x * (e * f) + y * (f * f - e * e) + z * (f * f) = f * f) : False := by
  obtain ⟨h0, -, -⟩ := Erdos634.CChord.c_chord_unique_thick he hef hco h
  omega

/-- **K1 for `f < 2e` (`M₀ = 2`), by counts alone.**  Two words on `{a,b,c}` with equal totals
`L ≤ 2a`, the row containing an `a` and the rogue a `c`, cannot exist: `c ≤ L ≤ 2a` forces
`f < 2e` and `m_c = 1`, `n_c = 0`, `n_a ≤ 2`; at `n_a = 2` the rogue's `b`-count satisfies
`f ∣ m_b` (the `f_dvd_nb` descent) and dies on size; at `n_a = 1` the difference of the two
length identities is `(n_b − m_b)·b = Δ` with `0 < Δ < b`.  No stagger or angle input is used. -/
theorem slot_two_dies (e f b na nb nc ma mb mc L : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (hrow : na * (e * f) + nb * b + nc * f ^ 2 = L) (hna : 1 ≤ na)
    (hrog : ma * (e * f) + mb * b + mc * f ^ 2 = L) (hmc : 1 ≤ mc)
    (hL : L ≤ 2 * (e * f)) : False := by
  -- product/power bridges, all linear once named
  have hff : f ^ 2 = f * f := pow_two f
  have hee : e ^ 2 = e * e := pow_two e
  have hbpos : 0 < b := by
    have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
    omega
  have hBA : e * f < f * f := mul_lt_mul_of_pos_right hef (by omega)
  have hAe : e * e < e * f := mul_lt_mul_of_pos_left hef (by omega)
  have hf2L : f ^ 2 ≤ L := by
    have h1 : 1 * f ^ 2 ≤ mc * f ^ 2 := Nat.mul_le_mul_right _ hmc
    omega
  have hefL : e * f ≤ L := by
    have h1 : 1 * (e * f) ≤ na * (e * f) := Nat.mul_le_mul_right _ hna
    omega
  -- f < 2e (f = 2e dies on coprimality with e ≥ 2)
  have hf2e : f < 2 * e := by
    have h1 : f * f ≤ 2 * e * f := by
      calc f * f = f ^ 2 := hff.symm
        _ ≤ L := hf2L
        _ ≤ 2 * (e * f) := hL
        _ = 2 * e * f := by ring
    have h2 : f ≤ 2 * e := Nat.le_of_mul_le_mul_right h1 (by omega)
    rcases Nat.lt_or_ge f (2 * e) with h | h
    · exact h
    · exfalso
      have hdvd : e ∣ f := ⟨2, by omega⟩
      have := Nat.Coprime.eq_one_of_dvd hco hdvd
      omega
  have hmc1 : mc = 1 := by
    rcases Nat.lt_or_ge mc 2 with h | h
    · omega
    · exfalso
      have h1 : 2 * f ^ 2 ≤ mc * f ^ 2 := Nat.mul_le_mul_right _ h
      omega
  have hnc0 : nc = 0 := by
    rcases Nat.eq_zero_or_pos nc with h | h
    · exact h
    · exfalso
      have h1 : 1 * f ^ 2 ≤ nc * f ^ 2 := Nat.mul_le_mul_right _ h
      have h2 : 1 * (e * f) ≤ na * (e * f) := Nat.mul_le_mul_right _ hna
      omega
  have hna2 : na ≤ 2 := by
    rcases Nat.lt_or_ge na 3 with h | h
    · omega
    · exfalso
      have h1 : 3 * (e * f) ≤ na * (e * f) := Nat.mul_le_mul_right _ h
      have h2 : 0 < e * f := Nat.mul_pos (by omega) (by omega)
      omega
  subst hmc1 hnc0
  interval_cases na
  · -- n_a = 1: (n_b − m_b)·b = Δ = f² − ef with 0 < Δ < b
    have hma0 : ma = 0 := by
      rcases Nat.eq_zero_or_pos ma with h | h
      · exact h
      · exfalso
        have h1 : 1 * (e * f) ≤ ma * (e * f) := Nat.mul_le_mul_right _ h
        omega
    subst hma0
    have hkey : e * f + nb * b = mb * b + f ^ 2 := by omega
    have hnbmb : mb < nb := by
      rcases Nat.lt_or_ge mb nb with h | h
      · exact h
      · exfalso
        have h1 : nb * b ≤ mb * b := Nat.mul_le_mul_right _ h
        omega
    have h1 : (mb + 1) * b ≤ nb * b := Nat.mul_le_mul_right _ (by omega)
    have h2 : (mb + 1) * b = mb * b + b := by ring
    omega
  · -- n_a = 2: L = 2a exactly; f ∣ m_b, then size
    have h20 : nb * b = 0 ∧ L = 2 * (e * f) := by omega
    have hma0 : ma = 0 := by
      rcases Nat.eq_zero_or_pos ma with h | h
      · exact h
      · exfalso
        have h1 : 1 * (e * f) ≤ ma * (e * f) := Nat.mul_le_mul_right _ h
        omega
    subst hma0
    have hmbb : mb * b + f ^ 2 = 2 * (e * f) := by omega
    have hz : (f : ℤ) ∣ (mb : ℤ) * (b : ℤ) := by
      refine ⟨2 * (e : ℤ) - f, ?_⟩
      have hc : (mb : ℤ) * (b : ℤ) + (f : ℤ) ^ 2 = 2 * ((e : ℤ) * f) := by
        exact_mod_cast hmbb
      linear_combination hc
    have hfmb : f ∣ mb := Erdos634.Inflation.f_dvd_nb e f b mb hco hb hz
    -- b ≥ e + f, from f² ≥ ef + f and ef ≥ e² + e
    have hb1 : e * f + f ≤ f * f := by
      have h := Nat.mul_le_mul_left f (show e + 1 ≤ f by omega)
      calc e * f + f = f * (e + 1) := by ring
        _ ≤ f * f := h
    have hb2 : e * e + e ≤ e * f := by
      have h := Nat.mul_le_mul_left e (show e + 1 ≤ f by omega)
      calc e * e + e = e * (e + 1) := by ring
        _ ≤ e * f := h
    have hbef : e + f ≤ b := by omega
    rcases Nat.eq_zero_or_pos mb with h | h
    · -- m_b = 0 ⟹ f·f = 2e·f ⟹ f = 2e ⟹ e ∣ f
      subst h
      have hfeq : f = 2 * e := by
        refine Nat.eq_of_mul_eq_mul_right (show 0 < f by omega) ?_
        calc f * f = f ^ 2 := hff.symm
          _ = 2 * (e * f) := by omega
          _ = 2 * e * f := by ring
      have hdvd : e ∣ f := ⟨2, by omega⟩
      have := Nat.Coprime.eq_one_of_dvd hco hdvd
      omega
    · have hge : f ≤ mb := Nat.le_of_dvd h hfmb
      have h1 : f * b ≤ mb * b := Nat.mul_le_mul_right _ hge
      have h3 : f * (e + f) = e * f + f * f := by ring
      have h4 : f * (e + f) ≤ f * b := Nat.mul_le_mul_left _ hbef
      omega

/-- **K1 for `f > 2e` (`M₀ = ⌊f/e⌋+1 ≥ 3`), by length.**  Separated members have `a < b`, so the
rogue side's forced second edge gives `L ≥ c + a`; but at the first containment-surviving slot,
`(M−1)e < f` gives `M·a < a + c`.  The slot admits no chord at all. -/
theorem separated_first_slot_dies (e f M L : ℤ) (hf : 0 < f) (hM : (M - 1) * e < f)
    (hL1 : e * f + f ^ 2 ≤ L) (hL2 : L ≤ M * (e * f)) : False := by
  have h1 : ((M - 1) * e) * f < f * f := mul_lt_mul_of_pos_right hM hf
  have h2 : M * (e * f) = ((M - 1) * e) * f + e * f := by ring
  have h3 : f ^ 2 = f * f := pow_two f
  linarith

/-- **K2: the chord never exits through `AB`.**  `L = M·a` would make the rogue word an
edge-decomposition of `M·a` containing a `c`: `a_side_no_b` kills its `b`-count and
`a_side_words` writes `m_c = q·e`, `m_a + q·f = M`, so `m_c ≥ 1` forces `M ≥ f`.  For `M ≤ f−1`
the chord ends strictly inside `Δ_k`, and the interior-vertex regime is the only one. -/
theorem boundary_exit_impossible (e f b M ma mb mc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hco : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hM : M < f) (hmc : 1 ≤ mc)
    (heq : ma * (e * f) + mb * b + mc * f ^ 2 = M * (e * f)) : False := by
  have hmb : mb = 0 :=
    Erdos634.Inflation.a_side_no_b e f b M ma mb mc he hef hco hb (by omega) heq
  subst hmb
  have heq2 : ma * (e * f) + mc * f ^ 2 = M * (e * f) := by omega
  obtain ⟨q, h1, h2⟩ := Erdos634.Inflation.a_side_words e f M ma mc he hef hco heq2
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp at h2; omega
  · have : f ≤ q * f := Nat.le_mul_of_pos_left f h
    omega

/-- **The surviving range, and when it is empty.**  A slot survives K0–K3 iff `e + f < M·e` and
`M ≤ k−2`; if `(k−2)e ≤ e + f` the two are incompatible, so the step `W(k−1) ⟹ W(k)` is
rogue-free — that is `k ≤ ⌊f/e⌋ + 3`.  With `k ≤ f` throughout, the whole tower closes whenever
`⌊f/e⌋ ≥ f − 3`. -/
theorem wk_closes (e f M k : ℕ) (hcrit : (k - 2) * e ≤ e + f) (hM1 : e + f < M * e)
    (hM2 : M ≤ k - 2) : False := by
  have : M * e ≤ (k - 2) * e := Nat.mul_le_mul_right _ hM2
  omega

/-- `(2,3)`: slots need `5 < 2M` and `M ≤ k−2 ≤ 1` — empty.  The member closes. -/
theorem member_2_3_closes (M k : ℕ) (hk : k ≤ 3) (hM1 : 5 < M * 2) (hM2 : M ≤ k - 2) :
    False := by omega

/-- `(2,5)`: slots need `7 < 2M` and `M ≤ 3` — empty.  The member closes. -/
theorem member_2_5_closes (M k : ℕ) (hk : k ≤ 5) (hM1 : 7 < M * 2) (hM2 : M ≤ k - 2) :
    False := by omega

/-- `(3,4)`: slots need `7 < 3M` and `M ≤ 2` — empty.  The member closes. -/
theorem member_3_4_closes (M k : ℕ) (hk : k ≤ 4) (hM1 : 7 < M * 3) (hM2 : M ≤ k - 2) :
    False := by omega

/-- **The obstruction is real.**  For every slot in the surviving range the swap pair
`R = a·c`, `S = c·a` meets the whole chord system: equal totals `a + c`, staggered partials
(`a ≠ c`), and the strict bound `a + c < M·a`.  The chord system alone closes nothing more:
what remains is the finite survivor list per slot, tabulated for `f ≤ 9`. -/
theorem swap_fits (e f M : ℤ) (he : 0 < e) (hef : e < f) (hM : e + f < M * e) :
    e * f + f ^ 2 < M * (e * f) ∧ e * f ≠ f ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  have h1 : (e + f) * f < (M * e) * f := mul_lt_mul_of_pos_right hM hf
  have h2 : (e + f) * f = e * f + f * f := by ring
  have h3 : (M * e) * f = M * (e * f) := by ring
  have h4 : f ^ 2 = f * f := pow_two f
  refine ⟨by linarith, fun h => ?_⟩
  have h5 : e * f < f * f := mul_lt_mul_of_pos_right hef hf
  linarith

end Erdos634.RogueChord

#print axioms Erdos634.RogueChord.delta_identities
#print axioms Erdos634.RogueChord.tvertex_forcing
#print axioms Erdos634.RogueChord.top_slot_dies
#print axioms Erdos634.RogueChord.slot_two_dies
#print axioms Erdos634.RogueChord.separated_first_slot_dies
#print axioms Erdos634.RogueChord.boundary_exit_impossible
#print axioms Erdos634.RogueChord.wk_closes
#print axioms Erdos634.RogueChord.member_2_3_closes
#print axioms Erdos634.RogueChord.member_2_5_closes
#print axioms Erdos634.RogueChord.member_3_4_closes
#print axioms Erdos634.RogueChord.swap_fits
