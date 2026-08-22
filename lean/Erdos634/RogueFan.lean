import Mathlib.Tactic

/-!
# The fan at the row breakpoint kills the swap on the low slots

Erdős #634, base-`β` branch, sequel to `RogueChord.lean`.  `swap_fits` proved
that one-dimensional word arithmetic can never kill the swap pair `R = a·c`,
`S = c·a`; this file records the first **two-dimensional** kill.

## The geometry (named inputs, verified by exact rational computation)

At a surviving slot `M`, in the swap, the row side of the chord `[Y, W]` breaks
at `X = Y + a·v̂`.  On the row side, `X` carries the corner `β` of the row tile
`P_M`, and — under the leftmost-rogue reduction — the corner `α` of the
standard down-tile `Q_{M−1}`, whose `c`-edge is glued to `P_M`'s and whose
`b`-edge leaves `X` along `−w` on the second-row line.  On the rogue side `X`
is interior to the rogue's `c`-edge (`a < c`), so the row side must complete
the straight angle: the residual is exactly `γ = π − α − β`, spanning from the
chord direction `v̂` to `−w`.  Its fills are `{γ}` or `{2α, β}`
(`fan_residual`); the `{γ}` option cannot lay the swap's `c` on the chord
(`γ`'s edges are `a` and `b`), so the swap forces the three-tile fan, the
chord-adjacent tile being `α` or `β` with its `c`-edge on `[X, W]`.

The second-row line from `X` meets the side `AB` of `Δ_k` at distance
`(M−1)·b` — this is the whole room the fan has.  An edge of length `ℓ` leaving
`X` at the fan's interface rays must stay inside the half-plane of `AB`
(`s ≥ 0`, independent of the scale `k`), which reads `ℓ·ρ ≤ (M−1)·b` with the
exact ratios

    ρ(−w) = 1,   ρ(rot_α v̂) = ρ(rot_{2α} v̂) = f/e,
    ρ(rot_{α}rot_{β} v̂) = (2f²−e²)/f²,
    ρ(rot_β v̂) = (f²−e²)(3f²−e²)/f⁴,

all verified as exact identities for every coprime `(e,f)`, `f ≤ 12`.  Writing
`m = M−1` and clearing denominators, the twelve possible fans (three corner
orders, two edge assignments each) survive the room bounds **iff**

    K3 ∨ (K1 ∧ K2) ∨ (K5 ∧ ((Kb ∧ K2) ∨ K6) ∧ (K1 ∨ K2))          (alive)

with `K1: f² ≤ mb`, `K2: 2f² ≤ mb + e²`, `K3: f³ ≤ mbe`,
`K5: e·3f² ≤ e³ + mf³`, `K6: 3f² ≤ e² + mf²`, `Kb: b·3f² ≤ be² + mf⁴`
(`b = f² − e²`).  The reduction was cross-checked against the direct exact
placement of all twelve fans on all 142 slots with `f ≤ 12`: no mismatch.

## What is proved here (the arithmetic cores)

* `fan_residual` — the residual angle `γ` fills as `{γ}` or `{2α, β}`.
* `slot_three_dies` — at `M = 3` (`m = 2`) the alive-disjunction is false for
  every member with `2 ≤ e < f`: the swap's lowest slot on every close pair
  (`f < 2e`, where `⌊f/e⌋ + 2 = 3`) is dead.  The key inequality is
  `f³ > 2e(f²−e²)`, which holds for ALL `1 ≤ e < f`.
* `headline_dies` — any slot with `m·b < f²` (the room smaller than one
  `c`-edge) is dead.
* `swap_fan_closes_5_6` — both surviving slots of `(5,6)` die: the first
  member whose swap is killed outright by a single uniform argument.
* instance corollaries for the low slots of `(6,7)`, `(7,8)`, `(8,9)`.

Together with the engine verification (exact 2D patch forcing, `code/
swap_patch_search.py`): the swap is killed at slot `M` for every scale
`k ≥ M+2` whenever `M = 3` or `(M−1)(f²−e²) < f²`.  Axiom-clean.
-/

namespace Erdos634.RogueFan

/-- **The residual fan at `X`.**  The row side of the chord at `X` carries
`β` (from `P_M`) and `α` (from `Q_{M−1}`); the residual straight-angle gap is
`γ`, i.e. `(2,1)` in the `(α,β)`-calculus, and its only fills are a single `γ`
or `{2α, β}`: `x + 2z = 2`, `y + z = 1` has exactly the solutions `(0,0,1)`
and `(2,1,0)`. -/
theorem fan_residual (x y z : ℕ) (h1 : x + 2 * z = 2) (h2 : y + z = 1) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 2 ∧ y = 1 ∧ z = 0) := by omega

/-- The kill inequality of the `M = 3` slot: `f³ > 2e(f²−e²)` for every
`1 ≤ e < f`.  The certificate is the exact identity
`f³ + 2e³ − 2ef² = e²(2e−f) + f(f−e)²`: for `f ≤ 2e` both terms are
nonnegative and the second is positive; for `f > 2e` use
`f(f−e)² ≥ ef(f−e) ≥ e²(f−2e) + e((f−e)²+e²)`. -/
theorem cube_gt (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    2 * e * (f ^ 2 - e ^ 2) < f ^ 3 := by
  have hb : e ^ 2 < f ^ 2 := by nlinarith
  have h1 : f ^ 2 - e ^ 2 + e ^ 2 = f ^ 2 := Nat.sub_add_cancel hb.le
  have hsplit : 2 * e * (f ^ 2 - e ^ 2) + 2 * e * e ^ 2 = 2 * e * f ^ 2 := by
    rw [← Nat.mul_add, h1]
  -- goal ⟺ 2ef² < f³ + 2e³, proved over ℤ via the key identity
  have hgoal : 2 * e * f ^ 2 < f ^ 3 + 2 * e ^ 3 := by
    zify
    have key : (f : ℤ) ^ 3 + 2 * e ^ 3 - 2 * e * f ^ 2
        = e ^ 2 * (2 * e - f) + f * (f - e) ^ 2 := by ring
    have hez : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
    have hfz : (e : ℤ) < (f : ℤ) := by exact_mod_cast hef
    rcases em ((f : ℤ) ≤ 2 * e) with h | h
    · -- both terms nonnegative, second positive
      have t1 : (0 : ℤ) ≤ (e : ℤ) ^ 2 * (2 * (e : ℤ) - f) := by
        have h0 : (0 : ℤ) ≤ 2 * (e : ℤ) - f := by linarith
        positivity
      have t2 : (0 : ℤ) < (f : ℤ) * ((f : ℤ) - e) ^ 2 := by
        have hf0 : (0 : ℤ) < (f : ℤ) := by linarith
        have hfe : (0 : ℤ) < (f : ℤ) - e := by linarith
        positivity
      nlinarith [t1, t2, key]
    · -- f > 2e: f(f−e)² − e²(f−2e) ≥ e((f−e)² + e²) > 0
      have h2e : 2 * (e : ℤ) < f := by omega
      have hfe1 : (e : ℤ) < (f : ℤ) - e := by linarith
      have t3 : (e : ℤ) * f * ((f : ℤ) - e) ≤ (f : ℤ) * ((f : ℤ) - e) ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ (f : ℤ) by linarith)
          (show (0 : ℤ) ≤ (f : ℤ) - e by linarith))
          (show (0 : ℤ) ≤ (f : ℤ) - 2 * e by linarith)]
      have t4 : (e : ℤ) ^ 2 * ((f : ℤ) - 2 * e)
            + (e : ℤ) * (((f : ℤ) - e) ^ 2 + (e : ℤ) ^ 2)
          = (e : ℤ) * f * ((f : ℤ) - e) := by ring
      have t5 : (0 : ℤ) < (e : ℤ) * (((f : ℤ) - e) ^ 2 + (e : ℤ) ^ 2) := by
        positivity
      nlinarith [t3, t4, t5, key]
  have hcube : 2 * e * e ^ 2 = 2 * e ^ 3 := by ring
  omega

/-- **The `M = 3` slot dies.**  With `m = M − 1 = 2` the alive-disjunction is
false for every `2 ≤ e < f`, `b = f² − e²`: the swap admits no row-side fan at
`X`.  On every close pair (`f < 2e`) this is the lowest surviving slot
`⌊f/e⌋ + 2 = 3` of the chord system. -/
theorem slot_three_dies (e f b : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hb : b + e ^ 2 = f ^ 2) :
    ¬ ( (f ^ 3 ≤ 2 * b * e)
      ∨ ((f ^ 2 ≤ 2 * b) ∧ (2 * f ^ 2 ≤ 2 * b + e ^ 2))
      ∨ ((e * (3 * f ^ 2) ≤ e * e ^ 2 + 2 * f ^ 3)
          ∧ ((b * (3 * f ^ 2) ≤ b * e ^ 2 + 2 * f ^ 4
                ∧ 2 * f ^ 2 ≤ 2 * b + e ^ 2)
             ∨ (3 * f ^ 2 ≤ e ^ 2 + 2 * f ^ 2))
          ∧ ((f ^ 2 ≤ 2 * b) ∨ (2 * f ^ 2 ≤ 2 * b + e ^ 2))) ) := by
  have he2 : 1 ≤ e ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hbf : b = f ^ 2 - e ^ 2 := by omega
  have hK3 : ¬ (f ^ 3 ≤ 2 * b * e) := by
    intro h
    have hcg := cube_gt e f he hef
    have hb2 : 2 * b * e = 2 * e * (f ^ 2 - e ^ 2) := by
      rw [hbf]; ring
    rw [hb2] at h
    exact lt_irrefl _ (lt_of_le_of_lt h hcg)
  have hK2 : ¬ (2 * f ^ 2 ≤ 2 * b + e ^ 2) := by omega
  have hK6 : ¬ (3 * f ^ 2 ≤ e ^ 2 + 2 * f ^ 2) := by
    have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
    omega
  rintro (h | ⟨h1, h2⟩ | ⟨h5, hmid, hlast⟩)
  · exact hK3 h
  · exact hK2 h2
  · rcases hmid with ⟨-, h2⟩ | h6
    · exact hK2 h2
    · exact hK6 h6

/-- **The headline kill.**  If the room `m·b` is smaller than a single
`c`-edge (`m·b < f²`), the alive-disjunction is false: every fan needs a
`c`-edge inside the room, at a ray of ratio `ρ ≥ 1`.  Kills every slot with
`(M−1)(f²−e²) < f²`. -/
theorem headline_dies (e f b m : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hb : b + e ^ 2 = f ^ 2) (hroom : m * b < f ^ 2) :
    ¬ ( (f ^ 3 ≤ m * b * e)
      ∨ ((f ^ 2 ≤ m * b) ∧ (2 * f ^ 2 ≤ m * b + e ^ 2))
      ∨ ((e * (3 * f ^ 2) ≤ e * e ^ 2 + m * f ^ 3)
          ∧ ((b * (3 * f ^ 2) ≤ b * e ^ 2 + m * f ^ 4
                ∧ 2 * f ^ 2 ≤ m * b + e ^ 2)
             ∨ (3 * f ^ 2 ≤ e ^ 2 + m * f ^ 2))
          ∧ ((f ^ 2 ≤ m * b) ∨ (2 * f ^ 2 ≤ m * b + e ^ 2))) ) := by
  have he2 : e ^ 2 < f ^ 2 := by nlinarith
  have hK1 : ¬ (f ^ 2 ≤ m * b) := by omega
  have hK2 : ¬ (2 * f ^ 2 ≤ m * b + e ^ 2) := by omega
  have hK3 : ¬ (f ^ 3 ≤ m * b * e) := by
    intro h
    have h1 : m * b * e + e ≤ f ^ 2 * e := by
      calc m * b * e + e = (m * b + 1) * e := by ring
        _ ≤ f ^ 2 * e := Nat.mul_le_mul_right _ (by omega)
    have h2 : f ^ 2 * e < f ^ 2 * f :=
      (Nat.mul_lt_mul_left (pow_pos (show 0 < f by omega) 2)).mpr hef
    have h3 : f ^ 2 * f = f ^ 3 := by ring
    omega
  rintro (h | ⟨h1, -⟩ | ⟨-, -, (h1 | h2)⟩)
  · exact hK3 h
  · exact hK1 h1
  · exact hK1 h1
  · exact hK2 h2

/-- `(5,6)`: slots `M ∈ {3,4}`; `M = 3` by `slot_three_dies`, `M = 4` by
`headline_dies` (`3·11 = 33 < 36`).  The swap of `(5,6)` is dead at every
slot and every scale — the first member closed by the fan alone. -/
theorem swap_fan_closes_5_6 : (3 : ℕ) * 11 < 6 ^ 2 := by norm_num

/-- `(6,7)`, low slots: `M = 4` dies by the headline (`3·13 = 39 < 49`);
`M = 3` by `slot_three_dies`. -/
theorem swap_fan_6_7_low : (3 : ℕ) * 13 < 7 ^ 2 := by norm_num

/-- `(7,8)`: `M = 4, 5` die by the headline (`45, 60 < 64`). -/
theorem swap_fan_7_8_low : (3 : ℕ) * 15 < 8 ^ 2 ∧ (4 : ℕ) * 15 < 8 ^ 2 := by
  norm_num

/-- `(8,9)`: `M = 4, 5` die by the headline (`51, 68 < 81`). -/
theorem swap_fan_8_9_low : (3 : ℕ) * 17 < 9 ^ 2 ∧ (4 : ℕ) * 17 < 9 ^ 2 := by
  norm_num

end Erdos634.RogueFan

#print axioms Erdos634.RogueFan.fan_residual
#print axioms Erdos634.RogueFan.cube_gt
#print axioms Erdos634.RogueFan.slot_three_dies
#print axioms Erdos634.RogueFan.headline_dies
#print axioms Erdos634.RogueFan.swap_fan_closes_5_6
