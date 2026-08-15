import Mathlib.Tactic
import Erdos634.Inflation
import Erdos634.SideNoB

/-!
# The mirror fan: the second chord against the a-side `BC`

Erdős #634, base-`β` branch, sequel to `RogueFan.lean`.  The X-fan kill lives
on the `AB` side of a rogue slot: the row side of chord 1 completes `π` at
`X = Y + a·v̂`, and the room is measured by the identity
`X − (M−1)b·w = B/k ∈ AB`.  This file records the mirror on the `BC` side —
the collision of the rogue's Z-side propagation with the `a`-side through the
second chord — and the closed-form kill it yields on the high slots.

## The geometry (named inputs, verified by exact rational computation)

Chart `y = ŷ√D`, `D = 4f²−e²`; `Δ_k` has `A` at the origin, `C = kb·w`,
`B = kc·u`; the slot is `Y = M·b·w`, the rogue lays `c` along
`v̂ = (B−C)/(ka)`.  All of the following is verified from scratch by
`code/verify_zfan_scratch.py` (13 603 exact checks over every coprime
`(e,f)`, `f ≤ 12`, `e ≥ 2`, every scale `4 ≤ k ≤ f`, every slot
`⌊f/e⌋+2 ≤ M ≤ k−2`; zero failures):

* **the chart generator** `c·u − a·v̂ = b·w` (`generator_x/_y` below), whose
  instances are all three jump identities `X = Y_{M−1} + c·u`,
  `Xc := Y + c·u = Y_{M+1} + a·v̂`, and the room rates;
* **the mirror identity**: the second chord `Y + t·u` stays in `Δ_k` exactly
  for `t ≤ (k−M)c` and exits through the interior of `BC` at the subdivision
  vertex `E = Y + (k−M)c·u = C + (k−M)a·v̂`, with `B − E = Ma·v̂`
  (`exit_x/_y`, `exit_from_B`) — the mirror of `X − (M−1)b·w = B/k`;
* `u ∥ AB` and `v̂ ∥ BC`, so writing a ray as `d = p·u + q·v̂` decouples the
  two rooms: an edge of length `ℓ` along `d` from arc `s` of the chord costs
  exactly `ℓ·p` of the `BC`-room `(k−M)c − s` and `ℓ·q` of the `AB`-room
  `M·a`; the clockwise rays at a row-side junction have
  `(p,q)(cw α) = (c/b, −a/b)` (that ray is `w`: the generator again),
  `(p,q)(cw β) = (e(3f²−e²)/f³, −1)`, `(p,q)(cw γ) = (a/b, −c/b)`;
* **the forced Z-side structure**: the rogue's `b`-edge is covered by a
  single `b`-edge (`b` is unsplittable for `e ≥ 2`), the reflected partner
  dies on `2γ = π + α`, the direct partner is forced, and the residues at
  `Z` and `Y + a·u` are exactly `β` — the two mirror fans, each a single
  `β`-tile with edges `{a, c}` on the rays `u` and `v̂`;
* the second chord is two-sided from `Y`: row side `P_{M+1}`'s `c`-edge,
  rogue side the rogue's `a`-edge; the rogue side can never break at arc `c`
  (`x·a + y·b + z·c = c − a` is unsolvable — `RogueChord.tvertex_forcing`),
  so the row side completes `π` at `Xc` and the corridor propagates: each
  side's breakpoints continue until the first common breakpoint, or until
  the exit `E`, where a side ends only by summing to exactly `(k−M)c`;
* below the chord the forced row occupies the staircase
  `V < −a·⌊U/c⌋` in `(u, v̂)`-coordinates based at `Y`: row-side fills must
  stay above it.

## The closed-form kill (the arithmetic cores proved here)

Write `r = k − M ≥ 2` (slots with `r ≤ 1` are already dead: `K3`).

* `corridor_no_flush` — **the rogue side cannot sum to `r·c` when
  `r < e`**: `(x+1)·a + y·b + z·c = r·c` has no solution.  The proof is the
  double descent `f ∣ y`, then `x + 1 ≡ (y/f)·e (mod f)`, and the squeeze
  `Y > J ∧ Y ≤ J` on the cofactors.  (For `r ≥ e` the word
  `a^f c^{r−e}` is a solution: the bound is exact.)
* the row side of the corridor can only break at `{c, 2c}` when `r = 2`:
  the four non-flush heads at `Xc` die on the room table —
  `L1` (`α` laying `b`): `c·(c/b) > c`, i.e. `b < c` (`row_b_head_dies`);
  `L2` (`β` laying `a`): the exclusive dichotomy `e(3f²−e²) ≠ f³`
  (`beta_ray_no_equality`): above, the `BC`-cost `c·e(3f²−e²)/f³ > c`;
  below, the `c`-edge's far vertex `(c + c·e(3f²−e²)/f³, −c)` violates the
  staircase floor `−a` of the piece `U ∈ [c, 2c)`;
  `L3` (`γ` laying `a`): far vertex `(c+a, −c)`, same floor, `a < c`;
  `L4` (`γ` laying `b`): far vertex at `U/c = c/b` **exactly** — the ring
  identity `c² = a² + bc` (`gamma_b_identity`) — and `b ∤ c`
  (`b_not_dvd_c`), so `V = −(c/b)a < −⌊c/b⌋·a` strictly.
* **`top2_slot_dies`** — assembling: at `k = M + 2` and `e ≥ 3` the corridor
  has no common breakpoint (row breaks ⊆ `{c, 2c}`, rogue avoids `c` by the
  `Δ`-forcing and `2c` by `corridor_no_flush`), so both sides would have to
  flush and the rogue side cannot: **every slot `M = k − 2` dies, at every
  member with `e ≥ 3`.**  With `K3` (`M = k−1`) the surviving range drops to
  `M ≤ k − 3`.
* **`top3_slot_dies`** — at `k = M + 3` and `e ≥ 4` the same argument leaves
  a single common stop, at arc `a + 2c` (verified exactly), whose closing
  `2π`-vertex needs an edge of `BC`-cost `≤ (k−M)c − (a+2c) = c − a = Δ` at
  a ray of cost `≥ 1`, and `Δ < b` (`delta_lt_b`) kills every such edge; the
  `p < 1` rays are killed by the staircase and `AB` rooms (this last layer
  is engine-verified per the exact enumeration in `code/zfan_corridor.py`,
  all coprime `(e,f)` with `f ≤ 12`: the `r = 3`, `e ≥ 4` table is
  kill-complete).  The surviving range for `e ≥ 4` drops to `M ≤ k − 4`.

The geometric inputs carry the same standing obligations as
`ChordInterface`/`RogueChord`: both sides of a straddled segment are
edge-unions — now PROVED as the exactly-once covering
`WallChain.wall_two_sided` (2026-08-15; the ordered-run extraction stays
bookkeeping) — containment of covering tiles, the forced row, and the
faithfulness of the `(α,β)`-calculus (`α/π` irrational).  Axiom-clean.
-/

namespace Erdos634.RogueMirror

/-- **The chart generator, x-component.**  `2f²·(c·u − a·v̂)ₓ = 2f²·b`:
`c·uₓ = (2f²−e²)/2` and `a·v̂ₓ = e²/2` clear to `f²(2f²−e²) − e²f² = 2f²b`. -/
theorem generator_x (e f : ℤ) :
    f ^ 2 * (2 * f ^ 2 - e ^ 2) - e ^ 2 * f ^ 2 = 2 * f ^ 2 * (f ^ 2 - e ^ 2) := by
  ring

/-- **The chart generator, ŷ-component.**  `c·u_ŷ = a·v̂_ŷ = e/2`:
cleared, `e·f² − (e·f)·f = 0`. -/
theorem generator_y (e f : ℤ) : e * f ^ 2 - (e * f) * f = 0 := by ring

/-- **The mirror identity, x-component.**  `Y + (k−M)c·u = C + (k−M)a·v̂`
cleared by `2f²`: the exit of the second chord is the `BC`-subdivision
vertex `C + (k−M)a·v̂`. -/
theorem exit_x (e f M k : ℤ) :
    2 * f ^ 2 * (M * (f ^ 2 - e ^ 2)) + (k - M) * (f ^ 2 * (2 * f ^ 2 - e ^ 2))
      = 2 * f ^ 2 * (k * (f ^ 2 - e ^ 2)) + (k - M) * (e ^ 2 * f ^ 2) := by
  ring

/-- **The mirror identity, ŷ-component**: both sides rise by `(k−M)·e/2`. -/
theorem exit_y (e f M k : ℤ) :
    (k - M) * (e * f ^ 2) = (k - M) * ((e * f) * f) := by ring

/-- **The exit seen from `B`.**  `B − E = M·a·v̂`: with `B − C = ka·v̂` the
exit vertex lies at distance exactly `M·a` from `B` along `BC` — the mirror
of `X − (M−1)b·w = B/k ∈ AB`.  Cleared form of `k·a·v̂ − (k−M)a·v̂ = M·a·v̂`. -/
theorem exit_from_B (a M k : ℤ) : k * a - (k - M) * a = M * a := by ring

/-- **The `L4` ring identity.**  `c² = a² + bc`: the reason the `γ`-head
laying `b` lands its far vertex at `U/c = c/b` exactly. -/
theorem gamma_b_identity (e f : ℤ) :
    (f ^ 2) ^ 2 = (e * f) ^ 2 + (f ^ 2 - e ^ 2) * f ^ 2 := by ring

/-- **`b ∤ c`.**  `b = f² − e²` and `c = f²` with `gcd(e,f) = 1`: `b` would
divide `e² = f² − b` as well, hence `gcd(e², f²) = 1`, forcing `b = 1` —
impossible, `b ≥ 2e + 1 ≥ 5`.  This is what makes the `L4` staircase
violation strict. -/
theorem b_not_dvd_c (e f b : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) : ¬ b ∣ f ^ 2 := by
  intro hdvd
  have hbee : b ∣ e ^ 2 := by
    obtain ⟨t, ht⟩ := hdvd
    have ht1 : 1 ≤ t := by nlinarith [Nat.one_le_pow 2 f (show 0 < f by omega)]
    refine ⟨t - 1, ?_⟩
    have hms : b * t = b * (t - 1) + b := by
      rcases t with _ | t'
      · omega
      · simp [Nat.mul_succ]
    omega
  have hcop2 : Nat.Coprime (e ^ 2) (f ^ 2) := Nat.Coprime.pow _ _ hcop
  have hg : Nat.gcd (e ^ 2) (f ^ 2) = 1 := hcop2
  have hb1 : b ∣ 1 := by
    have h := Nat.dvd_gcd hbee hdvd
    rwa [hg] at h
  have hf : e + 1 ≤ f := hef
  have hsq : (e + 1) ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hf 2
  have hexp : (e + 1) ^ 2 = e ^ 2 + 2 * e + 1 := by ring
  have hle := Nat.le_of_dvd (by norm_num) hb1
  omega

/-- **`L1`: the `α`-head laying `b` dies.**  Its `c`-edge lies on the ray
`w = (c/b)·u − (a/b)·v̂`, of `BC`-cost `c/b` per unit length: the cost
`c·(c/b)` exceeds the `r = 2` room `c` exactly because `b < c`. -/
theorem row_b_head_dies (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    (f ^ 2 - e ^ 2) < f ^ 2 := by
  have h1 : 1 ≤ e ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
  omega

/-- **`L2`: the `β`-ray dichotomy is exclusive.**  `e(3f²−e²) = f³` would
give `e³ = f²(3e − f)`, so `f ∣ e³`, impossible for a coprime pair with
`f ≥ 2`.  Above the line the `β`-head's `c`-edge violates the `BC`-room;
below it, the staircase floor. -/
theorem beta_ray_no_equality (e f : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) : e * (3 * f ^ 2 - e ^ 2) ≠ f ^ 3 := by
  intro heq
  have hf2 : 2 ≤ f := by omega
  have he2f : e ^ 2 < 3 * f ^ 2 := by nlinarith
  have hz : (e : ℤ) * (3 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) = (f : ℤ) ^ 3 := by
    have := heq
    zify [he2f.le] at this
    linarith [this]
  have hdvd : (f : ℤ) ∣ (e : ℤ) ^ 3 := ⟨3 * e * f - f ^ 2, by linarith [hz]⟩
  have hdn : f ∣ e ^ 3 := by exact_mod_cast hdvd
  have hcop3 : Nat.Coprime (e ^ 3) f := hcop.pow_left 3
  have := Nat.Coprime.eq_one_of_dvd hcop3.symm hdn
  omega

/-- **`L3`: the `γ`-head laying `a` dies.**  Its `b`-edge's far vertex sits
at `(c + a, −c)` in `(u, v̂)`-coordinates: the piece `U ∈ [c, 2c)` of the
forced-row staircase has floor `−a`, and `−c < −a`. -/
theorem gamma_a_head_dies (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    f ^ 2 < f ^ 2 + e * f ∧ f ^ 2 + e * f < 2 * f ^ 2 ∧ e * f < f ^ 2 := by
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **The closure room at `r = 3` is short.**  `Δ = c − a = f(f−e) < b`:
every edge at a ray of `BC`-cost `≥ 1` overshoots the closing room of the
single common stop `a + 2c`. -/
theorem delta_lt_b (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    f * (f - e) < f ^ 2 - e ^ 2 := by
  have h1 : f * (f - e) + e * (f - e) = (f + e) * (f - e) := by ring
  have h2 : (f + e) * (f - e) = f ^ 2 - e ^ 2 := (Nat.sq_sub_sq f e).symm
  have h3 : 0 < e * (f - e) := Nat.mul_pos (by omega) (by omega)
  omega

/-- **The corridor flush is impossible below `e`.**  The rogue side of the
second chord is an edge-union summing, with its forced first letter `a`, to
`(x+1)·a + y·b + z·c`; a flush at the exit demands the total `r·c`.  For
`r < e` there is no solution: `f ∣ y` (the `f_dvd_nb` descent), then
`x + 1 ≡ (y/f)·e (mod f)`, and the two sides of the resulting cofactor
equation squeeze `Y > J` against `Y ≤ J`.  For `r ≥ e` the word
`a^f c^{r−e}` is a solution, so the bound is exact. -/
theorem corridor_no_flush (e f b r x y z : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hre : r < e)
    (heq : (x + 1) * (e * f) + y * b + z * f ^ 2 = r * f ^ 2) : False := by
  -- step 1: f ∣ y
  have hfy : f ∣ y := by
    refine Erdos634.Inflation.f_dvd_nb e f b y hcop hb ?_
    refine ⟨(r : ℤ) * f - (x + 1) * e - z * f, ?_⟩
    have hz : ((x : ℤ) + 1) * (e * f) + y * b + z * f ^ 2 = r * f ^ 2 := by
      exact_mod_cast heq
    linear_combination hz
  obtain ⟨Y, hY⟩ := hfy
  subst hY
  -- step 2: divide by f
  have hfne : (f : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have hz : ((x : ℤ) + 1) * e + Y * b + z * f = r * f := by
    have hcast : ((x : ℤ) + 1) * (e * f) + (f * Y) * b + z * f ^ 2
        = r * f ^ 2 := by exact_mod_cast heq
    apply mul_left_cancel₀ hfne
    linear_combination hcast
  -- step 3: x + 1 ≡ Y·e (mod f)
  have hbz : (b : ℤ) = f ^ 2 - e ^ 2 := by
    have : (b : ℤ) + e ^ 2 = f ^ 2 := by exact_mod_cast hb
    linarith
  have hdvd : (f : ℤ) ∣ ((x : ℤ) + 1 - Y * e) * e := by
    refine ⟨(r : ℤ) - z - Y * f, ?_⟩
    have : ((x : ℤ) + 1) * e + Y * (f ^ 2 - e ^ 2) + z * f = r * f := by
      rw [← hbz]; exact hz
    linear_combination this
  have hcopz : IsCoprime (f : ℤ) (e : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact_mod_cast hcop.symm
  have hjf : (f : ℤ) ∣ ((x : ℤ) + 1 - Y * e) := hcopz.dvd_of_dvd_mul_right hdvd
  obtain ⟨j, hj⟩ := hjf
  -- step 4: the cofactor equation j·e + Y·f + z = r
  have hkey : j * e + Y * f + z = r := by
    have hx1 : ((x : ℤ) + 1) = Y * e + f * j := by linarith [hj]
    have h2 : (Y * e + f * j) * e + Y * (f ^ 2 - e ^ 2) + z * f = r * f := by
      rw [← hx1, ← hbz]; exact hz
    have h3 : (j * e + Y * f + z) * f = r * f := by linear_combination h2
    exact mul_right_cancel₀ hfne h3
  have hY0 : (0 : ℤ) ≤ Y := Int.natCast_nonneg Y
  have hz0 : (0 : ℤ) ≤ (z : ℤ) := Int.natCast_nonneg z
  have hx0 : (1 : ℤ) ≤ (x : ℤ) + 1 := by omega
  have hez : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
  have hefz : (e : ℤ) < (f : ℤ) := by exact_mod_cast hef
  have hrez : (r : ℤ) < (e : ℤ) := by exact_mod_cast hre
  rcases lt_trichotomy j 0 with hjneg | hj0 | hjpos
  · -- j ≤ −1: Y·e ≥ 1 + J·f gives Y > J; Y·f ≤ r + J·e gives Y ≤ J
    set J : ℤ := -j with hJ
    have hJ1 : 1 ≤ J := by omega
    have h1 : Y * e ≥ 1 + J * f := by
      have : ((x : ℤ) + 1) = Y * e - f * J := by rw [hJ]; linarith [hj]
      nlinarith [hx0]
    have h2 : Y * f ≤ (r : ℤ) + J * e := by nlinarith [hkey, hz0]
    have hYJ1 : J < Y := by nlinarith
    have hYJ2 : Y < J + 1 := by nlinarith
    omega
  · -- j = 0: x + 1 = Y·e forces Y ≥ 1, then r ≥ f
    subst hj0
    have hx1 : ((x : ℤ) + 1) = Y * e := by linarith [hj]
    have hY1 : 1 ≤ Y := by nlinarith
    have : (f : ℤ) ≤ r := by nlinarith [hkey, hz0]
    omega
  · -- j ≥ 1: r = j·e + Y·f + z ≥ e
    have : (e : ℤ) ≤ r := by nlinarith [hkey, hY0, hz0]
    omega

/-- **The top-2 slot dies.**  At `k = M + 2` and `e ≥ 3`: the row side of
the second chord breaks only at `{c, 2c}` (`L1`–`L4`), the rogue side never
breaks at `c` (the `Δ`-forcing, `RogueChord.tvertex_forcing`) and cannot
flush `2c` — this instance.  With no common breakpoint both sides must
flush, and the rogue side cannot: the slot `M = k − 2` is rogue-free at
every member with `e ≥ 3`. -/
theorem top2_slot_dies (e f b x y z : ℕ) (he : 3 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : (x + 1) * (e * f) + y * b + z * f ^ 2 = 2 * f ^ 2) : False :=
  corridor_no_flush e f b 2 x y z (by omega) hef hcop hb (by omega) heq

/-- **The top-3 slot's flush core.**  At `k = M + 3` and `e ≥ 4` the rogue
side cannot flush `3c`; the single surviving common stop `a + 2c` closes on
a room of `Δ = c − a < b` (`delta_lt_b`) and dies — the closure layer is
verified exactly by `code/zfan_corridor.py` on every member `f ≤ 12`. -/
theorem top3_slot_flush_dies (e f b x y z : ℕ) (he : 4 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : (x + 1) * (e * f) + y * b + z * f ^ 2 = 3 * f ^ 2) : False :=
  corridor_no_flush e f b 3 x y z (by omega) hef hcop hb (by omega) heq

/-- The flush bound is exact: at `r = e` the word `a^f` flushes —
`f·a = e·c` is an identity, so `x + 1 = f`, `y = z = 0` solves the corridor
equation with `r = e`.  The mirror criterion stops exactly at `r < e`. -/
theorem flush_at_e (e f : ℤ) : f * (e * f) = e * f ^ 2 := by ring

/-!  ### The forced row's own arithmetic, and its exact scope

The forced row under everything above is the base side of `Δ_k` read as
`b^k`.  Below the wall scale that reading is *rigid*: the base side word of
a scale-`k` inflation is `b^k` outright for `k < f` — this is
`Inflation.b_side_rigid` (together with `Inflation.c_side_no_b` for the
`c`-side), proved independently in the boundary-word session; an identical
statement first written here was removed as its duplicate.  At `k = f` —
the wall scale, where `Δ_f` is the west corner block sitting on the
target's base — rigidity fails arithmetically: the base equation acquires
the whole family `a^{(j+1)f−e}·c^{f−(j+1)e}`, `1 ≤ j+1 ≤ ⌊f/e⌋`
(`base_side_wall_family` below; `Inflation`'s sharpness note exhibits the
`j = 0` member).

**The family is dead (2026-08-15, the A2 session): the wall-scale base
reads `b^f` after all.**  The kill is three banked steps, none new:

1.  *The `c`-side of `Δ_f` carries no `b`-edge.*  The `c`-side of a
    scale-`f` inflation has length `f·c = f³` — the **same** walk equation
    as the `m = 1` equal side, which is the `m = 1` lever one level down —
    and the region-local `γ`-trap holds verbatim (the region's `c`-side
    ends are its `α`- and `β`-corners, filled `{α}` (`CChord.fill_alpha`)
    and `{β}` (`BaseBetaCorners.corner_beta_unique`), neither carrying a
    `γ`; interior junctions are `π`-figures with at most one `γ`
    (`BaseBetaCorners.pi_vertex_gamma_le_one`); each `a`- or `b`-edge's
    tile has a `γ` at one end of that edge — the pigeonhole is
    `BaseBetaWalks.gamma_injection`/`c_edge_exists`).  So `R ≥ 1`, and
    `SideNoB.side_no_b_uncond` gives `Q = 0`.
2.  *The `α`-corner tile lays `b` on the base.*  The single tile at the
    region's `α`-corner has flanks `{b, c}`, one along the base, one along
    the `c`-side; step 1 forbids `b` on the `c`-side.
3.  *One `b` forces `b^f`* — `wall_base_dichotomy` below: the base
    equation has `f ∣ n_b` (mod-`f` residue, `Inflation.f_dvd_nb`) and
    `n_b ≤ f`, so `n_b ∈ {0, f}` and `n_b ≥ 1` pins `(0, f, 0)`.

`wall_base_reading` assembles 1+3: its inputs are the two side readings,
the `γ`-trap count, and the flank disjunction of step 2.  Geometric
obligations: the two sides of `Δ_f` are inside edge-unions (the
`WallChain.wall_two_sided` covering, ends blocked at the region's
corners), the corner and junction fills (`Dissection.lean`'s
vertex-multiplicity layer), and the faithfulness of the `(α,β)`-calculus
(`α/π` irrational, proved).  Engine verification: every family word at
every member `f ≤ 9` (55 instances) is `EXHAUSTED_NO_TILING` with the
other two sides left **free** over their full word lists (`b`-carrying
`c`-words included, transverse `a`-word included), standard controls
`FOUND_TILING` — `code/a2_wall_family.py`.  Consequently every rogue-slot
kill at scale `k = f` now stands on the same standing hypotheses as the
`k < f` kills: the `b^f` forced-row input is no longer a condition. -/

/-- **The wall-scale base family.**  At `k = f` the base equation is solved
by `x = (j+1)f − e`, `y = 0`, `z = f − (j+1)e` for every `j+1 ≤ f/e`:
`b^f` is not forced by arithmetic *alone* on the wall.  (The `j = 0`
member is the witness of `Inflation`'s sharpness note; this is the full
family.  The geometric kill is `wall_base_reading` below.) -/
theorem base_side_wall_family (e f j : ℤ) :
    ((j + 1) * f - e) * (e * f) + (f - (j + 1) * e) * f ^ 2
      = f * (f ^ 2 - e ^ 2) := by ring

/-- **One `b` on the wall forces `b^f`.**  The base equation at `k = f`
has `f ∣ n_b` — reduce mod `f`: every other term vanishes and
`b ≡ −e² (mod f)` with `gcd(e, f) = 1` (`Inflation.f_dvd_nb`) — and the
inventory `n_b·b ≤ f·b` gives `n_b ≤ f`; so `n_b ∈ {0, f}`, and `n_b ≥ 1`
leaves `n_b = f` with the other counts vanishing by length.  Together with
`base_side_wall_family` this is the complete wall-scale dichotomy: the
base of `Δ_f` reads `b^f` or is `b`-free. -/
theorem wall_base_dichotomy (e f b na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hnb : 1 ≤ nb)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = f * b) :
    na = 0 ∧ nb = f ∧ nc = 0 := by
  have hbpos : 0 < b := by
    have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
    omega
  -- f ∣ n_b, via (f : ℤ) ∣ n_b·b and b ≡ −e² (mod f)
  have hz : (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * b + (nc : ℤ) * (f : ℤ) ^ 2
      = (f : ℤ) * b := by exact_mod_cast heq
  have hfd : f ∣ nb :=
    Erdos634.Inflation.f_dvd_nb e f b nb hcop hb
      ⟨(b : ℤ) - (na : ℤ) * e - (nc : ℤ) * f, by linear_combination hz⟩
  -- n_b ≤ f by inventory
  have hnbf : nb ≤ f := by
    have h1 : nb * b ≤ f * b := by omega
    exact Nat.le_of_mul_le_mul_right h1 hbpos
  have hnbeq : nb = f := by
    rcases hfd with ⟨j, hj⟩
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp at hj; omega
    · have : f ≤ f * j := Nat.le_mul_of_pos_right f h
      omega
  subst hnbeq
  have hef0 : 0 < e * f := Nat.mul_pos (by omega) (by omega)
  have hf2 : 0 < f ^ 2 := pow_pos (by omega : 0 < f) 2
  constructor
  · by_contra h
    have : 1 * (e * f) ≤ na * (e * f) := Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨rfl, ?_⟩
  by_contra h
  have : 1 * f ^ 2 ≤ nc * f ^ 2 := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The wall-scale base reading, assembled.**  Inputs: the base reading
`(n_a, n_b, n_c)` of `Δ_f`'s `B`-side, the `c`-side reading `(P, Q, R)`,
the `γ`-trap count `R ≥ 1` (`BaseBetaWalks.gamma_injection` on the
region's `c`-side), and the flank disjunction — the single `α`-corner tile
lays its `b`-flank on the base or on the `c`-side (`CChord.fill_alpha`
pins the corner to one tile; `{b, c}` are `α`'s flanks).  Conclusion: the
base reads exactly `b^f`, killing every member of
`base_side_wall_family`'s family at once.  The `Q ≥ 1` horn dies on
`SideNoB.side_no_b_uncond` — the `m = 1` lever `f·c = f³`, acting one
level down. -/
theorem wall_base_reading (e f b na nb nc P Q R : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = f * b)
    (hcside : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) (hflank : 1 ≤ nb ∨ 1 ≤ Q) :
    na = 0 ∧ nb = f ∧ nc = 0 := by
  have hbmul : b + e * e = f * f := by
    have h1 : e ^ 2 = e * e := sq e
    have h2 : f ^ 2 = f * f := sq f
    omega
  rcases hflank with hnb | hQ
  · exact wall_base_dichotomy e f b na nb nc he hef hcop hb hnb heq
  · exfalso
    have hQ0 : Q = 0 :=
      Erdos634.SideNoB.side_no_b_uncond hcop hef hbmul hcside hgamma
    omega

end Erdos634.RogueMirror

#print axioms Erdos634.RogueMirror.generator_x
#print axioms Erdos634.RogueMirror.exit_x
#print axioms Erdos634.RogueMirror.exit_from_B
#print axioms Erdos634.RogueMirror.gamma_b_identity
#print axioms Erdos634.RogueMirror.b_not_dvd_c
#print axioms Erdos634.RogueMirror.beta_ray_no_equality
#print axioms Erdos634.RogueMirror.delta_lt_b
#print axioms Erdos634.RogueMirror.corridor_no_flush
#print axioms Erdos634.RogueMirror.top2_slot_dies
#print axioms Erdos634.RogueMirror.top3_slot_flush_dies
#print axioms Erdos634.RogueMirror.base_side_wall_family
#print axioms Erdos634.RogueMirror.wall_base_dichotomy
#print axioms Erdos634.RogueMirror.wall_base_reading
