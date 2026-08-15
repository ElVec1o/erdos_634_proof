import Mathlib.Tactic
import Erdos634.CChord

/-!
# The transverse corner block: the forced opening, and the squeeze ladder

Erdős #634, base-`β` branch.  At scale `k = f` the `a`-side of an inflation `Δ_f` admits the word
`c^e` (`Inflation.a_side_all_c`); the **transverse branch** is the configuration with that word, the
`β`-corner tile laying `c` along `BC` and `a` along `AB`.  It is the last configuration of the
`W`-induction not excluded by uniform argument: killed by hand at `e = 1`, by 61 exhaustive engine
searches over 13 members for `e ≥ 2`, and by the exact 2-D patch forcer
(`code/swap_patch_search.py --scenario transverse`, three demand layers) at
`(2,3) (3,4) (2,5) (3,5) (4,5) (5,6) (2,7) (6,7) (7,8) (8,9)` — every close pair `e = f−1`
with `f ≤ 9`.

This file banks the arithmetic cores of what **is** uniform.  Frame: `B` the `β`-corner,
`J_j = B + jc` along `BC`, `P_2 = B + a` along `AB`, `K_j = P_2 + jc` along the line `ℓ1 ∥ BC`
through `P_2`; wedge fills are counted as in `CChord`: a wedge `Xα + Yβ` filled by corner counts
`(x, y, z)` of `(α, β, γ)` satisfies `x + 2z = X`, `y + z = Y` (`γ = 2α + β`).

## The forced opening (uniform in the member — no size or close-pair hypothesis)

*  `b_seg_single` — **a straight stretch of length `b` covered flush at both ends is a single
   `b`-edge.**  `n_c = 0` and `n_b ≤ 1` by size; the residual case `n_a·a = b` dies by coprimality:
   `e ∣ f²` forces `e = 1`, then `f ∣ f² − 1` forces `f = 1`.  Applied to `T_0`'s `b`-chord
   `[J_1, P_2]` — both of whose end-extensions leave `Δ_f` through `BC` resp. `AB`, so the far-side
   covering is flush at both ends — it yields a full-edge partner tile.

*  `residual_alpha_beta` — the `π`-figure at `P_2 ∈ AB` after `T_0`'s `γ` is `α + β`, and its fill
   is exactly `{α, β}` (no `γ`): the **mirror** partner, which presents `γ` at `P_2`, is dead, so
   the partner is the **direct** `D_0` (its `α` at `P_2`), and the rest of the `P_2` figure is one
   `β`-tile — the head `W_0` of the second strip.

*  `j1_figure` — the `π`-figure at `J_1 ∈ BC` containing `T_0`'s `α` and `D_0`'s `γ` is exactly
   `{α, β, γ}`: one `β` remains.  Its tile must put its `c`-flank on `BC` (the branch's `c`-grid)
   and its `a`-flank flush on `[J_1, K_1]`, so it is the translate `T_1 = T_0 + c·(−v̂)`.

Hence `{T_0, D_0, T_1}` plus the `P_2` decomposition are forced for **every** member, and the
first-strip chain begins direct — the `AB`-boundary `γγ` argument of the swap-kill session, now
member-uniform.  Beyond `J_2` the forcing genuinely branches (the chord `[J_2, K_1]` may be met by
an overhanging `a`- or `c`-edge, `K_1` being interior), which is where the patch engine takes over.

## The `C`-corner demands

*  `c_corner_after_beta` — if the last `BC` tile presents `β` at `C`, the residual `2α` fills as
   `{α, α}`.  With `residual_alpha_beta` (the `α` case) this classifies both `C`-corner splits.
*  `c_corner_no_gamma` — in either case no fill tile presents `γ` at `C`: the **direct** partner of
   the last `BC` tile is dead at `C`, so a full-edge partner there is the **mirror**.  Against the
   opening this is the collision the induction rides: direct demanded at the first block, mirror at
   the last.  At `e = 1` first = last and the branch dies outright; for `e ≥ 2` the collision must
   propagate through `e − 1` interior blocks, where the mirror is *not* angle-excluded (an interior
   vertex has `2π`), and the uniform argument is open.

## The squeeze ladder (where every engine kill sits)

The line through `B + s·a·(−u)` parallel to `BC` (depth `s` along `AB`) meets the base after run
`t_s` with `t_s = e·f² − s·e²` (`strip_hit`), an integer.  The kills of the patch engine
concentrate at the foot of `ℓ1` (`x = b(f² − e)/f`, the recorded "squeeze between the partner strip
and the base near `C`"), and the ladder identities say why the region is critical:

*  `strip_gap_b` — the `ℓ1` run exceeds the `(e−1)` `c`-edges of the `D`-chain by exactly `b`.
*  `strip_shrink` — depth `s` exceeds `(e−s)` `c`-edges by `s·b`: the strips are self-similar with
   `e` decrementing per layer, which is the reduction toward the killed `e = 1` configuration.
*  `strip_window` — consecutive base feet are `e·b/f` apart (stated cleared by `f`).
*  `phit_not_breakpoint` — **the foot of `ℓ_s` is never a breakpoint of the base word**: the base
   covering breaks at integer distances from `C`, the foot sits at `s·e·b/f`, and `f ∣ s·e·b`
   forces `f ∣ s` by two coprimalities.  So an edge along `ℓ_s` flush at the base ends at a point
   interior to a base edge — a tile corner is demanded where none can lie flush along the base.
   This is the arithmetic behind the engine's `angle-nofill` kills at the feet.

## The complete block dies: the diagonal wall and the mirror chain

The transverse block, if complete, is the tile at scale `e` in transverse orientation: the lattice
`T^{(s)}_j = T_0 + s·a·(−u) + j·c·(−v̂)` (`s + j ≤ e − 1`) with direct partners `D^{(s)}_j`
(`s + j ≤ e − 2`), `e(e+1)/2 + e(e−1)/2 = e²` tiles (`block_count`), every interior lattice vertex
carrying the full `2π = 2(α+β+γ)`.  Its inner boundary is the **diagonal** from `C` to the point
`(e·a, 0)` on `AB`, made of `e` collinear lattice `b`-edges (`law_cos_beta` is the collinearity's
length core).  Both diagonal ends have blocked extensions (`C` a corner, `(e·a, 0)` on `AB`), so the
far side is a flush edge-union of length `e·b` — and `Inflation.b_side_rigid` (`e ≤ f − 1 < f`)
forces it to be **exactly `b^e`**, breakpoints at the lattice points `P_i`.  Each far-side tile
`R_i` spans `[P_i, P_{i+1}]` with `α` at one end, `γ` at the other, and:

* at `C` the fill admits no `γ` (`c_corner_no_gamma`), so `R_0` has `α` at `P_0 = C` — the
  **mirror** demand;
* at each interior `P_i` the far side is a `π`-figure carrying at most one `γ`
  (`pi_at_most_one_gamma`), so `γγ` is forbidden and `R_i`'s `α`-end propagates:
  `α` at `P_i` forces `α` at `P_{i+1}` (`chain_forces_alpha`) — the chain replicates **direct**;
* hence `R_{e−1}` presents `γ` at `P_e = (e·a, 0) ∈ AB`, where the lattice tile `T^{(e−1)}_0`
  already has its `γ`: two `γ`s at a `π`-point (`pi_at_most_one_gamma` again).  **Dead.**

At `e = 1` the block is a single tile and this is precisely the known hand kill; the argument is
uniform in `(e, f)` with no size or close-pair hypothesis.  So no tiling of `Δ_f` in the transverse
branch contains the complete scale-`e` block: any survivor must *straddle* the block's diagonal.
The straddling (deviant) branches are the ones the patch engine enumerates and kills per member;
`double_b_chord` and the ladder above are the word-level tools that prune them (in the `W^c`
deviation the chord `[J_2, P_3]` is straight of length `2b` and its far side is forced `b·b` for
every `e ≥ 2`, so the overhang moves die there and the forcing extends by `{D'_0, D_1, T_2}`).

## Status

Forced opening, the ladder, and the complete-block kill: PROVED here as arithmetic cores; the
geometric inputs — edge-unions on straight stretches with blocked ends, wedge-fill bookkeeping,
edges never crossing edge-covered lines, the `c`-grid discipline of the branch — are the named
standing hypotheses of `Dissection`/`ChordInterface`.  The straddling branches for `e ≥ 2`:
VERIFIED per member (engine searches and the exact patch forcer), plus the trace-level check that
the engine's forced prefixes at `(2,3)`, `(3,4)` are exactly `{T_0, D_0, T_1, …}` and that the
`(2,3)` main-branch kill site is `(e·a, 0)` — the predicted collision point.  A uniform straddle
kill is **open**; the residual set is exactly: members `e ≥ 2` outside the searched list, straddling
configurations only.  Axiom-clean.
-/

namespace Erdos634.TransverseChain

/-- **A flush stretch of length `b` is a single `b`-edge — every member.**  The two-or-more-edge
decompositions die by size (`c > b`, `2b > b`) and by coprimality (`n_a·a = b` needs `e ∣ f²`,
hence `e = 1`, then `f ∣ f² − 1`).  No close-pair hypothesis: the `b`-smallness of the close pairs
is not what carries this. -/
theorem b_seg_single (e f b na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = b) :
    na = 0 ∧ nb = 1 ∧ nc = 0 := by
  have hf2 : 2 ≤ f := by omega
  have hbpos : 0 < b := by
    have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
    omega
  have he2 : 0 < e ^ 2 := pow_pos (by omega) 2
  have hnc : nc = 0 := by
    by_contra h
    have : 1 * f ^ 2 ≤ nc * f ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  subst hnc
  have hnb1 : nb ≤ 1 := by
    by_contra h
    have : 2 * b ≤ nb * b := Nat.mul_le_mul_right _ (by omega)
    omega
  interval_cases nb
  · -- the pure-`a` split `n_a·a = b`
    exfalso
    have heq' : na * (e * f) = b := by omega
    have hedvd : e ∣ b := ⟨na * f, by rw [← heq']; ring⟩
    have hef2 : e ∣ f ^ 2 := by
      have h1 : e ∣ b + e ^ 2 := Nat.dvd_add hedvd ⟨e, by ring⟩
      rwa [hb] at h1
    have he1 : e = 1 := by
      have h2 : Nat.gcd e (f ^ 2) = 1 := Nat.Coprime.gcd_eq_one (hcop.pow_right 2)
      have h3 : e ∣ Nat.gcd e (f ^ 2) := Nat.dvd_gcd dvd_rfl hef2
      exact Nat.dvd_one.mp (h2 ▸ h3)
    subst he1
    have hfdvd : f ∣ b := ⟨na, by rw [← heq']; ring⟩
    have h4 : f ∣ f ^ 2 := ⟨f, by ring⟩
    rw [← hb] at h4
    have h5 := Nat.dvd_sub h4 hfdvd
    have h6 : b + 1 ^ 2 - b = 1 := by omega
    rw [h6] at h5
    have := Nat.le_of_dvd (by omega) h5
    omega
  · -- `n_b = 1`: nothing else fits
    have heq' : na * (e * f) = 0 := by omega
    rcases Nat.mul_eq_zero.mp heq' with h | h
    · exact ⟨h, rfl, rfl⟩
    · exfalso; have : 0 < e * f := Nat.mul_pos (by omega) (by omega); omega

/-- **The `P_2` figure: the fill of `α + β` is `{α, β}`, never a `γ`.**  The mirror partner of
`T_0` presents `γ` at `P_2` and needs `z ≥ 1`; the fill has `z = 0`, so the partner is direct and
the leftover is a single `β` — the head of the second strip.  (Same core as
`CChord.fill_alpha_beta`; restated here as the site is different and the consequence — direct, not
mirror — is the load-bearing one.) -/
theorem residual_alpha_beta (x y z : ℕ) (h1 : x + 2 * z = 1) (h2 : y + z = 1) :
    x = 1 ∧ y = 1 ∧ z = 0 := CChord.fill_alpha_beta x y z h1 h2

/-- **The `J_1` figure: a `π`-figure carrying a `γ` is exactly `{α, β, γ}`.**  The `α`-presence
need not even be assumed: `z ≥ 1` alone forces `(x, y, z) = (1, 1, 1)`.  With `D_0`'s `γ` and
`T_0`'s `α` placed, one `β` remains; the `c`-grid on `BC` then pins its flanks and forces the
translate `T_1`. -/
theorem j1_figure (x y z : ℕ) (h1 : x + 2 * z = 3) (h2 : y + z = 2)
    (hz : 1 ≤ z) : x = 1 ∧ y = 1 ∧ z = 1 := by omega

/-- **The `C`-corner residual after a `β`: `2α` fills as `{α, α}`.**  Companion of the `α` case
(`residual_alpha_beta`): together they classify the split `γ`-corner `{2α, β}` of the transverse
branch. -/
theorem c_corner_after_beta (x y z : ℕ) (h1 : x + 2 * z = 2) (h2 : y + z = 0) :
    x = 2 ∧ y = 0 ∧ z = 0 := by omega

/-- **No fill tile presents `γ` at `C`.**  Whichever end the last `BC` tile presents (`α`, leaving
`X,Y = 1,1`, or `β`, leaving `2,0`), the fill has `z = 0`: the direct partner of the last tile is
dead at `C`, so a full-edge partner there is the mirror — the demand that collides with the direct
opening. -/
theorem c_corner_no_gamma (x y z X Y : ℕ)
    (hres : (X = 1 ∧ Y = 1) ∨ (X = 2 ∧ Y = 0))
    (h1 : x + 2 * z = X) (h2 : y + z = Y) : z = 0 := by
  rcases hres with ⟨hX, hY⟩ | ⟨hX, hY⟩ <;> omega

/-- **A `π`-figure carries at most one `γ`.**  The step rule of the mirror chain: two adjacent
far-side tiles cannot both present `γ` at a shared diagonal point, and the chain's terminal `γ`
cannot join the lattice `γ` at `(e·a, 0)`. -/
theorem pi_at_most_one_gamma (x y z : ℕ) (h1 : x + 2 * z = 3) (h2 : y + z = 2) : z ≤ 1 := by
  omega

/-- **The mirror chain propagates.**  `o i` says the `i`-th far-side tile has its `α` at the near
end `P_i` (hence its `γ` at `P_{i+1}`).  The no-`γγ` rule supplies the step, `c_corner_no_gamma`
the base, and the conclusion hands `R_{e−1}`'s `γ` to the `AB`-endpoint.  The glue is bare
induction; the content sits in the two cited fills. -/
theorem chain_forces_alpha (o : ℕ → Bool) (h0 : o 0 = true)
    (hstep : ∀ i, o i = true → o (i + 1) = true) : ∀ i, o i = true := by
  intro i
  induction i with
  | zero => exact h0
  | succ n ih => exact hstep n ih

/-- **The transverse block count.**  `e(e+1)/2` lattice tiles and `e(e−1)/2` direct partners make
`e²` — the tile at scale `e`, as `Inflation.a_side_all_c` predicts (stated cleared by `2`). -/
theorem block_count (e : ℤ) : e * (e + 1) + e * (e - 1) = 2 * e ^ 2 := by ring

/-- **The diagonal is straight of length `e·b`: the length core.**  The lattice `b`-vector is
`a·(−u) − c·(−v̂)`, and the law of cosines at `β` — `cos β = e(3f²−e²)/(2f³)` — clears to this
identity, which says exactly `|a·u − c·v̂|² = b²`: consecutive lattice `b`-edges are collinear and
the wall from `C` to `(e·a, 0)` is one straight stretch. -/
theorem law_cos_beta (e f : ℤ) :
    (e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2 = e ^ 2 * (3 * f ^ 2 - e ^ 2) := by
  ring

/-- **The double-`b` chord is `b·b` — every member with `e ≥ 2`.**  In the `W^c` deviation the
stretch `[J_2, P_3]` (length `2b`, both end-extensions blocked by `BC` and `AB`) must decompose as
two `b`-edges with the breakpoint at `K_1`: `n_c = 1` needs `e ∣ f²`; `n_b = 1` leaves `n_a·a = b`
(dead by `b_seg_single`'s core); `n_b = 0` needs `e ∣ 2f²`, hence `e = 2` and `f ∣ 4` against
coprimality.  The overhanging `a`- and `c`-moves at `J_2` die here, and the forcing extends by
`{D'_0, D_1, T_2}`.  Sharpness: at `(1,2)` the words `(1,0,1)` and `(3,0,0)` do decompose `2b`. -/
theorem double_b_chord (e f b na nb nc : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = 2 * b) :
    na = 0 ∧ nb = 2 ∧ nc = 0 := by
  have hbpos : 0 < b := by
    have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
    omega
  have he2 : 0 < e ^ 2 := pow_pos (by omega) 2
  have hblt : b < f ^ 2 := by omega
  have hbz : (b : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hb
  have hgcd : e ∣ f ^ 2 → e = 1 := fun hd => by
    have h2 : Nat.gcd e (f ^ 2) = 1 := Nat.Coprime.gcd_eq_one (hcop.pow_right 2)
    have h3 : e ∣ Nat.gcd e (f ^ 2) := Nat.dvd_gcd dvd_rfl hd
    exact Nat.dvd_one.mp (h2 ▸ h3)
  -- n_c ≤ 1, and n_c = 1 forces e ∣ f², dead for e ≥ 2
  have hnc : nc = 0 := by
    have hnc1 : nc ≤ 1 := by
      by_contra h
      have h2 : 2 * f ^ 2 ≤ nc * f ^ 2 := Nat.mul_le_mul_right _ (by omega)
      omega
    interval_cases nc
    · rfl
    · exfalso
      have hnb0 : nb = 0 := by
        by_contra h
        have h2 : 1 * b ≤ nb * b := Nat.mul_le_mul_right _ (by omega)
        omega
      subst hnb0
      have heq' : na * (e * f) + f ^ 2 = 2 * b := by omega
      have hz1 : (e : ℤ) ∣ 2 * (b : ℤ) - (f : ℤ) ^ 2 := by
        refine ⟨(na : ℤ) * f, ?_⟩
        have hc : (na : ℤ) * ((e : ℤ) * f) + (f : ℤ) ^ 2 = 2 * b := by exact_mod_cast heq'
        linear_combination -hc
      have hz2 : (e : ℤ) ∣ 2 * (b : ℤ) - 2 * (f : ℤ) ^ 2 :=
        ⟨-2 * e, by linear_combination 2 * hbz⟩
      have hz3 : (e : ℤ) ∣ (f : ℤ) ^ 2 := by
        have h4 := dvd_sub hz1 hz2
        have h5 : (2 * (b : ℤ) - f ^ 2) - (2 * b - 2 * f ^ 2) = (f : ℤ) ^ 2 := by ring
        rwa [h5] at h4
      have : e = 1 := hgcd (by exact_mod_cast hz3)
      omega
  subst hnc
  have hnb2 : nb ≤ 2 := by
    by_contra h
    have : 3 * b ≤ nb * b := Nat.mul_le_mul_right _ (by omega)
    omega
  interval_cases nb
  · -- n_a·a = 2b: e ∣ 2f² ⟹ e = 2, then f ∣ 4 against gcd(2, f) = 1
    exfalso
    have heq' : na * (e * f) = 2 * b := by omega
    have hedvd : e ∣ 2 * b := ⟨na * f, by rw [← heq']; ring⟩
    have hedvd2 : e ∣ 2 * f ^ 2 := by
      have h1 : e ∣ 2 * b + 2 * e ^ 2 := Nat.dvd_add hedvd ⟨2 * e, by ring⟩
      have h2 : 2 * b + 2 * e ^ 2 = 2 * f ^ 2 := by omega
      rwa [h2] at h1
    have hetwo : e ∣ 2 := (hcop.pow_right 2).dvd_of_dvd_mul_right hedvd2
    have he2' : e = 2 := by
      have := Nat.le_of_dvd (by norm_num) hetwo
      omega
    subst he2'
    -- n_a·2f = 2b, so n_a·f = b and f ∣ f² − b = 4
    have h6 : na * (2 * f) = 2 * (na * f) := by ring
    have hnaf : na * f = b := by omega
    have hfb : f ∣ b := ⟨na, by rw [← hnaf]; ring⟩
    have hff : f ∣ f ^ 2 := ⟨f, by ring⟩
    have hf4 : f ∣ 4 := by
      have h4 := Nat.dvd_sub hff hfb
      have h5 : f ^ 2 - b = 4 := by omega
      rwa [h5] at h4
    have hfle : f ≤ 4 := Nat.le_of_dvd (by norm_num) hf4
    interval_cases f
    · rcases hf4 with ⟨m, hm⟩; omega
    · exact absurd hcop (by decide)
  · -- n_a·a = b: dead by the b_seg core
    exfalso
    have heq' : na * (e * f) = b := by omega
    have hedvd : e ∣ b := ⟨na * f, by rw [← heq']; ring⟩
    have hef2 : e ∣ f ^ 2 := by
      have h1 : e ∣ b + e ^ 2 := Nat.dvd_add hedvd ⟨e, by ring⟩
      rwa [hb] at h1
    have := hgcd hef2
    omega
  · -- n_b = 2: nothing else fits
    have heq' : na * (e * f) = 0 := by omega
    rcases Nat.mul_eq_zero.mp heq' with h | h
    · exact ⟨h, rfl, rfl⟩
    · exfalso; have : 0 < e * f := Nat.mul_pos (by omega) (by omega); omega

/-- **The close-pair chain forcing.**  On the family `e = f − 1`, `f ≥ 5`, an `a`-edge is longer
than the whole double-`b` diagonal (`a > 2b`), so at every junction chord `[J_j, K_{j-1}]` the
overhanging `a`-move overruns the diagonal's `AB`-endpoint and dies by containment; with the
mirror dead by the fills, the entire `BC` chain `T_0 D_0 T_1 D_1 …` is forced tile by tile, and
the branching retreats strictly below the first strip.  This is where the smallness of
`b = 2f − 1` finally acts: engine traces confirm the all-`1/1` prefix at `(4,5)` and the deep
forced prefixes at `(5,6)`, `(6,7)`.  Sharp: at `f = 3, 4` (i.e. `(2,3)`, `(3,4)`) `a < 2b` and
the overhang move is genuinely live — those trees branch at `J_2`. -/
theorem a_overruns_double_b (e f : ℕ) (he : e + 1 = f) (hf : 5 ≤ f) :
    2 * (f ^ 2 - e ^ 2) < e * f := by
  have h3 : 1 ≤ f := by omega
  have h4 : f ^ 2 - e ^ 2 = 2 * f - 1 := by
    have he' : e = f - 1 := by omega
    subst he'
    have h2 : (f - 1) ^ 2 + (2 * f - 1) = f ^ 2 := by zify [h3, show 1 ≤ 2 * f by omega]; ring
    omega
  have h5 : e * f + f = f ^ 2 := by
    have he' : e = f - 1 := by omega
    subst he'
    zify [h3]; ring
  have h6 : 5 * f ≤ f * f := Nat.mul_le_mul_right f hf
  have h7 : f ^ 2 = f * f := sq f
  omega

/-- The `−v̂` ray from depth `s·a` on `AB` meets the base after run `t_s = e·f² − s·e²`: the
cleared form of `t_s = (f·c − s·a)·e/f`. -/
theorem strip_hit (e f s : ℤ) : (f * f ^ 2 - s * (e * f)) * e = (e * f ^ 2 - s * e ^ 2) * f := by
  ring

/-- **The squeeze stretch.**  The `ℓ1` run to the base exceeds the `(e−1)` `c`-edges of the
`D`-chain by exactly `b`. -/
theorem strip_gap_b (e f : ℤ) : (e * f ^ 2 - e ^ 2) - (e - 1) * f ^ 2 = f ^ 2 - e ^ 2 := by
  ring

/-- **Self-similar shrink.**  Depth `s` exceeds `(e−s)` `c`-edges by `s·b`: each strip decrements
`e` by one, the reduction toward the killed `e = 1` configuration. -/
theorem strip_shrink (b e f s : ℤ) (hb : b = f ^ 2 - e ^ 2) :
    (e * f ^ 2 - s * e ^ 2) - (e - s) * f ^ 2 = s * b := by
  subst hb; ring

/-- **The base window.**  Consecutive base feet are `e·b/f` apart, stated cleared by `f`. -/
theorem strip_window (b e f s : ℤ) :
    b * (f ^ 2 - s * e) - b * (f ^ 2 - (s + 1) * e) = e * b := by
  ring

/-- **The foot of `ℓ_s` is never a breakpoint of the base word** (`1 ≤ s < f`).  Breakpoints sit at
integer distances from `C`; the foot sits at `s·e·b/f`; and `f ∣ s·e·b` forces `f ∣ s` since `f` is
coprime to `e` and to `b` (`b ≡ −e² (mod f)`).  An edge-anchored strip foot therefore lands strictly
inside a base edge — the arithmetic core of the engine's kills at the squeeze. -/
theorem phit_not_breakpoint (e f b s : ℕ)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (hs1 : 1 ≤ s) (hsf : s < f) (hdvd : f ∣ s * e * b) : False := by
  have hcopb : Nat.Coprime f b := by
    have h1 : Nat.gcd f b ∣ f := Nat.gcd_dvd_left f b
    have h2 : Nat.gcd f b ∣ b := Nat.gcd_dvd_right f b
    have h4 : Nat.gcd f b ∣ f ^ 2 := h1.trans ⟨f, by ring⟩
    rw [← hb] at h4
    have h3 : Nat.gcd f b ∣ e ^ 2 := (Nat.dvd_add_right h2).mp h4
    have h6 : Nat.gcd f b ∣ Nat.gcd f (e ^ 2) := Nat.dvd_gcd h1 h3
    have h7 : Nat.gcd f (e ^ 2) = 1 := Nat.Coprime.gcd_eq_one (hcop.symm.pow_right 2)
    exact Nat.dvd_one.mp (h7 ▸ h6)
  have h9 : f ∣ s * e := hcopb.dvd_of_dvd_mul_right hdvd
  have h10 : f ∣ s := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right h9
  have := Nat.le_of_dvd (by omega) h10
  omega

end Erdos634.TransverseChain

#print axioms Erdos634.TransverseChain.b_seg_single
#print axioms Erdos634.TransverseChain.residual_alpha_beta
#print axioms Erdos634.TransverseChain.j1_figure
#print axioms Erdos634.TransverseChain.c_corner_no_gamma
#print axioms Erdos634.TransverseChain.pi_at_most_one_gamma
#print axioms Erdos634.TransverseChain.chain_forces_alpha
#print axioms Erdos634.TransverseChain.double_b_chord
#print axioms Erdos634.TransverseChain.strip_shrink
#print axioms Erdos634.TransverseChain.phit_not_breakpoint
