import Erdos634.Inflation
import Erdos634.SidePRange
import Erdos634.EpredWedgeClearance
import Erdos634.WallsCircular
import Erdos634.Interface

/-!
# The family `e = f − 1` under `p = 0`: the `(0,e,2e)` column, the letter budget, and what it
# refutes

Erdős #634.  Written 2026-09-12 against Target B of `private/ROOM/data/VERDICT.md` (thick members
`e = f − 1`, `N = 2f² + 2f − 1`; every prime in the family is `≡ 11 (mod 12)`,
`N1GapSubGolden.epred_prime_mod_twelve`).

## The one geometric input, and its exact Lean status

`thm:efminus1` (companion, `\lab{CONJECTURE}`; the identical statement is PROVED in the main paper
after `cor:pbound`, "`p = 0` on every equal side at every member with `e = f − 1`") says every
equal side of the `m = 1` target reads `c^f`.  Its proof is `cor:pbound`'s `n_c ≥ 2` — the apex
`c`-edge (real, `SideWalk.equal_side_no_b_of_gammatrap`) **plus the `c` immediately below the
first junction (`thm:secondc`)** — and the side arithmetic.  In Lean, `thm:secondc`'s content is
reduced to a single named exclusion (`SideWalk.apex_edge_and_next_of_gammatrap`: the edge below the
apex `c` is an `a` or a `c`, and the `a` is not yet excluded).  So:

* the **arithmetic tail** of `thm:efminus1` is proved here (`side_p_zero_of_two_c`,
  `epred_side_no_a`): on `e = f − 1`, `n_c ≥ 2` forces `P = Q = 0` on the side;
* the **geometric premise** `n_c ≥ 2` remains exactly `thm:secondc`'s open `a`-exclusion.  Every
  theorem below that uses `p = 0` carries it as the hypothesis `hR : 2 ≤ R` (or as the two letters
  it forces on the base word), never silently.

## Step 2 of the target: the column `(0, e, 2e)`

`rem:n1conditional`/`prop:n1fromwalls`: in that column no base edge is an `a`, so both corner tiles
lay `c` on the base, hence `a` on their equal side (flanks of `β`, `TilePlacement.c_corner_side_a`),
so `P > 0` on each side.  `column_zero_side_word` shows that on `e = f − 1` a side with `P > 0` is
forced to read exactly `a^f c` — `f` `a`-edges and the single apex `c`; `column_zero_dies_of_two_c`
kills it with `n_c ≥ 2`.  Note that this is *precisely* the configuration `thm:secondc` excludes
(one `c` at the apex, an `a` directly below it): the column's death and `thm:secondc` are the same
open fact in Lean.  The link "corner lays `c` on the base ⟹ the side chain's `P > 0`" is the
placement step recorded open at `lem:ccornerside`'s `PAPER_MAP` row; it enters as `hPpos`.

## Step 3, the residue — and the negative that falls out of the letter budget

With `p = 0` on **both** sides, both corner tiles lay `c` on their side and therefore `a` on the
base: the base word begins and ends with `a`, so `x ≥ 2`.  The surviving columns of
`EpredBaseColumns`/`EpredWedgeClearance` are then `(f−k, (k+1)f−1, f−1−k)` for
`0 ≤ k ≤ min(f−3, ⌊f/2⌋)` — listed exactly at `N = 23, 59, 83` in `survivors_23/59/83` — and
**none of them is touched by any tool in the corpus**: the count filters are already applied, the
apex/mismatch-ray results are column-independent, and `T_mid` needs the double cut.

What the letter budget *does* give is a sharp negative, `no_prefix_of_length_fa`:

> On `e = f − 1`, a base word that begins and ends with `a` and carries at most `f` letters `a`
> has **no prefix (and, by reversal, no suffix) of total length `f·a = e·c`**.

The only two words of length `f·a` are `a^f` and `c^{e}` (`prefix_ec`, via
`Inflation.a_side_no_b`/`a_side_words` at scale `k = f`); the first needs `f + 1` letters `a`
once the last letter is an `a`, the second needs the first letter to be a `c`.  Consequences,
each stated separately below:

1. **Hypothesis (walls) is refuted on the whole family**, both halves, by `p = 0` alone.  The west
   block's feet are `a^f` from the corner (`west_block_never_complete_epred`); the east block's
   foot is a `c` at the corner (`east_block_never_complete_epred`).  This is `WallsCircular`'s
   `e = 1` collapse recurring at `e = f − 1` by a different mechanism — there `thm:e1reduce` supplied
   the final `a`, here `p_east = 0` does — and `WallsCircular.lean`'s header sentence "for `e ≥ 2`
   nothing here applies" is therefore incomplete: on `e = f − 1` it applies in full.  Hence
   `thm:basebeta-full`/`thm:fullprime`, conditional on `hyp:walls`, have **no content at
   `N = 83, 179, 263, …`**: their hypothesis is unsatisfiable there by the papers' own PROVED chain
   (`WallsCircular.conditional_is_vacuous`).
2. **The mismatch apex ray is never a complete wall on `e = f − 1`.**  `thm:farregion` says a
   complete wall of inner length `f·b` cuts off the tile scaled by `f`, whose base side is the
   `f·a = e·f²` stretch from a corner (`OM-align`: "the forced `b^f` wall must land on the base at
   coordinate `e·f²`").  That landing point would be a base junction at distance `f·a` from a
   corner, which `no_prefix_of_length_fa`/`no_suffix_of_length_fa` forbid.  So the framing premise
   of `thm:align`/`thm:ray` ("of inner length `f·b`") fails in every hypothetical `e = f − 1`
   tiling — the wall-based apex toolkit (`rem:live`: "every tool developed here is wall-based") is
   provably inapplicable on this family, and `T_mid` (which needs the double cut = both walls)
   with it.

Neither consequence excludes a column or a member.  They say where not to look.

## Non-vacuity (standing rule)

`witness_prefix_ec_both` exhibits both words of length `f·a`; `witness_word_23_all_but_prefix`
exhibits a base word at `(2,3)` satisfying every hypothesis of `no_prefix_of_length_fa` except the
prefix clause; `witness_word_23_all_but_last` one satisfying every hypothesis except `hlast`
(so `hlast` is load-bearing); `witness_side_23` and `witness_column_zero_side_23` show the side
bundles are satisfiable before the killing hypothesis is added.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.EpredColumnKill

open Erdos634.Interface (Edge)

/-! ## 1.  The side at `e = f − 1`: `thm:efminus1`'s arithmetic tail -/

/-- `gcd(e, e+1) = 1`. -/
theorem coprime_succ (e : ℕ) : Nat.Coprime e (e + 1) := by
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_succ]
  simp

/-- **`thm:efminus1`, arithmetic tail.**  The side level equation at `e = f − 1` is
`p·(f−1) + n_c = f`; with `n_c ≥ 2` (the apex `c` and the `c` below `J`, `cor:pbound`) this
forces `p = 0`, since `p ≥ 1` already spends `f − 1` of the `f`. -/
theorem side_p_zero_of_two_c {e f p R : ℕ} (he : e + 1 = f)
    (hlevel : p * e + R = f) (hR : 2 ≤ R) : p = 0 := by
  by_contra hp
  have h1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
  have : e ≤ p * e := Nat.le_mul_of_pos_left _ h1
  omega

/-- **The equal side reads `c^f` on `e = f − 1`, given `n_c ≥ 2`.**  Composes the real side walk
(`lem:sidenob`, `SideNoB.side_no_b_uncond`, `f ∣ P` by `side_a_quantized`) with the tail above.
The hypothesis `hR` is `thm:secondc`'s content; nothing else is assumed. -/
theorem epred_side_no_a {e f P Q R b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hR : 2 ≤ R) : P = 0 ∧ Q = 0 := by
  have hco : Nat.Coprime e f := by subst he; exact coprime_succ e
  have hef : e < f := by omega
  have hQ : Q = 0 := SideNoB.side_no_b_uncond hco hef hb hwalk (by omega)
  subst hQ
  obtain ⟨p, hp⟩ := SideNoB.side_a_quantized hco hef b hb hwalk (by omega)
  have hf0 : 0 < f := by omega
  -- level equation `p·e + R = f`
  have hlevel : p * e + R = f := by
    subst hp
    have h1 : f * (p * e + R) * f = f * f * f := by
      simp only [Nat.zero_mul, Nat.add_zero] at hwalk
      nlinarith [hwalk]
    have h2 : p * e + R = f := by
      have := Nat.eq_of_mul_eq_mul_right hf0 h1
      exact Nat.eq_of_mul_eq_mul_left hf0 (by nlinarith [this])
    exact h2
  have hp0 : p = 0 := side_p_zero_of_two_c he hlevel hR
  subst hp0
  exact ⟨by simpa using hp, rfl⟩

/-! ## 2.  The column `(0, e, 2e)` at `e = f − 1` -/

/-- **A side with an `a`-edge at `e = f − 1` reads exactly `a^f c`.**  `lem:ccornerside`'s
arithmetic (`SidePRange.side_p_range`) gives `1 ≤ p ≤ (f−1)/e = 1`, so `P = f`; the level
equation then leaves a single `c`.  `hPpos` is what the column `(0,e,2e)` supplies through the
corner flank (`TilePlacement.c_corner_side_a`) and the open chain-first-edge link. -/
theorem column_zero_side_word {e f P Q R b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) (hPpos : 0 < P) : P = f ∧ Q = 0 ∧ R = 1 := by
  have hco : Nat.Coprime e f := by subst he; exact coprime_succ e
  have hef : e < f := by omega
  obtain ⟨p, hP, hp1, hple⟩ := side_p_range hco hef b hb hwalk hgamma he1 hPpos
  have hdiv : (f - 1) / e = 1 := by
    have : f - 1 = e := by omega
    rw [this, Nat.div_self (by omega)]
  have hp : p = 1 := by omega
  subst hp
  simp only [Nat.mul_one] at hP
  have hQ : Q = 0 := SideNoB.side_no_b_uncond hco hef hb hwalk hgamma
  subst hQ
  refine ⟨hP, rfl, ?_⟩
  have hf0 : 0 < f := by omega
  rw [hP] at hwalk
  simp only [Nat.zero_mul, Nat.add_zero] at hwalk
  -- `f·e·f + R·f² = f³`  ⟹  `e + R = f`  ⟹  `R = 1`
  have h1 : (e + R) * (f * f) = f * (f * f) := by nlinarith [hwalk]
  have h2 : e + R = f := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hf0 hf0) h1
  omega

/-- **The column `(0, e, 2e)` dies on `e = f − 1` given `n_c ≥ 2`.**  `prop:n1fromwalls` with its
hypothesis `p = 0` discharged by `thm:efminus1`'s tail: the side forced to `a^f c` has one `c`,
against two.  The open geometric content is exactly `thm:secondc`'s `a`-exclusion below the apex
`c` — the configuration killed here *is* that configuration. -/
theorem column_zero_dies_of_two_c {e f P Q R b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f)
    (hwalk : P * (e * f) + Q * b + R * (f * f) = f * f * f)
    (hgamma : 1 ≤ R) (hPpos : 0 < P) (hR : 2 ≤ R) : False := by
  obtain ⟨_, _, hR1⟩ := column_zero_side_word he he1 hb hwalk hgamma hPpos
  omega

/-! ## 3.  The letter budget at `e = f − 1` -/

/-- Edge lengths for a word over `{a, b, c}`. -/
def len (a b c : ℕ) : Edge → ℕ
  | .a => a
  | .b => b
  | .c => c

/-- The length of a word is its letter counts against the three lengths. -/
theorem sum_len_eq (a b c : ℕ) : ∀ w : List Edge,
    (w.map (len a b c)).sum = w.count .a * a + w.count .b * b + w.count .c * c
  | [] => by simp
  | x :: w => by
      have ih := sum_len_eq a b c w
      cases x <;> simp [len, ih] <;> ring

/-- **The two words of length `f·a = e·c` on `e = f − 1`.**  `Inflation.a_side_no_b` (scale
`k = f`) kills the `b`-count and `a_side_words` parametrises the rest: `a^f` or `c^e`. -/
theorem prefix_ec {e f na nb nc b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f)
    (h : na * (e * f) + nb * b + nc * (f * f) = f * (e * f)) :
    (na = f ∧ nb = 0 ∧ nc = 0) ∨ (na = 0 ∧ nb = 0 ∧ nc = e) := by
  have hco : Nat.Coprime e f := by subst he; exact coprime_succ e
  have hef : e < f := by omega
  have hb' : b + e ^ 2 = f ^ 2 := by rw [pow_two, pow_two]; exact hb
  have h' : na * (e * f) + nb * b + nc * f ^ 2 = f * (e * f) := by rw [pow_two]; exact h
  have hnb : nb = 0 := Inflation.a_side_no_b e f b f na nb nc he1 hef hco hb' (le_refl f) h'
  subst hnb
  simp only [Nat.zero_mul, Nat.add_zero] at h'
  obtain ⟨q, hq1, hq2⟩ := Inflation.a_side_words e f f na nc he1 hef hco h'
  have hf0 : 0 < f := by omega
  have hq : q ≤ 1 := by
    by_contra hc
    have : 2 * f ≤ q * f := Nat.mul_le_mul_right f (by omega)
    omega
  interval_cases q
  · left; exact ⟨by omega, rfl, by simpa using hq2⟩
  · right; exact ⟨by omega, rfl, by simpa using hq2⟩

/-- **No prefix of length `f·a`.**  A base word on `e = f − 1` that begins and ends with `a`, with
at most `f` letters `a` and the base's total length, has no prefix of total length `f·a`.
The base length is written `e·(2f² + b) = e(3f² − e²)`, subtraction-free. -/
theorem no_prefix_of_length_fa {e f b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f) (w : List Edge)
    (hsum : (w.map (len (e * f) b (f * f))).sum = e * (2 * (f * f) + b))
    (hhead : w.head? = some .a) (hlast : w.getLast? = some .a)
    (hcount : w.count .a ≤ f)
    (u v : List Edge) (huv : w = u ++ v)
    (hu : (u.map (len (e * f) b (f * f))).sum = f * (e * f)) : False := by
  rw [sum_len_eq] at hu
  rcases prefix_ec he he1 hb hu with ⟨hna, -, -⟩ | ⟨hna, -, hnc⟩
  · -- `u = a^f` by count; the last letter of `w` is a further `a`
    have hv : v ≠ [] := by
      rintro rfl
      rw [List.append_nil] at huv
      subst huv
      rw [sum_len_eq] at hsum
      rw [hna] at hsum hu
      have hf0 : 0 < f := by omega
      have hpos : 0 < e * (f * f) := Nat.mul_pos (by omega) (Nat.mul_pos hf0 hf0)
      nlinarith [hsum, hu, hpos]
    rcases List.eq_nil_or_concat v with h | ⟨v', y, hv'⟩
    · exact hv h
    rw [List.concat_eq_append] at hv'
    subst hv'
    have hlast' : w.getLast? = some y := by
      rw [huv, ← List.append_assoc, List.getLast?_concat]
    rw [hlast'] at hlast
    have hy : y = Edge.a := Option.some.inj hlast
    subst hy
    have hmem : Edge.a ∈ v' ++ [Edge.a] := List.mem_append_right _ (List.mem_singleton_self _)
    have hpos : 0 < (v' ++ [Edge.a]).count Edge.a := List.count_pos_iff.mpr hmem
    have hcw : w.count Edge.a = u.count Edge.a + (v' ++ [Edge.a]).count Edge.a := by
      rw [huv, List.count_append]
    omega
  · -- `u = c^e` is nonempty and starts with `c`, but `w` starts with `a`
    have hu_ne : u ≠ [] := by
      rintro rfl
      simp at hnc
      omega
    rcases u with _ | ⟨x, u'⟩
    · exact hu_ne rfl
    have hhead' : w.head? = some x := by rw [huv]; rfl
    rw [hhead'] at hhead
    have hx : x = Edge.a := Option.some.inj hhead
    subst hx
    simp at hna

/-- **No suffix of length `f·a`**, by reversal. -/
theorem no_suffix_of_length_fa {e f b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f) (w : List Edge)
    (hsum : (w.map (len (e * f) b (f * f))).sum = e * (2 * (f * f) + b))
    (hhead : w.head? = some .a) (hlast : w.getLast? = some .a)
    (hcount : w.count .a ≤ f)
    (u v : List Edge) (huv : w = u ++ v)
    (hv : (v.map (len (e * f) b (f * f))).sum = f * (e * f)) : False := by
  refine no_prefix_of_length_fa he he1 hb w.reverse ?_ ?_ ?_ ?_ v.reverse u.reverse ?_ ?_
  · rw [List.map_reverse, List.sum_reverse]; exact hsum
  · rw [List.head?_reverse]; exact hlast
  · rw [List.getLast?_reverse]; exact hhead
  · rw [(List.reverse_perm w).count_eq]; exact hcount
  · rw [huv, List.reverse_append]
  · rw [List.map_reverse, List.sum_reverse]; exact hv

/-! ## 4.  What the budget refutes -/

/-- **The west block of `hyp:walls` never completes on `e = f − 1`.**  The block form puts `f`
`a`-feet consecutively from the west corner, i.e. the base word begins with `a^f`; with `p = 0`
on the east side the last letter is an `a` (`TilePlacement.a_corner_side_c`, read backwards), and
`x ≤ f` on every surviving column (`EpredBaseColumns.epred_base_solutions` with `z ≥ 1`).
Compare `WallsCircular.west_block_never_complete` at `e = 1`, where the final `a` came from
`thm:e1reduce`. -/
theorem west_block_never_complete_epred {e f b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f) (w : List Edge)
    (hsum : (w.map (len (e * f) b (f * f))).sum = e * (2 * (f * f) + b))
    (hhead : w.head? = some .a) (hlast : w.getLast? = some .a)
    (hcount : w.count .a ≤ f)
    (walls_west : ∃ v, w = List.replicate f .a ++ v) : False := by
  obtain ⟨v, hv⟩ := walls_west
  refine no_prefix_of_length_fa he he1 hb w hsum hhead hlast hcount _ v hv ?_
  simp [List.map_replicate, List.sum_replicate, len]

/-- **The east block of `hyp:walls` never completes on `e = f − 1`.**  Its foot is a `c` at the
east corner, so the base word ends in `c`; but `p = 0` on the east side (`thm:efminus1`) makes the
east corner tile lay `c` on the side and hence `a` on the base.  Stated on the two letters. -/
theorem east_block_never_complete_epred (w : List Edge)
    (hlast : w.getLast? = some .a) (walls_east : w.getLast? = some .c) : False := by
  rw [hlast] at walls_east
  exact Edge.noConfusion (Option.some.inj walls_east)

/-- **Both halves at once**: under `p = 0` on both sides, no base word on `e = f − 1` is the walls
word.  Hence `hyp:walls` fails in every hypothetical tiling of the family, and a conditional
exclusion citing it there is `WallsCircular.conditional_is_vacuous`. -/
theorem walls_refuted_epred {e f b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f) (w : List Edge)
    (hsum : (w.map (len (e * f) b (f * f))).sum = e * (2 * (f * f) + b))
    (hhead : w.head? = some .a) (hlast : w.getLast? = some .a)
    (hcount : w.count .a ≤ f) :
    ¬ (∃ v, w = List.replicate f .a ++ v) ∧ w.getLast? ≠ some .c :=
  ⟨fun h => west_block_never_complete_epred he he1 hb w hsum hhead hlast hcount h,
   fun h => east_block_never_complete_epred w hlast h⟩

/-- **The mismatch ray's landing point is never a base junction on `e = f − 1`.**  A complete
mismatch wall of inner length `f·b` lands on the base at distance `f·a = e·f²` from a corner
(`thm:farregion`, `OM-align`); the base word would then split there into a prefix of length `f·a`
and the rest (or, for the other chirality, a suffix).  Both are excluded, so on this family the
premise of `thm:align`/`thm:ray` fails in every tiling. -/
theorem no_junction_at_fa {e f b : ℕ} (he : e + 1 = f) (he1 : 1 ≤ e)
    (hb : b + e * e = f * f) (w : List Edge)
    (hsum : (w.map (len (e * f) b (f * f))).sum = e * (2 * (f * f) + b))
    (hhead : w.head? = some .a) (hlast : w.getLast? = some .a)
    (hcount : w.count .a ≤ f) (u v : List Edge) (huv : w = u ++ v) :
    (u.map (len (e * f) b (f * f))).sum ≠ f * (e * f) ∧
    (v.map (len (e * f) b (f * f))).sum ≠ f * (e * f) :=
  ⟨fun h => no_prefix_of_length_fa he he1 hb w hsum hhead hlast hcount u v huv h,
   fun h => no_suffix_of_length_fa he he1 hb w hsum hhead hlast hcount u v huv h⟩

/-! ## 5.  The surviving columns at `N = 23, 59, 83`

Filters: `z ≥ 1` (`prop:gammatrap`), `x + z ≥ 4` (`prop:cornerpara`), `x ≥ 2` (both corners lay
`a`, from `p = 0` on both sides), and the wedge clearance `y·(2f−1)² ≤ 2f⁴ + 2f³ − 3f + 1`
(`EpredWedgeClearance.epred_b_count_bound`, available for `f ≥ 4`).  `x ≥ 2` is the only
filter here that rests on `thm:efminus1`; it is what removes `(0, e, 2e)`. -/

/-- **`N = 23`, `(e,f) = (2,3)`: one column survives, the walls column `(3,2,2)`.**
(`NO_TILING` by exhaustive search, `tab:basebeta`; so this one column is a genuine gap, not a
counterexample.) -/
theorem survivors_23 {x y z : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 1 ≤ z)
    (hxz : 4 ≤ x + z) (hx2 : 2 ≤ x)
    (h : EpredBaseColumns.BaseEq 3 x y z) : x = 3 ∧ y = 2 ∧ z = 2 := by
  rcases EpredBaseColumns.epred_base_solutions (by norm_num : (3:ℤ) ≤ 3) hx hy (by omega) h with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨k, hk0, hk, h1, h2, h3⟩
  · omega
  · omega
  · have hkc : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkc with rfl | rfl | rfl <;> omega

/-- **`N = 59`, `(e,f) = (4,5)`: three columns survive**, `(5,4,4)`, `(4,9,3)`, `(3,14,2)`.
(`NO_TILING` by search; three genuine gaps.) -/
theorem survivors_59 {x y z : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 1 ≤ z)
    (hxz : 4 ≤ x + z) (hx2 : 2 ≤ x)
    (hwedge : y * (2 * 5 - 1) ^ 2 ≤ 2 * 5 ^ 4 + 2 * 5 ^ 3 - 3 * 5 + 1)
    (h : EpredBaseColumns.BaseEq 5 x y z) :
    (x = 5 ∧ y = 4 ∧ z = 4) ∨ (x = 4 ∧ y = 9 ∧ z = 3) ∨ (x = 3 ∧ y = 14 ∧ z = 2) := by
  rcases EpredBaseColumns.epred_base_solutions (by norm_num : (3:ℤ) ≤ 5) hx hy (by omega) h with
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨k, hk0, hk, h1, h2, h3⟩
  · omega
  · omega
  · have hkc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hkc with rfl | rfl | rfl | rfl | rfl
    · left; omega
    · right; left; omega
    · right; right; omega
    · exfalso; omega
    · exfalso; omega

/-- **`N = 83`, `(e,f) = (5,6)`: four columns survive**, `(6,5,5)`, `(5,11,4)`, `(4,17,3)`,
`(3,23,2)` — the four base words of `report_e2.md` §1, now derived rather than quoted.  This is
the open row; nothing below excludes any of the four. -/
theorem survivors_83 {x y z : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 1 ≤ z)
    (hxz : 4 ≤ x + z) (hx2 : 2 ≤ x)
    (hwedge : y * (2 * 6 - 1) ^ 2 ≤ 2 * 6 ^ 4 + 2 * 6 ^ 3 - 3 * 6 + 1)
    (h : EpredBaseColumns.BaseEq 6 x y z) :
    (x = 6 ∧ y = 5 ∧ z = 5) ∨ (x = 5 ∧ y = 11 ∧ z = 4) ∨
    (x = 4 ∧ y = 17 ∧ z = 3) ∨ (x = 3 ∧ y = 23 ∧ z = 2) := by
  rcases EpredBaseColumns.witness_83_complete hx hy (by omega) h with
    h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · omega
  · omega
  · left; exact h1
  · right; left; exact h1
  · right; right; left; exact h1
  · right; right; right; exact h1
  · omega
  · omega

/-! ## 6.  Non-vacuity witnesses -/

/-- Both words of length `f·a` really occur: `a^f` and `c^e`, at `(2,3)`: `3·6 = 18 = 2·9`. -/
theorem witness_prefix_ec_both :
    (3 * (2 * 3) + 0 * 5 + 0 * (3 * 3) = 3 * (2 * 3)) ∧
    (0 * (2 * 3) + 0 * 5 + 2 * (3 * 3) = 3 * (2 * 3)) := by decide

/-- A base word at `(2,3)` satisfying **every** hypothesis of `no_prefix_of_length_fa` except the
prefix clause: `a c a b b c a`, length `6+9+6+5+5+9+6 = 46 = 2·(2·9 + 5)`, first and last `a`,
three `a`'s.  So the hypotheses are jointly satisfiable and only the prefix is refuted. -/
theorem witness_word_23_all_but_prefix :
    let w : List Edge := [.a, .c, .a, .b, .b, .c, .a]
    (w.map (len (2 * 3) 5 (3 * 3))).sum = 2 * (2 * (3 * 3) + 5) ∧
    w.head? = some .a ∧ w.getLast? = some .a ∧ w.count .a ≤ 3 := by
  decide

/-- A word satisfying every hypothesis **except** `hlast`, with the prefix `a^3` of length
`18 = f·a`: `a a a b b c c`.  So `hlast` (the east corner's `a`, i.e. `p_east = 0`) is
load-bearing — without it the west block is consistent with the letter count. -/
theorem witness_word_23_all_but_last :
    let w : List Edge := [.a, .a, .a, .b, .b, .c, .c]
    (w.map (len (2 * 3) 5 (3 * 3))).sum = 2 * (2 * (3 * 3) + 5) ∧
    w.head? = some .a ∧ w.count .a ≤ 3 ∧
    w = List.replicate 3 .a ++ [.b, .b, .c, .c] ∧
    ((List.replicate 3 (Edge.a)).map (len (2 * 3) 5 (3 * 3))).sum = 3 * (2 * 3) := by
  decide

/-- The side bundle of `epred_side_no_a` is satisfiable at `(2,3)`: `c^3`, i.e. `(P,Q,R) = (0,0,3)`
with `0·6 + 0·5 + 3·9 = 27`, `R ≥ 2`. -/
theorem witness_side_23 :
    0 * (2 * 3) + 0 * 5 + 3 * (3 * 3) = 3 * 3 * 3 ∧ 2 ≤ 3 := by decide

/-- The bundle of `column_zero_side_word` (walk, `γ`-trap, `P > 0`) is satisfiable at `(2,3)` by
the word `a^3 c`, `(P,Q,R) = (3,0,1)`: `3·6 + 0 + 1·9 = 27`.  Only `hR : 2 ≤ R` kills it, and that
is `thm:secondc`. -/
theorem witness_column_zero_side_23 :
    3 * (2 * 3) + 0 * 5 + 1 * (3 * 3) = 3 * 3 * 3 ∧ 0 < 3 ∧ 1 ≤ 1 ∧ ¬ (2 ≤ 1) := by decide

end Erdos634.EpredColumnKill

#print axioms Erdos634.EpredColumnKill.epred_side_no_a
#print axioms Erdos634.EpredColumnKill.column_zero_dies_of_two_c
#print axioms Erdos634.EpredColumnKill.no_prefix_of_length_fa
#print axioms Erdos634.EpredColumnKill.no_suffix_of_length_fa
#print axioms Erdos634.EpredColumnKill.walls_refuted_epred
#print axioms Erdos634.EpredColumnKill.no_junction_at_fa
#print axioms Erdos634.EpredColumnKill.survivors_23
#print axioms Erdos634.EpredColumnKill.survivors_59
#print axioms Erdos634.EpredColumnKill.survivors_83
