import Erdos634.N1GapSubcases

/-!
# The crossing branch at a **sub-golden** member: exactly two configurations, and no prefix

Erdős #634, companion to `N1GapSubcases` / `N1GapMastGap` / `N1GapCRange`.

Those three files subatomise the surviving crossing branch of `rem:n1gapexact` along the **index
`x`**, at a *separated* member (`Member`, whose field `sep` is `2ef + e² < f²`).  The verdict there
is `2⌊b/a⌋ + 2 ≥ 6` configurations and **no monovariant in `x`**.

This file subatomises along the **`(e,f)` axis instead**, and the answer is different in kind.

**The regime.**  A member is *sub-golden* when `f² < ef + e²`, i.e. `f/e < φ`; equivalently
`b < a`, the tile's `b = f² − e²` being its **shortest** side rather than its middle one.  This is
the regime `prop:nogolden` was built for, and it contains the whole family `e = f − 1` for `f ≥ 3`
(`epred_subGolden`).  Sub-golden is **incompatible with separation** (`not_separated`,
`not_member`): `f² < ef + e² < 2ef + e²`.  So the entire `2⌊b/a⌋ + 2` stack is not merely large or
small at these members — its hypothesis is unsatisfiable there, and the enumeration must be redone.

**What the enumeration becomes.**

* `floor_b_div_a` — `⌊b/a⌋ = 0`, so "`2X + 2`" would read `2`.  It does, but not for that reason:
* `prefix_empty` — **there is no prefix at all.**  Every far-side partial sum strictly below `b` is
  `0`, because `b` is now the *shortest* tile side and no edge fits underneath it.  Where
  `N1GapSubcases.prefix_all_a` allowed a run `a^x` before the crossing edge, here the crossing edge
  is the *first* edge of the far-side run, anchored at `∂ABC`.  The index `x` does not exist.
* `adm_iff_subGolden` — the admissible `(x, L)` are exactly `(0, a)` and `(0, c)`.
* `card_adm_subGolden` — hence exactly **two** sub-configurations, against `≥ 6` at every separated
  member (`N1GapMastGap.card_adm_ge_six`).
* `overhang_c` (`= e²`, unchanged) and `overhang_a` (`= ef + e² − f² > 0`).  Both branches are
  **overruns**: the `ℓ = a` fall-short branch of `N1Gap.step_reduces_to_crossing` disappears
  entirely, so `Frontier.gap_b_sub_a` / `N1Gap.a_short_is_gap` — the lemma that closes the shortfall
  — has nothing to do at a sub-golden member (`no_shortfall_branch`).

**The prime case.**  `epred_N`: at `e = f − 1` the tile count is `N = 2f² + 2f − 1`, matching
`rem:efminus1`/`O-efminus1`.  `epred_three_dvd` and `epred_mod_twelve` give the clean dichotomy —
`f ≡ 1 (mod 3)` forces `3 ∣ N`, and otherwise `N ≡ 11 (mod 12)` **automatically**.  So
`epred_prime_mod_twelve`: at `e = f − 1`, *every* prime `N > 3` in the family is already `≡ 11`
mod `12`, i.e. is a base-`β` candidate; there is no mod-12 sieve to apply here.  The family is a
quadratic in `f`, so its prime count is a Bunyakovsky question and is **not** finite —
`O-efminus1` records the same and likewise claims nothing about infinitude.

**Honest scope.**  This file proves the *arithmetic* enumeration at a sub-golden member.  It does
**not** claim that `thm:n1`'s reduction (`N1Gap.step_reduces_to_crossing`, stated on `Member`) is
available there; `rem:band2e` records that separation is inert in that proof but that the base
dichotomy itself is only established for `f > 2e`, which sub-golden members violate.  No sub-case
is killed and no Rule 0 label moves.

Zero `sorry`; standard three axioms.  Witnesses `(2,3)` (`N = 23`) and `(5,6)` (`N = 83`, the one
open base-β row below `110`) are exhibited at the foot.
-/

namespace Erdos634.N1GapSubGolden

variable {e f a b c : ℕ}

/-- A **sub-golden member**: the standard base-β tile data, with `f² < ef + e²` (`f/e` below the
golden ratio) in place of `Member`'s separation `2ef + e² < f²`.  Equivalently `b < a`. -/
structure SubGolden (e f a b c : ℕ) : Prop where
  he : 1 ≤ e
  hef : e < f
  hco : Nat.Coprime e f
  ha : a = e * f
  hb : b + e * e = f * f
  hc : c = f * f
  gold : f * f < e * f + e * e

/-! ## The side order inverts -/

theorem SubGolden.b_lt_a (S : SubGolden e f a b c) : b < a := by
  obtain ⟨_, _, _, ha, hb, _, gold⟩ := S; subst ha; nlinarith [hb, gold]

theorem SubGolden.a_lt_c (S : SubGolden e f a b c) : a < c := by
  obtain ⟨he, hef, _, ha, _, hc, _⟩ := S; subst ha; subst hc; nlinarith

theorem SubGolden.b_lt_c (S : SubGolden e f a b c) : b < c :=
  lt_trans S.b_lt_a S.a_lt_c

theorem SubGolden.b_pos (S : SubGolden e f a b c) : 0 < b := by
  obtain ⟨he, hef, _, _, hb, _, _⟩ := S; nlinarith

theorem SubGolden.a_pos (S : SubGolden e f a b c) : 0 < a := by
  have := S.b_lt_a; have := S.b_pos; omega

/-- **Sub-golden members are never separated.**  `f² < ef + e² < 2ef + e²`, so `Member`'s field
`sep` fails: the `2⌊b/a⌋ + 2` enumeration of `N1GapSubcases` has an unsatisfiable hypothesis on
this whole regime, and the `(e,f)` axis is not a way of shrinking that list — it replaces it. -/
theorem not_separated (S : SubGolden e f a b c) : ¬ (2 * e * f + e * e < f * f) := by
  obtain ⟨he, hef, _, _, _, _, gold⟩ := S
  have h1 : 0 < e * f := Nat.mul_pos (by omega) (by omega)
  have h2 : 2 * e * f = e * f + e * f := by ring
  omega

theorem not_member (S : SubGolden e f a b c) : ¬ Erdos634.N1Gap.Member e f a b c :=
  fun M => not_separated S M.sep

/-! ## `⌊b/a⌋ = 0`, and the prefix is empty -/

/-- The index range of `N1GapSubcases.adm_iff` collapses: `X = ⌊b/a⌋ = 0`. -/
theorem floor_b_div_a (S : SubGolden e f a b c) : b / a = 0 :=
  Nat.div_eq_of_lt S.b_lt_a

/-- **No prefix.**  `b` is the shortest tile side, so a far-side partial sum strictly below `b`
uses no edge at all.  This is the sub-golden replacement for `N1GapSubcases.prefix_all_a`, and it
is strictly stronger: there the prefix was `a^x` with `x` free up to `⌊b/a⌋`; here the crossing
edge is the first edge of the run. -/
theorem prefix_empty (S : SubGolden e f a b c) {x y z s : ℕ}
    (hs : x * a + y * b + z * c = s) (hlt : s < b) : x = 0 ∧ y = 0 ∧ z = 0 ∧ s = 0 := by
  have hba := S.b_lt_a
  have hbc := S.b_lt_c
  have hbp := S.b_pos
  have hx : x = 0 := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exact h
    · exfalso; have := Nat.le_mul_of_pos_left a h; omega
  have hy : y = 0 := by
    rcases Nat.eq_zero_or_pos y with h | h
    · exact h
    · exfalso; have := Nat.le_mul_of_pos_left b h; omega
  have hz : z = 0 := by
    rcases Nat.eq_zero_or_pos z with h | h
    · exact h
    · exfalso; have := Nat.le_mul_of_pos_left c h; omega
  subst hx; subst hy; subst hz; exact ⟨rfl, rfl, rfl, by omega⟩

/-! ## The enumeration: exactly two configurations -/

/-- **The sub-golden enumeration.**  A crossing at `V_k` — near end at `x·a` strictly before `V_k`,
far end strictly past it — happens exactly for `(x, L) = (0, a)` and `(x, L) = (0, c)`.

Contrast `N1GapSubcases.adm_iff`, where `L = c` ran over `0 ≤ x ≤ X`, `L = b` over `1 ≤ x ≤ X`,
and `L = a` was the single top index. -/
theorem adm_iff_subGolden (S : SubGolden e f a b c) {x L : ℕ} (hL : L = a ∨ L = b ∨ L = c) :
    (x * a < b ∧ b < x * a + L) ↔ (x = 0 ∧ (L = a ∨ L = c)) := by
  have hba := S.b_lt_a
  have hbc := S.b_lt_c
  have hstart : x * a < b ↔ x = 0 := by
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos x with h' | h'
      · exact h'
      · exfalso; have := Nat.le_mul_of_pos_left a h'; omega
    · rintro rfl; simpa using S.b_pos
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x = 0 := hstart.mp h1
    subst hx
    refine ⟨rfl, ?_⟩
    rcases hL with rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso; simp at h2
    · exact Or.inr rfl
  · rintro ⟨rfl, hLm⟩
    refine ⟨hstart.mpr rfl, ?_⟩
    rcases hLm with rfl | rfl <;> simpa using (by omega : b < L)

/-- **Exactly two sub-configurations** — against `≥ 6` at every separated member
(`N1GapMastGap.card_adm_ge_six`).  Same `Finset` shape as `N1GapSubcases.card_adm`. -/
theorem card_adm_subGolden (S : SubGolden e f a b c) :
    ((Finset.range (b / a + 1) ×ˢ ({a, b, c} : Finset ℕ)).filter
      (fun p => p.1 * a < b ∧ b < p.1 * a + p.2)).card = 2 := by
  classical
  have hba := S.b_lt_a
  have hbc := S.b_lt_c
  have hac := S.a_lt_c
  have hX : b / a = 0 := floor_b_div_a S
  have hset :
      (Finset.range (b / a + 1) ×ˢ ({a, b, c} : Finset ℕ)).filter
        (fun p => p.1 * a < b ∧ b < p.1 * a + p.2)
      = ({((0 : ℕ), a), ((0 : ℕ), c)} : Finset (ℕ × ℕ)) := by
    ext ⟨x, L⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton, Prod.ext_iff, hX]
    constructor
    · rintro ⟨⟨hxr, hLmem⟩, hcond⟩
      have hL : L = a ∨ L = b ∨ L = c := by tauto
      obtain ⟨rfl, hLm⟩ := (adm_iff_subGolden S hL).mp hcond
      rcases hLm with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨by omega, by tauto⟩,
          (adm_iff_subGolden S (Or.inl rfl)).mpr ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨⟨by omega, by tauto⟩,
          (adm_iff_subGolden S (Or.inr (Or.inr rfl))).mpr ⟨rfl, Or.inr rfl⟩⟩
  rw [hset]
  rw [Finset.card_pair]
  simp only [ne_eq, Prod.mk.injEq, not_and]
  intro _
  omega

/-! ## The two overhangs, and the vanishing of the shortfall branch -/

/-- `L = c`: overhang `c − b = e²`, exactly as at a separated member. -/
theorem overhang_c (S : SubGolden e f a b c) : c - b = e * e := by
  obtain ⟨_, _, _, _, hb, hc, _⟩ := S; omega

/-- `L = a`: overhang `a − b = ef + e² − f² > 0`.  At a separated member the `a`-edge instead falls
`b − a` **short** of `V_k`; here it overruns. -/
theorem overhang_a (S : SubGolden e f a b c) :
    a - b = e * f + e * e - f * f ∧ 0 < a - b := by
  have hba := S.b_lt_a
  obtain ⟨_, _, _, ha, hb, _, gold⟩ := S
  exact ⟨by omega, by omega⟩

/-- **The shortfall branch does not exist at a sub-golden member.**  `N1Gap.step_reduces_to_crossing`
splits the leading far-side edge `ℓ` into: `ℓ = b` (junction), `ℓ = a` (falls `b − a` short) and
`ℓ = c` (overruns by `e²`).  At a sub-golden member the middle branch inverts: `a > b`, so *both*
non-junction branches are overruns, and `N1Gap.a_short_is_gap` / `Frontier.gap_b_sub_a` — the lemma
whose whole job is to close the shortfall — is inapplicable, having no shortfall to close. -/
theorem no_shortfall_branch (S : SubGolden e f a b c) (ℓ : ℕ) (hmem : ℓ = a ∨ ℓ = b ∨ ℓ = c) :
    (ℓ = b) ∨ (b < ℓ ∧ ℓ = a ∧ ℓ - b = e * f + e * e - f * f)
      ∨ (b < ℓ ∧ ℓ = c ∧ ℓ - b = e * e) := by
  rcases hmem with rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨S.b_lt_a, rfl, (overhang_a S).1⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨S.b_lt_c, rfl, overhang_c S⟩)

/-! ## The family `e = f − 1`, and its tile counts -/

/-- Every `e = f − 1` member with `f ≥ 3` is sub-golden.  (`f = 2` is the exception `(1,2)`, where
`a = 2 < 3 = b`.)  Tile: `(a,b,c) = (f² − f, 2f − 1, f²)`. -/
theorem epred_subGolden (f : ℕ) (hf : 3 ≤ f) :
    SubGolden (f - 1) f (f * f - f) (2 * f - 1) (f * f) where
  he := by omega
  hef := by omega
  hco := by
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 3 := ⟨f - 3, by omega⟩
    have : k + 3 - 1 = k + 2 := by omega
    rw [this]
    show Nat.gcd (k + 2) (k + 3) = 1
    have h2 : k + 3 = (k + 2) + 1 := by ring
    rw [h2, Nat.gcd_rec, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), Nat.gcd_one_left]
  ha := by
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 3 := ⟨f - 3, by omega⟩
    have h1 : k + 3 - 1 = k + 2 := by omega
    have h2 : (k + 3) * (k + 3) - (k + 3) = (k + 2) * (k + 3) := by
      have : (k + 2) * (k + 3) + (k + 3) = (k + 3) * (k + 3) := by ring
      omega
    rw [h1, h2]
  hb := by
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 3 := ⟨f - 3, by omega⟩
    have h1 : k + 3 - 1 = k + 2 := by omega
    have h2 : 2 * (k + 3) - 1 = 2 * k + 5 := by omega
    rw [h1, h2]; ring
  hc := rfl
  gold := by
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 3 := ⟨f - 3, by omega⟩
    have h1 : k + 3 - 1 = k + 2 := by omega
    rw [h1]; nlinarith

/-- The tile count on the family: `N = 3f² − e² = 2f² + 2f − 1` (`O-efminus1`; reproduction). -/
theorem epred_N (f : ℕ) (hf : 1 ≤ f) : 3 * f * f - (f - 1) * (f - 1) = 2 * f * f + 2 * f - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have e1 : 3 * (k + 1) * (k + 1) = 3 * (k * k) + 6 * k + 3 := by ring
  have e2 : 2 * (k + 1) * (k + 1) + 2 * (k + 1) = 2 * (k * k) + 6 * k + 4 := by ring
  have e3 : k * k = 1 * (k * k) := by ring
  omega

/-! ### The mod-12 dichotomy on `N = 2f² + 2f − 1` -/

private theorem two_sq_mod (g r : ℕ) : (2 * (6 * g + r) * (6 * g + r) + 2 * (6 * g + r)) % 12
    = (2 * r * r + 2 * r) % 12 := by
  have h : 2 * (6 * g + r) * (6 * g + r) + 2 * (6 * g + r)
      = 12 * (6 * g * g + 2 * g * r + g) + (2 * r * r + 2 * r) := by ring
  rw [h, Nat.mul_add_mod]

/-- `f ≡ 1 (mod 3)` forces `3 ∣ N`, so no such `f` gives a prime beyond `N = 3`. -/
theorem epred_three_dvd (f : ℕ) (hf : 1 ≤ f) (h : f % 3 = 1) : 3 ∣ (2 * f * f + 2 * f - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, f = 3 * k + 1 := ⟨f / 3, by omega⟩
  subst hk
  refine ⟨6 * k * k + 6 * k + 1, ?_⟩
  have : 2 * (3 * k + 1) * (3 * k + 1) + 2 * (3 * k + 1) = 3 * (6 * k * k + 6 * k + 1) + 1 := by
    ring
  omega

/-- **The mod-12 dichotomy.**  For `f ≥ 2`, `N = 2f² + 2f − 1` is `≡ 3 (mod 12)` when
`f ≡ 1 (mod 3)` and `≡ 11 (mod 12)` otherwise. -/
theorem epred_mod_twelve (f : ℕ) (hf : 2 ≤ f) :
    (f % 3 = 1 → (2 * f * f + 2 * f - 1) % 12 = 3) ∧
    (f % 3 ≠ 1 → (2 * f * f + 2 * f - 1) % 12 = 11) := by
  obtain ⟨g, r, hr, rfl⟩ : ∃ g r, r < 6 ∧ f = 6 * g + r :=
    ⟨f / 6, f % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  have hmod := two_sq_mod g r
  have hbig : 8 ≤ 2 * (6 * g + r) * (6 * g + r) + 2 * (6 * g + r) := by nlinarith
  have hr3 : (6 * g + r) % 3 = r % 3 := by omega
  interval_cases r <;> simp_all <;> omega

/-- **At `e = f − 1` there is no mod-12 sieve left to apply.**  Every prime `N = 2f² + 2f − 1 > 3`
in the family is automatically `≡ 11 (mod 12)`, hence a base-β candidate: the alternative residue
`3` carries the factor `3`.  So the family's intersection with the prime case is *not* thinned by
the congruence condition of `thm:mod12`; it is the full set of `f ≢ 1 (mod 3)` for which the
quadratic is prime, a Bunyakovsky question (nothing about infinitude is claimed). -/
theorem epred_prime_mod_twelve (f : ℕ) (hf : 2 ≤ f) (hp : Nat.Prime (2 * f * f + 2 * f - 1))
    (hgt : 3 < 2 * f * f + 2 * f - 1) : (2 * f * f + 2 * f - 1) % 12 = 11 := by
  refine (epred_mod_twelve f hf).2 (fun h => ?_)
  have hdvd := epred_three_dvd f (by omega) h
  have := (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd)
  omega

/-! ## Non-vacuity -/

/-- Witness 1: `(e,f) = (2,3)`, tile `(6,5,9)`, `N = 23` — prime, `23 ≡ 11 (mod 12)`, settled
NO_TILING at `19 677` nodes (`tab:basebeta`). -/
theorem witness_23 : SubGolden 2 3 6 5 9 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Witness 2: `(e,f) = (5,6)`, tile `(30,11,36)`, `N = 83` — prime, `83 ≡ 11 (mod 12)`, and the
**one genuinely open base-β row below `N = 110`**.  It is sub-golden (`36 < 30 + 25`), so its
crossing branch carries two configurations, not `2⌊11/30⌋ + 2` read off the separated formula. -/
theorem witness_83 : SubGolden 5 6 30 11 36 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem witness_83_two_configs :
    ((Finset.range (11 / 30 + 1) ×ˢ ({30, 11, 36} : Finset ℕ)).filter
      (fun p => p.1 * 30 < 11 ∧ 11 < p.1 * 30 + p.2)).card = 2 := by
  have := card_adm_subGolden witness_83
  norm_num at this ⊢
  exact this

/-- Both witnesses really are outside `N1GapSubcases`' hypothesis. -/
theorem witness_83_not_member : ¬ Erdos634.N1Gap.Member 5 6 30 11 36 := not_member witness_83

/-- The two overhangs at `N = 83`: `a − b = 19` and `c − b = 25 = e²`. -/
theorem witness_83_overhangs : (30 : ℕ) - 11 = 19 ∧ (36 : ℕ) - 11 = 25 := by norm_num

end Erdos634.N1GapSubGolden
