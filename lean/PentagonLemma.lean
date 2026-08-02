import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# The Pentagon Lemma, arithmetic core (Erdős #634, base-β branch)

This file states and proves the pentagon lemma's arithmetic content as a single theorem, general in
`(e,f)` and with no member-by-member appeal.

## What the geometry hands us

In the base walk `(0,e,2e)` both dual blocks complete and the middle region is a pentagon whose west
base corner has interior angle `π − α`. Every decomposition of that corner places, against the dual
hypotenuse, a flank from `{a,c}`; the hypotenuse is partitioned into whole `b`-edges, so no flank
terminates at a junction and each placement leaves a STUB against the next `b`-edge. The two stubs
the analysis produces are

    `s₁ = c − b = e²`   (reduced mod `b`, since the hypotenuse is a run of `b`-edges), and
    `s₂ = |a − b|`.

A stub is a boundary segment of the region, so it must itself be partitioned into whole tile edges.
The lemma is that neither can be — hence the region dies.

## What is proved here

`pentagon_lemma` : for every member, BOTH stubs are nonzero and are gaps of the numerical semigroup
`⟨a,b,c⟩`. The two halves fail for genuinely different reasons, and it is worth keeping them apart:

  · `s₁ = e² mod b` lands in `(0, min(a,b))`, and that whole interval is a gap;
  · `s₂ = |a−b|` need NOT land there — at `(e,f) = (1,3)` the tile is `(3,8,9)`, `min(a,b) = 3` and
    `s₂ = 5` — yet it is a gap all the same, because `s₂ < c` rules out `c`, `s₂ < max(a,b)` rules
    out the larger of `a,b`, and what remains would force `min(a,b) ∣ max(a,b)` against `gcd(a,b)=1`.

An earlier treatment sent `s₂` walking by `e²` modulo `b` until it entered `(0, min(a,b))`, and the
step count of that walk was the one part of the branch argument left as prose. It is not needed: the
walk never executes a step, since both stubs are already gaps (checked exhaustively for every member
with `f ≤ 200` in `rust/stubgap`). The mechanism is deleted rather than justified.

Also proved here, rather than deferred: `gcd(ef, f² − e²) = 1`, and the positivity `b ∤ e²` of the
first stub. `Pentagon.lean` (core toolchain, no imports) had to record both in prose "for want of
library lemmas"; with Mathlib available they are short.

Axioms: the standard three (`propext`, `Classical.choice`, `Quot.sound`). No `sorry`.
-/

namespace Erdos634.PentagonLemma

variable {e f a b c t : ℕ}

/-- A boundary segment of length `t` can be split into whole tile edges. -/
def Partitionable (a b c t : ℕ) : Prop := ∃ x y z : ℕ, x * a + y * b + z * c = t

/-! ## Coprimality of the two short edges -/

/-- `e` is coprime to `b = f² − e²`: a common divisor divides `b + e² = f²`. -/
theorem coprime_e_b (hco : Nat.Coprime e f) (hb : b + e * e = f * f) : Nat.Coprime e b := by
  have hef2 : Nat.Coprime e (f * f) := hco.mul_right hco
  have hdvd : Nat.gcd e b ∣ f * f := by
    have h1 : Nat.gcd e b ∣ e * e := Dvd.dvd.mul_right (Nat.gcd_dvd_left e b) e
    have h2 : Nat.gcd e b ∣ b := Nat.gcd_dvd_right e b
    rw [← hb]; exact Nat.dvd_add h2 h1
  exact Nat.eq_one_of_dvd_coprimes hef2 (Nat.gcd_dvd_left e b) hdvd

/-- `f` is coprime to `b = f² − e²`: a common divisor divides `f² − b = e²`. -/
theorem coprime_f_b (hco : Nat.Coprime e f) (hb : b + e * e = f * f) : Nat.Coprime f b := by
  have hfe2 : Nat.Coprime f (e * e) :=
    (Nat.coprime_comm.mp hco).mul_right (Nat.coprime_comm.mp hco)
  have hdvd : Nat.gcd f b ∣ e * e := by
    have h1 : Nat.gcd f b ∣ f * f := Dvd.dvd.mul_right (Nat.gcd_dvd_left f b) f
    have h2 : Nat.gcd f b ∣ b := Nat.gcd_dvd_right f b
    have h3 : Nat.gcd f b ∣ b + e * e := by rw [hb]; exact h1
    exact (Nat.dvd_add_right h2).mp h3
  exact Nat.eq_one_of_dvd_coprimes hfe2 (Nat.gcd_dvd_left f b) hdvd

/-- **The two short edges are coprime**: `gcd(ef, f² − e²) = 1`. -/
theorem coprime_a_b (hco : Nat.Coprime e f) (ha : a = e * f) (hb : b + e * e = f * f) :
    Nat.Coprime a b := by
  subst ha; exact Nat.Coprime.mul_left (coprime_e_b hco hb) (coprime_f_b hco hb)

/-! ## Size facts -/

theorem two_le_a (he : 1 ≤ e) (hef : e < f) (ha : a = e * f) : 2 ≤ a := by subst ha; nlinarith

theorem three_le_b (he : 1 ≤ e) (hef : e < f) (hb : b + e * e = f * f) : 3 ≤ b := by nlinarith

theorem b_lt_c (he : 1 ≤ e) (hb : b + e * e = f * f) (hc : c = f * f) : b < c := by
  subst hc; nlinarith

/-! ## Anything below both `a` and `b` is a gap -/

/-- The interval `(0, min(a,b))` is a gap of `⟨a,b,c⟩`: a nonzero combination is at least
`min(a,b,c)`, and `c` exceeds `b`. -/
theorem gap_of_lt_both (hb : b ≤ c) (hs : 0 < t) (hta : t < a) (htb : t < b) :
    ¬ Partitionable a b c t := by
  rintro ⟨x, y, z, hrep⟩
  rcases Nat.eq_zero_or_pos x with hx | hx
  · rcases Nat.eq_zero_or_pos y with hy | hy
    · rcases Nat.eq_zero_or_pos z with hz | hz
      · subst hx; subst hy; subst hz; omega
      · have : c ≤ z * c := Nat.le_mul_of_pos_left _ hz
        subst hx; subst hy; omega
    · have : b ≤ y * b := Nat.le_mul_of_pos_left _ hy
      subst hx; omega
  · have : a ≤ x * a := Nat.le_mul_of_pos_left _ hx
    omega

/-! ## The first stub: `e² mod b` -/

/-- The first stub is nonzero: `b ∤ e²`, because `b` is coprime to `e` and exceeds `1`. -/
theorem first_stub_pos (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hb : b + e * e = f * f) : 0 < e * e % b := by
  have hb3 : 3 ≤ b := three_le_b he hef hb
  rcases Nat.eq_zero_or_pos (e * e % b) with h | h
  · exfalso
    have hdvd : b ∣ e * e := Nat.dvd_of_mod_eq_zero h
    have hcop : Nat.Coprime (e * e) b := Nat.Coprime.mul_left (coprime_e_b hco hb) (coprime_e_b hco hb)
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) hdvd
    omega
  · exact h

/-- The first stub is smaller than both `a` and `b`. -/
theorem first_stub_lt (he : 1 ≤ e) (hef : e < f) (ha : a = e * f) (hb : b + e * e = f * f) :
    e * e % b < a ∧ e * e % b < b := by
  have hb3 : 3 ≤ b := three_le_b he hef hb
  refine ⟨?_, Nat.mod_lt _ (by omega)⟩
  have hlt : e * e < a := by subst ha; nlinarith
  rcases Nat.lt_or_ge (e * e) b with h | h
  · rw [Nat.mod_eq_of_lt h]; exact hlt
  · have : e * e % b ≤ e * e := Nat.mod_le _ _
    omega

/-! ## The main theorem -/

/-- **Pentagon Lemma (arithmetic core).**
For every member of the base-β family — `gcd(e,f) = 1`, `1 ≤ e < f`, tile
`(a,b,c) = (ef, f²−e², f²)` — both stubs produced at the pentagon's west wedge are nonzero and
admit no partition into whole tile edges. Hence no corner decomposition survives and the pentagon
region admits no tiling.

The second stub is quantified over all `t` with `t = |a − b|`, stated additively so that no
truncated natural subtraction occurs. -/
theorem pentagon_lemma (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (ha : a = e * f) (hb : b + e * e = f * f) (hc : c = f * f) :
    (0 < e * e % b ∧ ¬ Partitionable a b c (e * e % b)) ∧
    (∀ t, (a + t = b ∨ b + t = a) → 0 < t ∧ ¬ Partitionable a b c t) := by
  have hab : Nat.Coprime a b := coprime_a_b hco ha hb
  have ha2 : 2 ≤ a := two_le_a he hef ha
  have hb3 : 3 ≤ b := three_le_b he hef hb
  have hbc : b < c := b_lt_c he hb hc
  constructor
  · -- first stub: lands in (0, min(a,b)), which is a gap
    have hpos := first_stub_pos hco he hef hb
    obtain ⟨hlta, hltb⟩ := first_stub_lt he hef ha hb
    exact ⟨hpos, gap_of_lt_both (le_of_lt hbc) hpos hlta hltb⟩
  · -- second stub: |a − b|, which may exceed min(a,b) and is a gap for a different reason
    intro t ht
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · exfalso; subst h
        have hEq : a = b := by omega
        have : a ∣ b := ⟨1, by omega⟩
        have := Nat.Coprime.eq_one_of_dvd hab this
        omega
      · exact h
    refine ⟨htpos, ?_⟩
    rintro ⟨x, y, z, hrep⟩
    -- t < c, so c cannot appear
    have htc : t < c := by
      subst hc; subst ha
      rcases ht with h | h <;> nlinarith
    have hz : z = 0 := by
      by_contra hz0
      have h1 : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr hz0
      have : c ≤ z * c := Nat.le_mul_of_pos_left _ h1
      omega
    subst hz
    simp only [Nat.zero_mul, Nat.add_zero] at hrep
    rcases ht with h | h
    · -- a < b : the larger generator b cannot appear, so a ∣ b
      have hy : y = 0 := by
        by_contra hy0
        have h1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
        have : b ≤ y * b := Nat.le_mul_of_pos_left _ h1
        omega
      subst hy
      simp only [Nat.zero_mul, Nat.add_zero] at hrep
      have hmul : a * (x + 1) = x * a + a := by ring
      have hdvd : a ∣ b := ⟨x + 1, by omega⟩
      have := Nat.Coprime.eq_one_of_dvd hab hdvd
      omega
    · -- b < a : the larger generator a cannot appear, so b ∣ a
      have hx : x = 0 := by
        by_contra hx0
        have h1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx0
        have : a ≤ x * a := Nat.le_mul_of_pos_left _ h1
        omega
      subst hx
      simp only [Nat.zero_mul, Nat.zero_add] at hrep
      have hmul : b * (y + 1) = y * b + b := by ring
      have hdvd : b ∣ a := ⟨y + 1, by omega⟩
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hab) hdvd
      omega

/-- The pentagon region dies: whichever of the two stubs a corner decomposition produces, the
resulting boundary segment admits no whole-edge partition. -/
theorem pentagon_region_dies (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (ha : a = e * f) (hb : b + e * e = f * f) (hc : c = f * f)
    (hstub : t = e * e % b ∨ a + t = b ∨ b + t = a) :
    0 < t ∧ ¬ Partitionable a b c t := by
  obtain ⟨h1, h2⟩ := pentagon_lemma hco he hef ha hb hc
  rcases hstub with h | h
  · subst h; exact h1
  · exact h2 t h

/-! ## The partner relation, general in `(e,f)`

`Interface.lean` carries `partner_unique_1_2/1_3/1_4/2_3` per member. It is general: the only
whole-edge partition of a length-`b` chord is a single `b`-edge. The proof needs exactly
`coprime_a_b` (above) and the size facts. -/

/-- **Partner uniqueness.** `x·a + y·b + z·c = b` forces `(x,y,z) = (0,1,0)`, for every member. -/
theorem partner_unique (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (ha : a = e * f) (hb : b + e * e = f * f) (hc : c = f * f)
    {x y z : ℕ} (h : x * a + y * b + z * c = b) : x = 0 ∧ y = 1 ∧ z = 0 := by
  have hab : Nat.Coprime a b := coprime_a_b hco ha hb
  have ha2 : 2 ≤ a := by subst ha; nlinarith
  have hb3 : 3 ≤ b := by nlinarith
  have hbc : b < c := by subst hc; nlinarith
  -- z = 0 by size, then y ≤ 1 by size
  have hz : z = 0 := by
    by_contra hz0
    have : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr hz0
    nlinarith
  subst hz
  simp only [Nat.zero_mul, Nat.add_zero] at h
  have hy : y ≤ 1 := by nlinarith
  interval_cases y
  · -- y = 0: x·a = b with gcd(a,b) = 1 forces a = 1, against a ≥ 2
    exfalso
    simp only [Nat.zero_mul, Nat.add_zero] at h
    have hdvd : a ∣ b := ⟨x, by rw [Nat.mul_comm]; exact h.symm⟩
    have := Nat.Coprime.eq_one_of_dvd hab hdvd
    omega
  · -- y = 1: x·a = 0
    have hx : x * a = 0 := by omega
    have : x = 0 := by
      rcases Nat.mul_eq_zero.mp hx with h0 | h0
      · exact h0
      · omega
    exact ⟨this, rfl, rfl⟩

end Erdos634.PentagonLemma
