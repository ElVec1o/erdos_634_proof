import Mathlib.Tactic

/-!
# The certified seeds' interface relations vanish exactly on `f = 2e`

Erdős #634, companion `thm:seeddegenerate`. The sweep over the eight kernel-certified `(1,2)`
tilings (`code/interface_census.py`) finds that every maximal straight interface's two-sided words
either agree as multisets or differ by one of the five relations

  `c = 2a`, `2b = 3a`, `2b = a + c`, `3c = 4b`, `a + 2b = 2c`.

This file formalizes the theorem's *arithmetic* half, exactly as the paper states it: evaluated at
the base-β tile `(a,b,c) = (ef, f² − e², f²)`, each of the five differences factors as a unit times
`(f − 2e)` times a quantity positive on `0 < e < f`. Hence each relation holds **iff** `f = 2e`,
which is the seed-degeneracy claim: the certified seed complexes close on `(1,2)` and on no other
member.

Not formalized here, and not claimed: the sweep itself (that these five are the *only* relations
occurring across the eight certified tilings) is a computation over concrete tilings, so the paper
statement keeps its `CONJECTURE` label.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SeedDegenerate

variable (e f : ℤ)

/-- The base-β tile's `a`-side, `a = ef`. -/
def aSide : ℤ := e * f

/-- The base-β tile's `b`-side, `b = f² − e²`. -/
def bSide : ℤ := f ^ 2 - e ^ 2

/-- The base-β tile's `c`-side, `c = f²`. -/
def cSide : ℤ := f ^ 2

/-- **Relation 1**, `c = 2a`: `c − 2a = f · (f − 2e)`. -/
theorem factor_c_two_a : cSide f - 2 * aSide e f = f * (f - 2 * e) := by
  simp [aSide, cSide]; ring

/-- **Relation 2**, `2b = 3a`: `2b − 3a = (2f + e) · (f − 2e)`. -/
theorem factor_two_b_three_a : 2 * bSide e f - 3 * aSide e f = (2 * f + e) * (f - 2 * e) := by
  simp [aSide, bSide]; ring

/-- **Relation 3**, `2b = a + c`: `2b − (a + c) = (f + e) · (f − 2e)`. -/
theorem factor_two_b_a_c : 2 * bSide e f - (aSide e f + cSide f) = (f + e) * (f - 2 * e) := by
  simp [aSide, bSide, cSide]; ring

/-- **Relation 4**, `3c = 4b`: `3c − 4b = (-1) · (f + 2e) · (f − 2e)`. -/
theorem factor_three_c_four_b :
    3 * cSide f - 4 * bSide e f = (-1) * ((f + 2 * e) * (f - 2 * e)) := by
  simp [bSide, cSide]; ring

/-- **Relation 5**, `a + 2b = 2c`: `(a + 2b) − 2c = e · (f − 2e)`. -/
theorem factor_a_two_b_two_c : aSide e f + 2 * bSide e f - 2 * cSide f = e * (f - 2 * e) := by
  simp [aSide, bSide, cSide]; ring

/-- The five cofactors are all positive on `0 < e < f`, which is the paper's "a quantity positive
on `0 < e < f`" clause. -/
theorem cofactors_pos {e f : ℤ} (he : 0 < e) (hef : e < f) :
    0 < f ∧ 0 < 2 * f + e ∧ 0 < f + e ∧ 0 < f + 2 * e ∧ 0 < e :=
  ⟨by linarith, by linarith, by linarith, by linarith, he⟩

section Iff

variable {e f} (he : 0 < e) (hef : e < f)

include he hef

/-- **Relation 1 holds iff `f = 2e`.** -/
theorem c_two_a_iff : cSide f = 2 * aSide e f ↔ f = 2 * e := by
  constructor
  · intro h
    have hfac : f * (f - 2 * e) = 0 := by rw [← factor_c_two_a e f, h]; ring
    rcases mul_eq_zero.mp hfac with h0 | h0
    · omega
    · omega
  · intro h; simp [aSide, cSide, h]; ring

/-- **Relation 2 holds iff `f = 2e`.** -/
theorem two_b_three_a_iff : 2 * bSide e f = 3 * aSide e f ↔ f = 2 * e := by
  constructor
  · intro h
    have hfac : (2 * f + e) * (f - 2 * e) = 0 := by rw [← factor_two_b_three_a e f, h]; ring
    rcases mul_eq_zero.mp hfac with h0 | h0
    · omega
    · omega
  · intro h; simp [aSide, bSide, h]; ring

/-- **Relation 3 holds iff `f = 2e`.** -/
theorem two_b_a_c_iff : 2 * bSide e f = aSide e f + cSide f ↔ f = 2 * e := by
  constructor
  · intro h
    have hfac : (f + e) * (f - 2 * e) = 0 := by rw [← factor_two_b_a_c e f, h]; ring
    rcases mul_eq_zero.mp hfac with h0 | h0
    · omega
    · omega
  · intro h; simp [aSide, bSide, cSide, h]; ring

/-- **Relation 4 holds iff `f = 2e`.** -/
theorem three_c_four_b_iff : 3 * cSide f = 4 * bSide e f ↔ f = 2 * e := by
  constructor
  · intro h
    have hfac : (-1 : ℤ) * ((f + 2 * e) * (f - 2 * e)) = 0 := by
      rw [← factor_three_c_four_b e f, h]; ring
    have hfac' : (f + 2 * e) * (f - 2 * e) = 0 := by linarith
    rcases mul_eq_zero.mp hfac' with h0 | h0
    · omega
    · omega
  · intro h; simp [bSide, cSide, h]; ring

omit hef in
/-- **Relation 5 holds iff `f = 2e`.** -/
theorem a_two_b_two_c_iff : aSide e f + 2 * bSide e f = 2 * cSide f ↔ f = 2 * e := by
  constructor
  · intro h
    have hfac : e * (f - 2 * e) = 0 := by rw [← factor_a_two_b_two_c e f]; omega
    rcases mul_eq_zero.mp hfac with h0 | h0
    · omega
    · omega
  · intro h; simp [aSide, bSide, cSide, h]; ring

/-- **The seed-degeneracy dichotomy, arithmetic half.** Every one of the five interface relations
of the certified seeds holds at the member `(e,f)` if and only if `f = 2e` — i.e. (with
`gcd(e,f) = 1`) exactly at `(1,2)`. -/
theorem all_relations_iff :
    (cSide f = 2 * aSide e f ∨ 2 * bSide e f = 3 * aSide e f ∨
      2 * bSide e f = aSide e f + cSide f ∨ 3 * cSide f = 4 * bSide e f ∨
      aSide e f + 2 * bSide e f = 2 * cSide f) ↔ f = 2 * e := by
  constructor
  · rintro (h | h | h | h | h)
    · exact (c_two_a_iff he hef).mp h
    · exact (two_b_three_a_iff he hef).mp h
    · exact (two_b_a_c_iff he hef).mp h
    · exact (three_c_four_b_iff he hef).mp h
    · exact (a_two_b_two_c_iff he).mp h
  · intro h; exact Or.inl ((c_two_a_iff he hef).mpr h)

end Iff

/-- Non-vacuity: the member `(1,2)` really does satisfy all five relations. -/
theorem relations_at_one_two :
    cSide 2 = 2 * aSide 1 2 ∧ 2 * bSide 1 2 = 3 * aSide 1 2 ∧
      2 * bSide 1 2 = aSide 1 2 + cSide 2 ∧ 3 * cSide 2 = 4 * bSide 1 2 ∧
      aSide 1 2 + 2 * bSide 1 2 = 2 * cSide 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [aSide, bSide, cSide]

/-- Non-vacuity, the other way: at `(1,3)` (the member of `thm:notuniform`) none of the five
relations holds. -/
theorem relations_fail_at_one_three :
    ¬ (cSide 3 = 2 * aSide 1 3 ∨ 2 * bSide 1 3 = 3 * aSide 1 3 ∨
      2 * bSide 1 3 = aSide 1 3 + cSide 3 ∨ 3 * cSide 3 = 4 * bSide 1 3 ∨
      aSide 1 3 + 2 * bSide 1 3 = 2 * cSide 3) := by
  intro h
  have := (all_relations_iff (by norm_num : (0:ℤ) < 1) (by norm_num : (1:ℤ) < 3)).mp h
  norm_num at this

end Erdos634.SeedDegenerate
