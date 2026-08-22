import Mathlib.Tactic

/-!
# The base-word set is a decidable finite enumeration

Erdős #634 — lifting atom B3 from HEURISTIC to VERIFIED.

The base-word count was a Python enumeration, which is evidence and not proof.  This file makes it a
theorem: the set of base words at a member `(e,f)` is the `Finset` of `(P,Q,R)` in an explicit box
satisfying `P a + Q b + R c = T`, the box provably contains every solution, and the counts are
closed by `decide`.

`bound_of_eq` is the only content: from `P a + Q b + R c = T` with `a, b, c > 0` and all of
`P, Q, R ≥ 0`, each coordinate is bounded — `P a ≤ T` gives `P ≤ T / a`.  So the box
`[0, T/a] × [0, T/b] × [0, T/c]` loses nothing, and `mem_baseWords` is an iff.

Counts obtained (each by `decide`, so kernel-checked, not trusted from a script):

| member | `N` | base words |
|---|---|---|
| `(1,2)` | 11 | 4 |
| `(1,3)` | 26 | 3 |
| `(2,3)` | 23 | 5 |
| `(5,6)` | 83 | **8** |

The `(5,6)` count is the one that matters: the running `N = 83` search carries **five** base words,
so three were missing, and they are now running separately.  Earlier counts of five and seven in
this development were both wrong; this is the kernel-checked figure.

Axiom-clean; no `sorry`, no `native_decide`.
-/

set_option maxRecDepth 40000

namespace Erdos634.WordCount

/-- The box of candidate base words: `P ≤ T/a`, `Q ≤ T/b`, `R ≤ T/c`. -/
def box (a b c T : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (T / a + 1)) ×ˢ (Finset.range (T / b + 1)) ×ˢ (Finset.range (T / c + 1))

/-- The base words at a member: the solutions of `P a + Q b + R c = T` inside the box. -/
def baseWords (a b c T : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (box a b c T).filter (fun w => w.1 * a + w.2.1 * b + w.2.2 * c = T)

/-- **The box loses nothing.**  A nonnegative solution has each coordinate bounded by `T` divided by
the corresponding edge length. -/
theorem bound_of_eq {a b c T P Q R : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : P * a + Q * b + R * c = T) : P ≤ T / a ∧ Q ≤ T / b ∧ R ≤ T / c := by
  refine ⟨Nat.le_div_iff_mul_le ha |>.mpr (by omega),
          Nat.le_div_iff_mul_le hb |>.mpr (by omega),
          Nat.le_div_iff_mul_le hc |>.mpr (by omega)⟩

/-- **The enumeration is exactly the solution set.**  Membership in `baseWords` is equivalent to
solving the base equation, with no side condition. -/
theorem mem_baseWords {a b c T P Q R : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (P, Q, R) ∈ baseWords a b c T ↔ P * a + Q * b + R * c = T := by
  constructor
  · intro hmem
    simpa using (Finset.mem_filter.mp hmem).2
  · intro heq
    obtain ⟨h1, h2, h3⟩ := bound_of_eq ha hb hc heq
    refine Finset.mem_filter.mpr ⟨?_, by simpa using heq⟩
    simp only [box, Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega, by omega⟩

/-! ### The counts, closed by `decide` -/

/-- `(1,2)`, `N = 11`: tile `(2,3,4)`, base length `11`.  Four base words. -/
theorem count_1_2 : (baseWords 2 3 4 11).card = 4 := by decide

/-- `(1,3)`, `N = 26`: tile `(3,8,9)`, base length `26`.  Three base words. -/
theorem count_1_3 : (baseWords 3 8 9 26).card = 3 := by decide

/-- `(2,3)`, `N = 23`: tile `(6,5,9)`, base length `46`.  Five base words. -/
theorem count_2_3 : (baseWords 6 5 9 46).card = 5 := by decide

/-- **`(5,6)`, `N = 83`: tile `(30,11,36)`, base length `415`.  Eight base words.**
The running search carries five. -/
theorem count_5_6 : (baseWords 30 11 36 415).card = 8 := by decide

/-- The eight words of `83`, explicitly, and each is genuinely in the set. -/
theorem words_5_6 :
    (0, 5, 10) ∈ baseWords 30 11 36 415 ∧ (1, 35, 0) ∈ baseWords 30 11 36 415
      ∧ (2, 29, 1) ∈ baseWords 30 11 36 415 ∧ (3, 23, 2) ∈ baseWords 30 11 36 415
      ∧ (4, 17, 3) ∈ baseWords 30 11 36 415 ∧ (5, 11, 4) ∈ baseWords 30 11 36 415
      ∧ (6, 5, 5) ∈ baseWords 30 11 36 415 ∧ (12, 5, 0) ∈ baseWords 30 11 36 415 := by
  have H : ∀ P Q R : ℕ, P * 30 + Q * 11 + R * 36 = 415 → (P,Q,R) ∈ baseWords 30 11 36 415 :=
    fun P Q R h => (mem_baseWords (by norm_num) (by norm_num) (by norm_num)).mpr h
  exact ⟨H _ _ _ (by norm_num), H _ _ _ (by norm_num), H _ _ _ (by norm_num),
         H _ _ _ (by norm_num), H _ _ _ (by norm_num), H _ _ _ (by norm_num),
         H _ _ _ (by norm_num), H _ _ _ (by norm_num)⟩

/-- The three words absent from the running `N = 83` instance are genuine base words. -/
theorem missing_from_search :
    (1, 35, 0) ∈ baseWords 30 11 36 415 ∧ (2, 29, 1) ∈ baseWords 30 11 36 415
      ∧ (12, 5, 0) ∈ baseWords 30 11 36 415 :=
  ⟨words_5_6.2.1, words_5_6.2.2.1, words_5_6.2.2.2.2.2.2.2⟩

end Erdos634.WordCount

#print axioms Erdos634.WordCount.bound_of_eq
#print axioms Erdos634.WordCount.mem_baseWords
#print axioms Erdos634.WordCount.count_1_2
#print axioms Erdos634.WordCount.count_1_3
#print axioms Erdos634.WordCount.count_2_3
#print axioms Erdos634.WordCount.count_5_6
#print axioms Erdos634.WordCount.words_5_6
#print axioms Erdos634.WordCount.missing_from_search
