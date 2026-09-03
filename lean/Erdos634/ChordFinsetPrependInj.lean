import Mathlib.Tactic

/-!
# Injectivity survives prepending two new points

Erdős #634. The isolated mechanical fact the `Finset`-sort construction's injectivity discharge
needs: prepending two new points `p, r` (distinct from each other and from every point already in
the sequence) to an already-injective bounded sequence keeps the whole extended sequence injective.
Pure index bookkeeping, no geometry.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ChordTraceReal

variable {Plane : Type*}

/-- **Injectivity survives prepending two new points.** -/
theorem injective_prepend_two {g_old : ℕ → Plane} {B : ℕ} {p r : Plane}
    (hinj_old : ∀ a b, a ≤ B → b ≤ B → a ≠ b → g_old a ≠ g_old b)
    (hpr : p ≠ r)
    (hp_old : ∀ i, i ≤ B → p ≠ g_old i)
    (hr_old : ∀ i, i ≤ B → r ≠ g_old i) :
    ∀ a b, a ≤ B + 2 → b ≤ B + 2 → a ≠ b →
      (fun i => if i = 0 then p else if i = 1 then r else g_old (i - 2)) a
        ≠ (fun i => if i = 0 then p else if i = 1 then r else g_old (i - 2)) b := by
  intro a b _ _ hab
  simp only
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · exact absurd hb0.symm (by simpa using hab)
    · simp only [if_neg hb0]
      by_cases hb1 : b = 1
      · simpa [hb1] using hpr
      · simp only [if_neg hb1]
        exact fun h => hp_old (b - 2) (by omega) h
  · by_cases ha1 : a = 1
    · subst ha1
      by_cases hb0 : b = 0
      · simpa [hb0] using hpr.symm
      · simp only [if_neg hb0]
        by_cases hb1 : b = 1
        · exact absurd hb1.symm (by simpa using hab)
        · simp only [if_neg hb1]
          exact fun h => hr_old (b - 2) (by omega) h
    · simp only [if_neg ha0, if_neg ha1]
      by_cases hb0 : b = 0
      · subst hb0; exact fun h => hp_old (a - 2) (by omega) h.symm
      · by_cases hb1 : b = 1
        · subst hb1; exact fun h => hr_old (a - 2) (by omega) h.symm
        · simp only [if_neg hb0, if_neg hb1]
          exact hinj_old (a - 2) (b - 2) (by omega) (by omega) (fun h => hab (by omega))

end Erdos634.ChordTraceReal
