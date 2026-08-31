import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Int.GCD

/-!
# Rigidity R2, R3, R5 for every `f`

`Rigidity.lean` is import-free by design and so kernel-checks R2, R3 and R5 **per member**:
`junction_residue_f2 … _f12`, `apex_gb_* / apex_bg_*`, `b_hits_lattice_f3 … _f12`.  Its header
records the gap in as many words — "the general-`f` statements are two-line ring identities plus
`f ∤ 1` … the members kernel-checked below cover every instance in current play".

Those general statements are proved here.  They are kept out of `Rigidity.lean` so that file's
no-import property survives.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RigidityGeneral

/-- **R2, the junction residue, for every `f`.**  Base-walk junctions sit at partial sums of
`{a,b,c} = {f, f²-1, f²}`; since `b ≡ -1` and `a ≡ c ≡ 0 (mod f)`, a partial sum `S` with `Q`
`b`-letters satisfies `f ∣ S + Q`.  Stated as the identity the per-member checks use. -/
theorem junction_residue (f P Q R : ℤ) :
    P * f + Q * (f ^ 2 - 1) + R * f ^ 2 + Q = f * (P + Q * f + R * f) := by
  ring

/-- **R2 as a divisibility**, which is how it is used: `f` divides `S + Q`. -/
theorem junction_residue_dvd (f P Q R : ℤ) :
    (f : ℤ) ∣ (P * f + Q * (f ^ 2 - 1) + R * f ^ 2 + Q) :=
  ⟨P + Q * f + R * f, junction_residue f P Q R⟩

/-- **R3, the apex integrality dichotomy, for every `f ≥ 2`.**  The `(β,γ)` orientation puts the
apex at `2f·x = 2(3f²-1) + 2f²(i-1)`, an integer only if `f ∣ 3f² - 1`.  But `3f² - 1 ≡ -1 (mod f)`,
so this would force `f ∣ 1`. -/
theorem apex_bg_dead (f : ℤ) (hf : 2 ≤ f) : ¬ (f ∣ 3 * f ^ 2 - 1) := by
  intro ⟨k, hk⟩
  have h1 : f ∣ (1 : ℤ) := ⟨3 * f - k, by linarith [hk]; ⟩
  have := Int.le_of_dvd one_pos h1
  omega

/-- **R3, the surviving orientation.**  The `(γ,β)` apex sits at `2f·x = 2f²·i`, i.e. `x = i·f`,
always an integer. -/
theorem apex_gb_offset (f i : ℤ) : (2 * f) ∣ 2 * f ^ 2 * i :=
  ⟨f * i, by ring⟩

/-- **R5, the interior-multiple lemma, for every `f ≥ 2`.**  The `b`-edge has length `f² - 1 ≥ f+1`,
so any placement `[p, p + f² - 1]` contains a multiple of `f` strictly inside: take `m = p/f + 1`.
Hence the `b` can never lie west of the last column apex. -/
theorem b_hits_lattice (f p : ℕ) (hf : 2 ≤ f) :
    ∃ m, p < f * m ∧ f * m < p + (f ^ 2 - 1) := by
  have hf0 : 0 < f := by omega
  have hdm : f * (p / f) + p % f = p := Nat.div_add_mod p f
  have hmod : p % f < f := Nat.mod_lt _ hf0
  have hsq : f + 1 < f ^ 2 := by nlinarith
  refine ⟨p / f + 1, ?_, ?_⟩
  · have hexp : f * (p / f + 1) = f * (p / f) + f := by ring
    omega
  · have hexp : f * (p / f + 1) = f * (p / f) + f := by ring
    omega

end Erdos634.RigidityGeneral
