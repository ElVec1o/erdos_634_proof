import Mathlib.Tactic

/-!
# `b` is not a nontrivial sum of `{a,b,c}`-lengths

Erdős #634, toward `prop:cornerpara` ("the corner tile's `b`-edge is a chord matched by exactly
one tile"). `WallChain.wall_two_sided`/`.edge_two_sided` (pre-existing, general) give that any tile
edge lying in the target's interior is covered, on each side, by a *chain* of other tiles' edges
whose combined length equals the edge's own — but not that the chain has exactly one element. For
the base-β tile family `(a,b,c) = (f, f²−1, f²)` at `e = 1`, closing that gap for the `b`-edge
needs exactly one further fact: `b` cannot be written as a sum of two or more terms drawn from
`{a,b,c}` (with repetition) — so the covering chain on the far side of a `b`-edge, whatever
lengths it uses, can only be the trivial one-tile chain.

This is a genuinely different fact from `Pentagon.no_partition`/`.stub_lt_a_and_b`/
`.pentagon_stub_kills` (which bound a different quantity, the *stub* `e² mod b`, not `b` itself)
and from the walk-decomposition literature (`CChord`/`SideNoB`/`ChainWalk`), which concerns a
*side*'s decomposition in the walk model, a different combinatorial object from one tile edge.

The proof is a `mod f` argument: any nontrivial combination with `y = 0` sums to a multiple of `f`
plus possibly `z·f²` (still a multiple of `f`), but `b = f² − 1 ≡ f − 1 ≢ 0 (mod f)` for `f ≥ 2`;
and any combination with `y ≥ 1` already has `y·b ≥ b`, forcing `x = z = 0` and `y = 1`, the
trivial case.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.EdgeGap

/-- **`b` is never a nontrivial sum of `{a,b,c}`-lengths.** For the base-β tile family with
`a = f`, `b + 1 = f·f`, `c = f·f`: if `x` copies of `a`, `y` copies of `b`, `z` copies of `c` sum
to `b`, using at least one term, then `(x,y,z) = (0,1,0)` — the trivial one-term sum. -/
theorem b_not_partitionable (f b x y z : ℕ) (hf : 2 ≤ f) (hb : b + 1 = f * f)
    (heq : x * f + y * b + z * (f * f) = b) (hpos : 1 ≤ x + y + z)
    (hne : ¬ (x = 0 ∧ y = 1 ∧ z = 0)) : False := by
  rcases Nat.eq_zero_or_pos y with hy0 | hypos
  · subst hy0
    simp only [Nat.zero_mul, Nat.add_zero] at heq
    have hdvd : f ∣ (x * f + z * (f * f)) := by
      have h2 : f ∣ x * f := ⟨x, mul_comm x f⟩
      have h3 : f ∣ z * (f * f) := ⟨z * f, by ring⟩
      exact Nat.dvd_add h2 h3
    rw [heq] at hdvd
    have hb' : b = f * (f - 1) + (f - 1) := by
      have hfm1 : (f - 1) + 1 = f := by omega
      nlinarith [hfm1, hb]
    rw [hb'] at hdvd
    have hdvd2 : f ∣ (f - 1) := (Nat.dvd_add_right ⟨f - 1, rfl⟩).mp hdvd
    have hpos2 : 0 < f - 1 := by omega
    have hle := Nat.le_of_dvd hpos2 hdvd2
    omega
  · have hyge : b ≤ y * b := Nat.le_mul_of_pos_left _ hypos
    have hxf0 : x * f = 0 := by nlinarith [heq, hyge, Nat.zero_le (z * (f * f))]
    have hzff0 : z * (f * f) = 0 := by nlinarith [heq, hyge, Nat.zero_le (x * f)]
    have hx0 : x = 0 := by
      rcases Nat.eq_zero_or_pos x with h | h
      · exact h
      · exfalso; have : 0 < x * f := Nat.mul_pos h (by omega); omega
    have hz0 : z = 0 := by
      rcases Nat.eq_zero_or_pos z with h | h
      · exact h
      · exfalso; have : 0 < z * (f * f) := Nat.mul_pos h (by positivity); omega
    have hy1 : y = 1 := by
      rcases Nat.lt_or_ge y 2 with hy | hy
      · omega
      · exfalso
        have h2b : 2 * b ≤ y * b := Nat.mul_le_mul_right b hy
        nlinarith [heq, h2b, Nat.zero_le (x * f), Nat.zero_le (z * (f * f))]
    exact hne ⟨hx0, hy1, hz0⟩

end Erdos634.EdgeGap
