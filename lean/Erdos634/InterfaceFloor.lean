import Mathlib.Tactic
import Erdos634.Primitives

/-!
# The interface floor: a nonzero relation is long

`prop:interfacefloor` has two clauses.  The first — *a nonzero relation has one-sided length at
least `f·min(a,b)`* — is a statement about the relation lattice `Λ(e,f)` alone, and is proved here.
The second — *every maximal straight interface of a tiling shorter than `f·min(a,b)` carries the
same edge multiset on both sides* — needs maximal straight interfaces of a dissection as objects,
which the development does not have.

The proof is a case split on `n_b`.  If `n_b ≠ 0` then `f ∣ n_b` (`Primitives.rel_b_mult`) forces
`|n_b| ≥ f`, and the side carrying those `b`-edges already has length `≥ f·b`.  If `n_b = 0` the
relation is a multiple of `v₁ = (f, 0, -e)` (`Primitives.rel_param`), and either side has length
`|s|·f·a ≥ f·a`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.InterfaceFloor

/-- The length of the positive side of a relation `(n_a, n_b, n_c)` with side lengths `a, b, c`. -/
def oneSided (na nb nc a b c : ℤ) : ℤ := max na 0 * a + max nb 0 * b + max nc 0 * c

/-- The two sides of a relation have equal length: the positive part and the negative part. -/
theorem oneSided_eq_neg (na nb nc a b c : ℤ)
    (hrel : na * a + nb * b + nc * c = 0) :
    oneSided na nb nc a b c = max (-na) 0 * a + max (-nb) 0 * b + max (-nc) 0 * c := by
  have hsplit : ∀ x : ℤ, max x 0 = x + max (-x) 0 := by intro x; omega
  unfold oneSided
  rw [hsplit na, hsplit nb, hsplit nc]
  linarith [hrel]

/-- **The interface floor.**  For the tile `(a,b,c) = (ef, f²-e², f²)` with `0 < e < f` and
`gcd(e,f) = 1`, every nonzero relation has one-sided length at least `f · min(a,b)`. -/
theorem interface_floor (e f na nb nc : ℤ) (he : 0 < e) (hef : e < f)
    (hc : IsCoprime f e)
    (hrel : na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 = 0)
    (hne : ¬ (na = 0 ∧ nb = 0 ∧ nc = 0)) :
    f * min (e * f) (f ^ 2 - e ^ 2)
      ≤ oneSided na nb nc (e * f) (f ^ 2 - e ^ 2) (f ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  have ha : 0 < e * f := mul_pos he hf
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hcc : 0 < f ^ 2 := by positivity
  have hmin_a : min (e * f) (f ^ 2 - e ^ 2) ≤ e * f := min_le_left _ _
  have hmin_b : min (e * f) (f ^ 2 - e ^ 2) ≤ f ^ 2 - e ^ 2 := min_le_right _ _
  rcases lt_trichotomy nb 0 with hlt | heq | hgt
  · -- the `b`-edges sit on the negative side
    have hdvd : f ∣ nb := Erdos634.Primitives.rel_b_mult na nb nc e f hc hrel
    have hge : f ≤ -nb := by
      obtain ⟨k, hk⟩ := hdvd
      have hkneg : k ≤ -1 := by nlinarith [hk]
      nlinarith [hk]
    rw [oneSided_eq_neg na nb nc _ _ _ (by linarith [hrel])]
    have h1 : 0 ≤ max (-na) 0 * (e * f) := by positivity
    have h3 : 0 ≤ max (-nc) 0 * f ^ 2 := by positivity
    have h2 : max (-nb) 0 = -nb := by omega
    nlinarith [h1, h3, h2, hge, hb, hmin_b]
  · -- `b`-free: a multiple of `v₁ = (f, 0, -e)`
    subst heq
    have hrel' : na * (e * f) + nc * f ^ 2 = 0 := by linarith [hrel]
    obtain ⟨s, hs1, hs2⟩ :=
      Erdos634.Primitives.rel_param na nc e f (ne_of_gt hf) hc hrel'
    have hs0 : s ≠ 0 := by
      rintro rfl; exact hne ⟨by simpa using hs1, rfl, by simpa using hs2⟩
    unfold oneSided
    have hzero : max (0 : ℤ) 0 = 0 := by simp
    have hfa : f * (e * f) = e * f ^ 2 := by ring
    have hmin : f * min (e * f) (f ^ 2 - e ^ 2) ≤ f * (e * f) := by
      have := hmin_a; nlinarith
    rcases lt_or_gt_of_ne hs0 with hneg | hpos
    · -- the `c`-side carries `e|s|` edges of length `f²`
      have hnale : na ≤ 0 := by rw [hs1]; nlinarith
      have hncge : (0 : ℤ) ≤ nc := by rw [hs2]; nlinarith
      have hna : max na 0 = 0 := max_eq_right hnale
      have hnc : max nc 0 = nc := max_eq_left hncge
      have hs1' : (1 : ℤ) ≤ -s := by omega
      have hpos2 : (0 : ℤ) ≤ e * f ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hs1' hpos2
      have hstep : e * f ^ 2 ≤ nc * f ^ 2 := by rw [hs2]; nlinarith [hmul]
      rw [hna, hnc, hzero]
      linarith [hmin, hstep, hfa]
    · -- the `a`-side carries `f·s` edges of length `a`
      have hnage : (0 : ℤ) ≤ na := by rw [hs1]; nlinarith
      have hncle : nc ≤ 0 := by rw [hs2]; nlinarith
      have hna : max na 0 = na := max_eq_left hnage
      have hnc : max nc 0 = 0 := max_eq_right hncle
      have hs1' : (1 : ℤ) ≤ s := hpos
      have hpos2 : (0 : ℤ) ≤ f * (e * f) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hs1' hpos2
      have hstep : f * (e * f) ≤ na * (e * f) := by rw [hs1]; nlinarith [hmul]
      rw [hna, hnc, hzero]
      linarith [hmin, hstep]
  · -- the `b`-edges sit on the positive side
    have hdvd : f ∣ nb := Erdos634.Primitives.rel_b_mult na nb nc e f hc hrel
    have hge : f ≤ nb := by
      obtain ⟨k, hk⟩ := hdvd
      have hkpos : 1 ≤ k := by nlinarith [hk]
      nlinarith [hk]
    unfold oneSided
    have h1 : 0 ≤ max na 0 * (e * f) := by positivity
    have h3 : 0 ≤ max nc 0 * f ^ 2 := by positivity
    have h2 : max nb 0 = nb := by omega
    nlinarith [h1, h3, h2, hge, hb, hmin_b]

/-! ## The hypotheses are satisfiable, and the bound is sharp -/

/-- `v₁ = (f, 0, -e)` is a relation. -/
theorem v1_relation (e f : ℤ) :
    f * (e * f) + 0 * (f ^ 2 - e ^ 2) + (-e) * f ^ 2 = 0 := by ring

/-- `v₁` is nonzero, so `interface_floor`'s hypotheses are not vacuous. -/
theorem v1_nonzero (e f : ℤ) (hf : 0 < f) : ¬ (f = 0 ∧ (0 : ℤ) = 0 ∧ -e = 0) := by
  rintro ⟨h, -, -⟩; omega

/-- **The floor is attained**, by `v₁` itself: its positive side is the `f` `a`-edges, of total
length `f·a`.  So `f·min(a,b)` is the exact floor whenever `min(a,b) = a`. -/
theorem floor_attained (e f : ℤ) (he : 0 < e) (hf : 0 < f) :
    oneSided f 0 (-e) (e * f) (f ^ 2 - e ^ 2) (f ^ 2) = f * (e * f) := by
  unfold oneSided
  have h1 : max f 0 = f := max_eq_left (le_of_lt hf)
  have h2 : max (0 : ℤ) 0 = 0 := by simp
  have h3 : max (-e) 0 = 0 := max_eq_right (by omega)
  rw [h1, h2, h3]; ring

end Erdos634.InterfaceFloor
