import Mathlib.Tactic

/-!
# Containment kills the rogue `c`-edge below the threshold `(k−1)e < f`

Erdős #634, base-`β` branch.  The induction `W(k−1) ⟹ W(k)` (every scale-`k` inflation occurring
inside a tiling is standard) forces the row along the `B`-side and stalls at exactly one
configuration: at the slot `Y_i = A + (i+1)b·w` (`i = 1, …, k−2`), the `β`-tile may lay `c` instead
of `a` along the chord ray toward `X_i`, overrunning `X_i` by `c − a = f(f−e)`.

The rogue tile lies inside `Δ_k` (its slot is an interior angle of a region whose boundary the
tiling respects), so its `c`-edge must lie in the closed triangle.  Computing the far endpoint
`Z_i = ((i+1) − c/a)·b·w + (c²/a)·u` in barycentric coordinates against the vertices
`A, C = kb·w, B = kc·u` gives — verified by 1 537 exact-arithmetic checks over all coprime `(e,f)`
with `f ≤ 12`, and proved as the ring identities below —

    s = ((i+1)e − f)/(ek),   t = f/(ek),   s + t = (i+1)/k .

Consequences:

* `t > 0` and `s + t ≤ (k−1)/k < 1` always in the slot range, so **containment turns on the single
  sign `s`**: `Z_i` is strictly outside iff `(i+1)e < f`, and equality `(i+1)e = f` is impossible in
  range (it needs `e ∣ f`, hence `e = 1`, `i+1 = f > k−1`).
* **The step `W(k−1) ⟹ W(k)` is rogue-free at every slot iff `(k−1)e < f`.**
* **`e = 1`: rogue-free for every `k ≤ f`** — the slot range demands `i+1 ≥ f` but only reaches
  `k−1 ≤ f−1`.  With the boundary words (proved for `f/e ≥ √2`, hence all of `e = 1`) and the forced
  row, the whole induction closes on the thin family.
* **`W(e)` closes for every member with `e(e−1) < f`** — all `(1,f)`, all `(2,f)`, `(3,f)` for
  `f ≥ 7` (including `(3,7)`, the member of `N = 138`), `(4,f)` for `f ≥ 13`, …
* The corner configuration `i+1 = k = f` sits outside the slot range and is exactly the transverse
  branch: the rogue `c`-edge from `C` along `BC` coincides with the full `a`-side iff `f² = f·a`,
  i.e. `e = 1` — the case already killed by hand; for `e ≥ 2` it is shorter than the `a`-side and
  was settled by the 61 exhaustive searches.

The geometric setup (the forced row `P₀, Q₀, P₁, …`) is paper-level, from the `W(k)` session; what
is formalized here is its complete arithmetic core.  Axiom-clean.
-/

namespace Erdos634.RogueContainment

/-- **The barycentric identity.**  Clearing denominators in `s·(kb)(kc) + t·(kb)(kc) = …`:
`x_i·c + y_i·b = (i+1)·e·b·c`, where `e·x_i = b((i+1)e − f)` and `e·y_i = f³` are the cleared
`w`- and `u`-coordinates of the rogue's far endpoint.  This is `s + t = (i+1)/k` with no `k`:
the sum is independent of the inflation's scale. -/
theorem barycentric_sum (i e f : ℤ) :
    (f ^ 2 - e ^ 2) * ((i + 1) * e - f) * f ^ 2 + f ^ 3 * (f ^ 2 - e ^ 2)
      = (i + 1) * e * ((f ^ 2 - e ^ 2) * f ^ 2) := by ring

/-- The `u`-coordinate is `c²/a`: `e · (c²/a) = f³`, positive — the rogue's far endpoint always
lies strictly on the interior side of the `B`-side.  Containment therefore turns on the
`w`-coordinate alone. -/
theorem t_pos (e f : ℤ) (he : 0 < e) (hf : 0 < f) : 0 < f ^ 3 := by positivity

/-- **The sign criterion.**  The cleared `w`-coordinate `e·x_i = b·((i+1)e − f)` is negative —
the far endpoint strictly outside `Δ_k` — exactly when `(i+1)e < f` (with `b > 0`, i.e. `e < f`). -/
theorem outside_iff (i e f : ℤ) (hef : e < f) (he : 0 < e) :
    (f ^ 2 - e ^ 2) * ((i + 1) * e - f) < 0 ↔ (i + 1) * e < f := by
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  constructor <;> intro h <;> nlinarith

/-- **Equality is impossible in the slot range.**  `(i+1)e = f` with `gcd(e,f) = 1` forces `e = 1`
and `i + 1 = f`; but slots reach only `i + 1 ≤ k − 1 ≤ f − 1`. -/
theorem no_equality (i e f k : ℤ) (hcop : IsCoprime e f) (hslot : i + 1 ≤ k - 1) (hk : k ≤ f)
    (he : 1 ≤ e) (heq : (i + 1) * e = f) : False := by
  have hdvd : e ∣ f := ⟨i + 1, by linarith [heq, mul_comm (i + 1) e]⟩
  have he1 : IsUnit e := hcop.isUnit_of_dvd' dvd_rfl hdvd
  have : e = 1 ∨ e = -1 := Int.isUnit_iff.mp he1
  rcases this with h1 | h1
  · subst h1; omega
  · omega

/-- **The step threshold.**  Every slot `1 ≤ i ≤ k−2` satisfies `(i+1)e < f` — the rogue is
excluded by containment at all of them — as soon as `(k−1)e < f`. -/
theorem step_rogue_free (i e f k : ℤ) (hi : i + 1 ≤ k - 1) (h : (k - 1) * e < f)
    (he : 0 < e) : (i + 1) * e < f := by nlinarith

/-- **The thin family closes outright.**  At `e = 1` the slot range `i + 1 ≤ k − 1 ≤ f − 1` never
reaches the threshold `f`, so every step `W(k−1) ⟹ W(k)`, `k ≤ f`, is rogue-free. -/
theorem thin_family_rogue_free (i k f : ℤ) (hi : i + 1 ≤ k - 1) (hk : k ≤ f) :
    (i + 1) * 1 < f := by omega

/-- **`W(e)` closes for `e(e−1) < f`.**  The worst step of `W(e)` is `k = e`, whose threshold is
`(e−1)e < f`.  Members: all `(1,f)`, all `(2,f)`; `(3,f)` for `f ≥ 7`; `(4,f)` for `f ≥ 13`; … -/
theorem we_closes (i e f k : ℤ) (hi : i + 1 ≤ k - 1) (hke : k ≤ e) (h : (e - 1) * e < f)
    (he : 0 < e) : (i + 1) * e < f := by nlinarith

/-- `(3,7)` — the member of `N = 138`: `e(e−1) = 6 < 7`, so `W(3)` is rogue-free by containment. -/
theorem we_at_3_7 : (3 : ℤ) * (3 - 1) < 7 := by norm_num

/-- The corner configuration is the transverse branch exactly on the thin family:
the rogue `c`-edge from the `γ`-corner along the `a`-side has length `f²`, and the side has length
`f·a = e·f²`; they coincide iff `e = 1`. -/
theorem corner_is_transverse_iff (e f : ℤ) (hf : 0 < f) :
    f ^ 2 = f * (e * f) ↔ e = 1 := by
  constructor
  · intro h; nlinarith
  · rintro rfl; ring

end Erdos634.RogueContainment

#print axioms Erdos634.RogueContainment.barycentric_sum
#print axioms Erdos634.RogueContainment.outside_iff
#print axioms Erdos634.RogueContainment.no_equality
#print axioms Erdos634.RogueContainment.step_rogue_free
#print axioms Erdos634.RogueContainment.thin_family_rogue_free
#print axioms Erdos634.RogueContainment.we_closes
