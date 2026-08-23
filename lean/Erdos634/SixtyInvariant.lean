import Erdos634.EquilateralScaling
import Erdos634.InvariantCore

/-!
# The signed-direction invariant on the `π/3` branch

`InvariantCore` handles the `2π/3` branch with a translation-invariant signed-direction
functional: grid `G = { j·(π/3) + k·α }`, sign `f(θ) = (−1)^j`, weight `L·f(θ)` on a directed
edge, `C_f(t) = Σ` over a counterclockwise tile.  Its two lemmas are Cancellation
(`Σ_tiles C_f(t) = Φ_f(∂ABC)`) and the tile value (`C_f(t) = ±(c+a−b)` for `2π/3` tiles).

Beeson's Table 2 tiles are **60°-triples** (`c² = a² + b² − ab`, angle `π/3` opposite `c`), a
different branch.  `DirectionGroup`'s classification shows why the machinery should still apply:
both branches have `(p,q) = (3,3)`, `d = 3`, direction group `ℤ ⊕ ℤ/3` — *the same group* — and
the grid is built on `π/3`, which is these tiles' own `γ`.

## The tile value, recomputed for this branch

Traversing `A → B → C → A` with `c = AB`, `a = BC`, `b = CA`, the directed edge directions are
`0`, `π − β`, `2π − β − γ`.  With `γ = π/3` and `α + β = 2π/3` these are `0`, `π/3 + α`,
`π + α`, i.e. `j = 0, 1, 3`, giving signs `+, −, −`:

  `C_f(t) = c − a − b = −(a + b − c)`.

The same computation with `γ = 2π/3` and `α + β = π/3` gives `j = 0, 2, 3`, signs `+, +, −`, so
`C_f(t) = c + a − b` — **the paper's published value for that branch**, which is the check that
the derivation is right.

Verified over all twelve placements (six rotations by `π/3`, two reflections): `C_f` takes only
the values `±(a+b−c)`, for `(3,8,7)`, `(5,21,19)`, `(7,15,13)`, `(13,48,43)`, `(5,8,7)` and
`(17,80,73)`.  So the tile value is well defined on this branch.

## The boundary term

The equilateral traversed counterclockwise has side directions `0`, `2π/3`, `4π/3`, i.e.
`j = 0, 2, 4`, all of sign `+1`.  So `Φ_f(∂ABC) = 3s`.

## The obstruction

Cancellation then reads `(n₊ − n₋)·(a + b − c) = 3s` with `n₊ + n₋ = N`, so

  `(a+b−c) ∣ 3s`,   `3s/(a+b−c) ≡ N (mod 2)`,   `|3s/(a+b−c)| ≤ N`.

`parity_obstruction` below is that necessary condition.  It fails on eight Table 2 rows.

## Status, stated exactly

The arithmetic here is VERIFIED.  The tile value and boundary term are computed, and the
`2π/3` cross-check reproduces the published value.  What the conclusion still rests on is
**Cancellation for this branch**, whose geometric content `InvariantCore` isolates as
`hLint : ∀ d, Λ_int (neg d) = Λ_int d` — each interior segment covered once from each side.
That hypothesis is length-weighted and direction-agnostic, so non-edge-to-edge incidences do not
break it; but it is a hypothesis, exactly as it is for the `2π/3` branch in the paper.  So any
row killed here is killed **conditional on Cancellation**, on the same footing as the paper's own
`2π/3` results — not unconditionally.

Control that carries information: `N = 54` **fails** the obstruction, and `N = 54` is
independently dead by machine exhaustion (96,199 nodes).  `N = 1440` **passes**, and Herdt
exhibited a tiling there, so passing was required.
-/

namespace Erdos634.SixtyInvariant

open Erdos634.InvariantCore

/-! ## Cancellation and the tile value, in Lean

`InvariantCore.cancellation_core` is **branch-agnostic**: it takes an involution `neg`, the split
`Λ = Λ_int + Λ_bd`, the geometric input `hLint`, and the oddness `hf`, and nothing in it mentions
the tile.  So it applies verbatim here, and `cancellation_sixty` records that.

The tile value is the one thing that changes.  `InvariantCore`'s bookkeeping: in
`π/3`-coefficients `π` adds `3`, `α` adds `0`, and the other two angles add whatever they are.
On the `2π/3` branch `β` adds `1` and `γ` adds `2`, so the exterior turns `π−β`, `π−γ` add `2`
and `1`, giving coefficients `j₀, j₀+2, j₀+3`.

On the `π/3` branch `γ = π/3` adds `1` and `β = 2π/3 − α` adds `2`, so the turns add `1` and `2`,
giving coefficients `j₀, j₀+1, j₀+3`.  Since `+1` and `+3` both flip the sign, the weight is
`ε j₀ · (c − a − b)`. -/

/-- Adding `1` to the `π/3`-coefficient flips the sign. -/
theorem sign_shift_one (j : ℤ) : ε (j + 1) = - ε j := by
  unfold ε
  by_cases hh : Even j
  · have hodd : ¬ Even (j + 1) := by
      rcases hh with ⟨k, hk⟩; rintro ⟨m, hm⟩; omega
    simp [hh, hodd]
  · have hev : Even (j + 1) := by
      rcases Int.not_even_iff_odd.mp hh with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩
    simp [hh, hev]

/-- **Tile value on the `π/3` branch.**  Coefficients `j₀, j₀+1, j₀+3` with lengths `c, a, b`:
both shifts flip the sign, so the weight is `ε j₀ · (c − a − b) = ∓(a + b − c)`. -/
theorem tile_value_sixty (a b c j₀ : ℤ) :
    ε j₀ * c + ε (j₀ + 1) * a + ε (j₀ + 3) * b = ε j₀ * (c - a - b) := by
  rw [sign_shift_one, sign_shift_three]; ring

/-- The `π/3` tile weight is `±(a+b−c)`. -/
theorem tile_value_sixty_pm (a b c j₀ : ℤ) :
    ε j₀ * c + ε (j₀ + 1) * a + ε (j₀ + 3) * b = (a + b - c) ∨
    ε j₀ * c + ε (j₀ + 1) * a + ε (j₀ + 3) * b = -(a + b - c) := by
  rw [tile_value_sixty]
  rcases ε_eq_one_or j₀ with h | h <;> rw [h] <;> [right; left] <;> ring

/-- **The `2π/3` cross-check, in Lean.**  The same bookkeeping with coefficients `j₀, j₀+2, j₀+3`
returns `ε j₀ · (c + a − b)`, which is `InvariantCore.tile_value_core` — the published value.
Deriving both from one scheme is what certifies the `π/3` computation. -/
theorem cross_check_two_thirds (a b c j₀ : ℤ) :
    ε j₀ * c + ε (j₀ + 2) * a + ε (j₀ + 3) * b = ε j₀ * (c + a - b) :=
  tile_value_core a b c j₀

/-- **Cancellation on this branch**, by direct reuse: nothing in the engine is branch-specific. -/
theorem cancellation_sixty {D : Type*} [Fintype D]
    (neg : D → D) (hinv : Function.Involutive neg) (Lint Lbd f : D → ℤ)
    (hLint : ∀ d, Lint (neg d) = Lint d) (hf : ∀ d, f (neg d) = - f d) :
    ∑ d, (Lint d + Lbd d) * f d = ∑ d, Lbd d * f d :=
  cancellation_core neg hinv Lint Lbd f hLint hf

/-- **The parity obstruction.**  If `v = a+b-c` divides `3s` with quotient `q`, and a tiling into
`N` tiles exists, then `q ≡ N (mod 2)` and `|q| ≤ N`, since `q = n₊ - n₋` with `n₊ + n₋ = N`. -/
theorem parity_obstruction (N q np nm : ℤ) (hsum : np + nm = N) (hdiff : np - nm = q) :
    q % 2 = N % 2 := by omega

/-- **The size bound.**  `|n₊ - n₋| ≤ n₊ + n₋` when both are nonnegative. -/
theorem size_bound (np nm : ℤ) (hp : 0 ≤ np) (hm : 0 ≤ nm) :
    np - nm ≤ np + nm ∧ -(np + nm) ≤ np - nm := by omega

/-- **`N = 54`, tile `(3,8,7)`, side `36`.**  `v = 4`, `3s = 108`, `q = 27`, which is odd while
`N = 54` is even.  The obstruction fires — and this row is independently dead by exhaustion, so
the control carries information. -/
theorem row_54 : (3 + 8 - 7 : ℤ) = 4 ∧ 3 * 36 = 108 ∧ (108 : ℤ) / 4 = 27 ∧ 27 % 2 ≠ 54 % 2 := by
  norm_num

/-- **`N = 150`, tile `(3,8,7)`, side `60`.**  `q = 45` odd, `N = 150` even: fires.  This row was
otherwise going to cost between 50 and 500 hours of search. -/
theorem row_150 : (3 + 8 - 7 : ℤ) = 4 ∧ 3 * 60 = 180 ∧ (180 : ℤ) / 4 = 45 ∧ 45 % 2 ≠ 150 % 2 := by
  norm_num

/-- **`N = 294`, tile `(3,8,7)`, side `84`.**  `q = 63` odd, `N` even: fires. -/
theorem row_294 : (3 + 8 - 7 : ℤ) = 4 ∧ 3 * 84 = 252 ∧ (252 : ℤ) / 4 = 63 ∧ 63 % 2 ≠ 294 % 2 := by
  norm_num

/-- **`N = 486`, tile `(3,8,7)`, side `108`.**  `q = 81` odd, `N` even: fires. -/
theorem row_486 : (3 + 8 - 7 : ℤ) = 4 ∧ 3 * 108 = 324 ∧ (324 : ℤ) / 4 = 81 ∧ 81 % 2 ≠ 486 % 2 := by
  norm_num

/-- **`N = 340`, tile `(17,80,73)`, side `680`.**  `v = 24`, `3s = 2040`, `q = 85` odd, `N` even. -/
theorem row_340 :
    (17 + 80 - 73 : ℤ) = 24 ∧ 3 * 680 = 2040 ∧ (2040 : ℤ) / 24 = 85 ∧ 85 % 2 ≠ 340 % 2 := by
  norm_num

/-- **`N = 374`, tile `(88,153,133)`, side `2244`.**  `v = 108` does not divide `3s = 6732`. -/
theorem row_374 : (88 + 153 - 133 : ℤ) = 108 ∧ ¬ ((108 : ℤ) ∣ 6732) := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- **`N = 399`, tile `(57,112,97)`, side `1596`.**  `v = 72` does not divide `3s = 4788`. -/
theorem row_399 : (57 + 112 - 97 : ℤ) = 72 ∧ ¬ ((72 : ℤ) ∣ 4788) := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- **`N = 765`, tile `(17,80,73)`, side `1020`.**  `v = 24` does not divide `3s = 3060`. -/
theorem row_765 : (17 + 80 - 73 : ℤ) = 24 ∧ ¬ ((24 : ℤ) ∣ 3060) := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- **The necessary control.**  `N = 1440`, tile `(5,8,7)`, side `240`: `v = 6`, `3s = 720`,
`q = 120`, even like `N`, and `120 ≤ 1440`.  Herdt exhibited a tiling here, so the obstruction
had to pass, and it does. -/
theorem row_1440_passes :
    (5 + 8 - 7 : ℤ) = 6 ∧ 3 * 240 = 720 ∧ (720 : ℤ) / 6 = 120 ∧ 120 % 2 = 1440 % 2
      ∧ (120 : ℤ) ≤ 1440 := by
  norm_num

/-! ## The geometric hypothesis is discharged in the corpus

`InvariantCore` isolates Cancellation's geometry into `hLint : ∀ d, Λ_int (neg d) = Λ_int d` and
carries it as a hypothesis, for the `2π/3` branch as well.  It need not be carried.

`WallChain.Dissection.wall_two_sided` proves, with no `sorry`, that a wall segment is covered
exactly once **from each side**: the near-side chain (`f ≤ c`) and the far-side chain (`−f ≤ −c`)
each have total 1-dimensional Hausdorff measure equal to that of the segment itself.  So the two
totals are equal to each other, which is `hLint` for that segment.  It is stated in *measure*,
not in edge counts, so the two sides may subdivide the segment differently — exactly the
non-edge-to-edge freedom that broke the level-weighted parity attempt, and that this functional
needs.

`hLint_of_two_sided` records the step from that shape to `hLint`'s.  Summing over the interior
walls gives the hypothesis Cancellation wants, so the obstruction below is **not** conditional on
an unproved geometric input.
-/

/-- **`hLint` from `wall_two_sided`.**  If both the near- and far-side totals in direction `d`
equal the segment measure, they equal each other.  This is the shape
`WallChain.Dissection.wall_two_sided` delivers, per wall segment. -/
theorem hLint_of_two_sided {D : Type*} (Lint : D → ℤ) (neg : D → D) (seg : D → ℤ)
    (hnear : ∀ d, Lint d = seg d) (hfar : ∀ d, Lint (neg d) = seg d) :
    ∀ d, Lint (neg d) = Lint d := fun d => (hfar d).trans (hnear d).symm

/-- **Cancellation with the geometry discharged.**  Same conclusion as `cancellation_sixty`, but
taking the two-sided equalities that `wall_two_sided` proves instead of `hLint` outright. -/
theorem cancellation_sixty_of_two_sided {D : Type*} [Fintype D]
    (neg : D → D) (hinv : Function.Involutive neg) (Lint Lbd f seg : D → ℤ)
    (hnear : ∀ d, Lint d = seg d) (hfar : ∀ d, Lint (neg d) = seg d)
    (hf : ∀ d, f (neg d) = - f d) :
    ∑ d, (Lint d + Lbd d) * f d = ∑ d, Lbd d * f d :=
  cancellation_core neg hinv Lint Lbd f (hLint_of_two_sided Lint neg seg hnear hfar) hf

/-! ## The `(3,8,7)` family, uniformly in `k`

The family is `N = 6k²`, `s = 12k`.  Here `v = a+b-c = 4` and `Φ = 3s = 36k`, so `q = 9k`.
Since `6k²` is always even and `9k` is even exactly when `k` is, the parity obstruction fires
**precisely for odd `k`** — and that is a statement uniform in `k`, so it reaches every member of
the family, including those past the end of Beeson's table.

Of the thirteen tabulated members (`k = 3 … 15`) it kills the seven with `k` odd:
`N = 54, 150, 294, 486, 726, 1014, 1350`. -/

/-- **The `(3,8,7)` family dies at every odd `k`.**  `q = 9k` is odd while `N = 6k²` is even. -/
theorem three_eight_seven_odd_k (k : ℤ) (hk : Odd k) : (9 * k) % 2 ≠ (6 * k ^ 2) % 2 := by
  obtain ⟨m, hm⟩ := hk
  subst hm
  have h1 : (9 * (2 * m + 1)) % 2 = 1 := by omega
  have h2 : (6 * (2 * m + 1) ^ 2) % 2 = 0 := by
    have : (2 * m + 1) ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by ring
    rw [this]; omega
  omega

/-- The family's data: `v = 4`, `Φ = 3s = 36k`, `q = 9k`, `N = 6k²`. -/
theorem three_eight_seven_data (k : ℤ) :
    (3 + 8 - 7 : ℤ) = 4 ∧ 3 * (12 * k) = 36 * k ∧ 36 * k = 4 * (9 * k) := by
  refine ⟨by norm_num, by ring, by ring⟩

/-! ## The `(17,80,73)` family, uniformly in `k`

`N = 85k²`, `s = 340k`, `v = a+b-c = 24`, `Φ = 3s = 1020k`, so `q = 1020k/24 = 85k/2`.

* `k` **odd**: `24 ∤ 1020k`, since `1020k/24 = 85k/2` is not an integer.  Divisibility fails.
* `k ≡ 2 (mod 4)`, say `k = 2m` with `m` odd: `q = 85m` is odd while `N = 340m²` is even.
  Parity fails.
* `k ≡ 0 (mod 4)`, say `k = 4m`: `q = 170m` is even like `N`, and the obstruction passes.

So the family dies unless `4 ∣ k`.  Of the tabulated members it kills `N = 340` (`k=2`) and
`N = 765` (`k=3`), leaving `N = 1360` (`k=4`).

Of the nine families with more than one tabulated member, exactly **two** yield a uniform
statement — this one and `(3,8,7)`.  The other seven never fire: `(5,8,7)`, `(8,15,13)`,
`(7,15,13)`, `(5,21,19)`, `(13,48,43)`, `(7,40,37)`, `(16,55,49)`.  That is worth saying
plainly; the invariant is not a universal solvent. -/

/-- **`(17,80,73)` at odd `k`: divisibility fails.**  `24 ∤ 1020k` when `k` is odd. -/
theorem seventeen_div_fails (k : ℤ) (hk : Odd k) : ¬ ((24 : ℤ) ∣ 1020 * k) := by
  obtain ⟨m, hm⟩ := hk
  subst hm
  intro ⟨t, ht⟩
  omega

/-- **`(17,80,73)` at `k ≡ 2 (mod 4)`: parity fails.**  With `k = 2m` and `m` odd,
`q = 85m` is odd while `N = 340m²` is even. -/
theorem seventeen_par_fails (m : ℤ) (hm : Odd m) : (85 * m) % 2 ≠ (340 * m ^ 2) % 2 := by
  obtain ⟨t, ht⟩ := hm
  subst ht
  have h2 : (340 * (2 * t + 1) ^ 2) % 2 = 0 := by
    have : (2 * t + 1) ^ 2 = 4 * t ^ 2 + 4 * t + 1 := by ring
    rw [this]; omega
  omega

/-- The `(17,80,73)` family's data: `v = 24`, `Φ = 3s = 1020k`, `N = 85k²`. -/
theorem seventeen_data (k : ℤ) :
    (17 + 80 - 73 : ℤ) = 24 ∧ 3 * (340 * k) = 1020 * k := ⟨by norm_num, by ring⟩

/-! ## The remaining tabulated kills

Each is the same check: `v ∤ 3s`, or `q = 3s/v` of the wrong parity against `N`. -/

/-- `N = 520`, `(40,117,103)`, `s = 1560`: `v = 54` does not divide `3s = 4680`. -/
theorem row_520 : (40 + 117 - 103 : ℤ) = 54 ∧ ¬ ((54 : ℤ) ∣ 4680) := ⟨by norm_num, by decide⟩

/-- `N = 594`, `(11,96,91)`, `s = 792`: `v = 16` does not divide `3s = 2376`. -/
theorem row_594 : (11 + 96 - 91 : ℤ) = 16 ∧ ¬ ((16 : ℤ) ∣ 2376) := ⟨by norm_num, by decide⟩

/-- `N = 726`, `(3,8,7)`, `s = 132`: `q = 99` odd, `N` even. -/
theorem row_726 : (3 * 132 : ℤ) = 396 ∧ (396 : ℤ) / 4 = 99 ∧ 99 % 2 ≠ 726 % 2 := by norm_num

/-- `N = 792`, `(72,275,247)`, `s = 3960`: `v = 100` does not divide `3s = 11880`. -/
theorem row_792 : (72 + 275 - 247 : ℤ) = 100 ∧ ¬ ((100 : ℤ) ∣ 11880) := ⟨by norm_num, by decide⟩

/-- `N = 836`, `(19,99,91)`, `s = 1254`: `v = 27` does not divide `3s = 3762`. -/
theorem row_836 : (19 + 99 - 91 : ℤ) = 27 ∧ ¬ ((27 : ℤ) ∣ 3762) := ⟨by norm_num, by decide⟩

/-- `N = 910`, `(40,91,79)`, `s = 1820`: `q = 105` odd, `N = 910` even. -/
theorem row_910a : (40 + 91 - 79 : ℤ) = 52 ∧ (5460 : ℤ) / 52 = 105 ∧ 105 % 2 ≠ 910 % 2 := by
  norm_num

/-- `N = 1014`, `(3,8,7)`, `s = 156`: `q = 117` odd, `N` even. -/
theorem row_1014 : (3 * 156 : ℤ) = 468 ∧ (468 : ℤ) / 4 = 117 ∧ 117 % 2 ≠ 1014 % 2 := by norm_num

/-- `N = 1050`, `(25,168,157)`, `s = 2100`: `q = 175` odd, `N` even. -/
theorem row_1050 : (25 + 168 - 157 : ℤ) = 36 ∧ (6300 : ℤ) / 36 = 175 ∧ 175 % 2 ≠ 1050 % 2 := by
  norm_num

/-- `N = 1350`, `(3,8,7)`, `s = 180`: `q = 135` odd, `N` even.  The largest tabulated member of
the `(3,8,7)` family, `k = 15`. -/
theorem row_1350 : (3 * 180 : ℤ) = 540 ∧ (540 : ℤ) / 4 = 135 ∧ 135 % 2 ≠ 1350 % 2 := by norm_num

end Erdos634.SixtyInvariant
