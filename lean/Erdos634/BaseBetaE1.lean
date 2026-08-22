import Mathlib.Tactic
import Mathlib.NumberTheory.Niven

/-!
Pillars of the base-`β` `e=1` no-go theorem (Erdős #634, the `3α+2β=π` branch), machine-checked.

For the primitive `3α+2β=π` tile `(a,b,c) = (ef, f²−e², f²)` (`1 ≤ e < f`, `gcd(e,f)=1`) the law of
cosines gives `cos α = (2f²−e²)/(2f²)`, hence `sin(α/2) = e/(2f)` exactly.

* `tile_alpha_irrational` — **the Laczkovich citation is not needed**: since `0 < e/(2f) < 1/2`
  strictly, Niven's theorem (Mathlib) forces `α` to be an irrational multiple of `π`, for *every*
  valid `(e,f)`.  This is the hypothesis the whole sporadic analysis rests on, now proved from
  scratch.
* `vertex_pi`, `vertex_beta_corner`, `vertex_apex` — the vertex-figure classification.  Writing a
  vertex figure as `x·α + y·β + z·γ` and using `β = (π−3α)/2`, `γ = (π+α)/2`, irrationality of `α/π`
  forces the two integer conditions used below; the enumerations then follow by `omega`.  In
  particular each base corner of `ABC` carries **exactly one** tile (its `β`-vertex) and the apex
  carries **exactly three** (each an `α`-vertex).
* `base_composition_e1` — at `e=1, m=1` the base `Y = 3f²−1` admits, among coverings by whole tile
  edges `a=f`, `b=f²−1`, `c=f²` with at least two `c`-edges, the **unique** solution `{b, c, c}`.

Together with the geometric steps in the paper these give: the `e=1, m=1` base-`β` family
(`N = 3f²−1 = 11, 26, 47, 74, 107, 191, …`) admits no tiling.  Axiom-clean.
-/

namespace Erdos634.BaseBetaE1

open Real

/-- **The tile's `α` is an irrational multiple of `π` — with no citation.**  For the primitive
`3α+2β=π` tile `(ef, f²−e², f²)` one has `sin(α/2) = e/(2f)`, and `1 ≤ e < f` places this strictly
between `0` and `1/2`; Niven's theorem then rules out `α` being a rational multiple of `π`.
(Replaces the appeal to Laczkovich for this branch.) -/
theorem tile_alpha_irrational (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (α : ℝ)
    (hsin : Real.sin (α / 2) = (e : ℝ) / (2 * (f : ℝ))) :
    ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := by
  rintro ⟨r, hr⟩
  -- α/2 is also a rational multiple of π
  have hhalf : ∃ s : ℚ, α / 2 = (s : ℝ) * Real.pi := ⟨r / 2, by rw [hr]; push_cast; ring⟩
  have hrat : ∃ q : ℚ, Real.sin (α / 2) = (q : ℝ) :=
    ⟨(e : ℚ) / (2 * (f : ℚ)), by rw [hsin]; push_cast; ring⟩
  have hmem := niven_sin hhalf hrat
  rw [hsin] at hmem
  -- but 0 < e/(2f) < 1/2 strictly
  have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le he (le_of_lt hef)
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hpos : 0 < (e : ℝ) / (2 * (f : ℝ)) := by positivity
  have hlt : (e : ℝ) / (2 * (f : ℝ)) < 1 / 2 := by
    have hef' : (e : ℝ) < (f : ℝ) := by exact_mod_cast hef
    have h2f : (0 : ℝ) < 2 * (f : ℝ) := by positivity
    have key : (e : ℝ) / (2 * (f : ℝ)) * (2 * (f : ℝ)) = (e : ℝ) :=
      div_mul_cancel₀ _ (ne_of_gt h2f)
    nlinarith [key, hef', h2f]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  · rw [h] at hpos; linarith
  · rw [h] at hpos; linarith
  · rw [h] at hpos; linarith
  · rw [h] at hlt; linarith
  · rw [h] at hlt; linarith

/-- Vertex figure summing to `π` (a boundary node or T-junction): with `y+z = 2` and `2x+z = 3y`
(the two integer conditions forced by irrationality of `α/π`), the only types are `{3α,2β}` and
`{α,β,γ}`. -/
theorem vertex_pi (x y z : ℕ) (h1 : y + z = 2) (h2 : 2 * x + z = 3 * y) :
    (x = 3 ∧ y = 2 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1) := by omega

/-- A corner of `ABC` of angle `β` is covered by **exactly one** tile, with its `β`-vertex there. -/
theorem vertex_beta_corner (x y z : ℕ) (h1 : y + z = 1) (h2 : 2 * x + z + 3 = 3 * y) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega

/-- The apex of `ABC` (angle `π − 2β = 3α`) is covered by **exactly three** tiles, each with its
`α`-vertex there. -/
theorem vertex_apex (x y z : ℕ) (h1 : y + z = 0) (h2 : 2 * x + z = 3 * y + 6) :
    x = 3 ∧ y = 0 ∧ z = 0 := by omega

/-- Base composition at `e = 1, m = 1`.  The base `Y = 3f²−1` is partitioned into whole tile edges
`a = f`, `b = f²−1`, `c = f²`; if it carries at least two `c`-edges then the multiset is exactly
`{b, c, c}`.  Subtraction-free: `B` denotes `f²−1` via `B + 1 = f²`. -/
theorem base_composition_e1 (f P Q R B : ℕ) (hf : 2 ≤ f) (hR : 2 ≤ R)
    (hB : B + 1 = f ^ 2)
    (h : P * f + Q * B + R * f ^ 2 + 1 = 3 * f ^ 2) :
    P = 0 ∧ Q = 1 ∧ R = 2 := by
  have hf2 : 4 ≤ f ^ 2 := by nlinarith [hf]
  -- R = 2 : R ≥ 3 already overshoots
  have hR2 : R = 2 := by
    by_contra hne
    have hR3 : 3 ≤ R := by omega
    have : 3 * f ^ 2 ≤ R * f ^ 2 := Nat.mul_le_mul_right _ hR3
    omega
  subst hR2
  -- P·f + Q·B = B
  have hkey : P * f + Q * B = B := by omega
  -- Q ≤ 1 : Q ≥ 2 overshoots since B ≥ 3
  have hQ2 : Q ≤ 1 := by
    by_contra hne
    have hQ : 2 ≤ Q := by omega
    have : 2 * B ≤ Q * B := Nat.mul_le_mul_right _ hQ
    omega
  -- Q = 0 would give f ∣ 1
  have hQ1 : Q = 1 := by
    rcases Nat.eq_zero_or_pos Q with h0 | h1
    · exfalso
      subst h0
      simp only [Nat.zero_mul, Nat.add_zero] at hkey
      -- P * f = B and B + 1 = f^2 = f * f
      have hff : P * f + 1 = f * f := by rw [pow_two] at hB; omega
      have hd1 : f ∣ P * f := dvd_mul_left f P
      have hd2 : f ∣ P * f + 1 := by rw [hff]; exact dvd_mul_right f f
      have hone : f ∣ 1 := (Nat.dvd_add_right hd1).mp hd2
      have := Nat.le_of_dvd one_pos hone
      omega
    · omega
  subst hQ1
  have hPf : P * f = 0 := by omega
  rcases Nat.mul_eq_zero.mp hPf with h | h
  · exact ⟨h, rfl, rfl⟩
  · omega


/-- **The direction group is free** (times `ℤ/2`) — the foundation of the colouring theorem, with no
citation.  If `α/π` is irrational then `n·(α/2 + π/2) = k·π` forces `n = 0`.  Equivalently
`η := exp(i(α/2+π/2))` is not a root of unity (`η^n = ±1 ⟹ n = 0`), so `⟨η,−1⟩ ≅ ℤ × ℤ/2` and the
sign character `χ₂(±η^n) := ±(−1)^n` is **well defined**.  That is exactly what makes the coloring
number `M = Σ_t χ₂(d_t)` a well-defined integer — i.e. Beeson's coloring theorem, which the
`3α+2β=π` tiling equations (and hence the triquadratic and four-component necessary sides) rest on.
Combined with `tile_alpha_irrational`, the colouring exists for **every** tile of the family, with no
appeal to the literature. -/
theorem direction_free (α : ℝ) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (n k : ℤ) (hn : n ≠ 0) :
    (n : ℝ) * (α / 2 + Real.pi / 2) ≠ (k : ℝ) * Real.pi := by
  intro h
  apply hirr
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  -- n·α = (2k − n)·π
  have key : (n : ℝ) * α = (2 * (k : ℝ) - (n : ℝ)) * Real.pi := by linarith
  refine ⟨((2 * k - n : ℤ) : ℚ) / ((n : ℤ) : ℚ), ?_⟩
  push_cast
  field_simp
  linarith [key]

/-- Packaged form: for the primitive `3α+2β=π` tile `(ef, f²−e², f²)` the sign character on edge
directions is well defined — no rational-multiple collision can occur.  (Niven ⟹ irrational ⟹ free.) -/
theorem colouring_well_defined (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (α : ℝ)
    (hsin : Real.sin (α / 2) = (e : ℝ) / (2 * (f : ℝ))) (n k : ℤ) (hn : n ≠ 0) :
    (n : ℝ) * (α / 2 + Real.pi / 2) ≠ (k : ℝ) * Real.pi :=
  direction_free α (tile_alpha_irrational e f he hef α hsin) n k hn

end Erdos634.BaseBetaE1

#print axioms Erdos634.BaseBetaE1.tile_alpha_irrational
#print axioms Erdos634.BaseBetaE1.vertex_pi
#print axioms Erdos634.BaseBetaE1.vertex_beta_corner
#print axioms Erdos634.BaseBetaE1.vertex_apex
#print axioms Erdos634.BaseBetaE1.base_composition_e1
#print axioms Erdos634.BaseBetaE1.direction_free
#print axioms Erdos634.BaseBetaE1.colouring_well_defined
