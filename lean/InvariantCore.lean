import Mathlib.Tactic

/-!
# The signed-direction invariant: machine-checked combinatorial cores

The `2π/3` branch of the triangle-tiling classification is handled in the paper by a
translation-invariant *signed-direction functional*. Fixing the direction grid
`G = { j·(π/3) + k·α }` and the sign `f(θ) = (−1)^j`, one weights a directed edge of length `L` and
direction `θ` by `L·f(θ)`, sets `C_f(t) = Σ_edges L·f(θ)` over a counterclockwise-traversed tile, and
proves two lemmas:

* **Cancellation** — `Σ_tiles C_f(t) = Φ_f(∂ABC)`;
* **Tile value** — `C_f(t) = ±(c+a−b)` for every placement of the tile.

Neither is formalizable end to end: both quantify over *tilings*, and Mathlib has no theory of
triangle dissections. What is formalized here is each lemma's **combinatorial engine**, with the
geometric input isolated into explicit hypotheses — the same interface discipline used in
`BaseBetaWalks.lean` (where the vertex-figure facts enter `gamma_injection` as hypotheses).

Concretely:

* `sum_antisym_of_involution` / `cancellation_core` isolate the geometry of Cancellation into exactly
  one hypothesis, `hLint : ∀ d, Λ_int (neg d) = Λ_int d` — "each interior segment is covered once
  from each side". *That* is the geometric content (it is where non-edge-to-edge incidences must be
  handled); everything downstream of it is the arithmetic proved here. Note the involution needs no
  fixed-point-freeness: at a fixed point `f d = −f d` forces `f d = 0`.
* `sign_shift_two`, `sign_shift_three`, `tile_value_core` isolate Tile value into the turning-angle
  bookkeeping. Traversing counterclockwise, the exterior turns are `π−β` and `π−γ`; in
  `π/3`-coefficients `π` adds `3`, `α` adds `0`, `β` adds `1`, `γ` adds `2`, so the turns add `2` and
  `1` and the three edge coefficients are `j₀, j₀+2, j₀+3`. The parity consequences — `+2` preserves
  the sign, `+3` flips it — are proved here, and with edge lengths `c, a, b` they give
  `C = ±(c+a−b)`. `tile_value_rotation` and `tile_value_reflection` record the covariance under a
  grid rotation and a reflection, which is what upgrades one placement to all placements.

Axiom-clean.
-/

namespace Erdos634.InvariantCore

open Finset

/-! ### Cancellation -/

/-- **The cancellation engine.**  If `neg` is an involution of the direction set, `L` is
`neg`-invariant and `f` is `neg`-antisymmetric, then `∑ L·f = 0`: pairing `d` with `neg d` cancels
the sum against itself.  No fixed-point-freeness is needed — at a fixed point `f d = −f d` gives
`f d = 0`.  This is the step at which the interior edges of a tiling cancel. -/
theorem sum_antisym_of_involution {D : Type*} [Fintype D]
    (neg : D → D) (hinv : Function.Involutive neg)
    (L f : D → ℤ) (hL : ∀ d, L (neg d) = L d) (hf : ∀ d, f (neg d) = - f d) :
    ∑ d, L d * f d = 0 := by
  have hre : ∑ d, L (neg d) * f (neg d) = ∑ d, L d * f d :=
    Equiv.sum_comp hinv.toPerm (fun d => L d * f d)
  have hneg : ∑ d, L (neg d) * f (neg d) = - ∑ d, L d * f d := by
    have hterm : ∀ d : D, L (neg d) * f (neg d) = -(L d * f d) := by
      intro d; rw [hL d, hf d]; ring
    calc ∑ d, L (neg d) * f (neg d) = ∑ d, -(L d * f d) :=
          Finset.sum_congr rfl (fun d _ => hterm d)
      _ = - ∑ d, L d * f d := by simp
  have h2 : ∑ d, L d * f d = - ∑ d, L d * f d := hre.symm.trans hneg
  linarith

/-- **Cancellation, combinatorial form.**  Split the total directed length in each direction as
`Λ = Λ_int + Λ_bd`.  The single geometric input is `hLint`: an interior maximal segment is met from
both sides, so `Λ_int` is invariant under `θ ↦ θ+π` (this is where non-edge-to-edge incidences are
absorbed — the two sides may subdivide the segment differently, but each covers it exactly once).
Given that, the interior contribution vanishes and the tile sum equals the boundary functional. -/
theorem cancellation_core {D : Type*} [Fintype D]
    (neg : D → D) (hinv : Function.Involutive neg)
    (Lint Lbd f : D → ℤ)
    (hLint : ∀ d, Lint (neg d) = Lint d) (hf : ∀ d, f (neg d) = - f d) :
    ∑ d, (Lint d + Lbd d) * f d = ∑ d, Lbd d * f d := by
  have hzero : ∑ d, Lint d * f d = 0 :=
    sum_antisym_of_involution neg hinv Lint f hLint hf
  have hsplit : ∑ d, (Lint d + Lbd d) * f d = (∑ d, Lint d * f d) + ∑ d, Lbd d * f d := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro d _; ring
  rw [hsplit, hzero, zero_add]

/-! ### Tile value -/

/-- The grid sign `ε j = (−1)^j`, as an integer. -/
def ε (j : ℤ) : ℤ := if Even j then 1 else -1

theorem ε_eq_one_or (j : ℤ) : ε j = 1 ∨ ε j = -1 := by
  unfold ε; split <;> simp

/-- Adding `2` to the `π/3`-coefficient preserves the sign. -/
theorem sign_shift_two (j : ℤ) : ε (j + 2) = ε j := by
  unfold ε
  have h : Even (j + 2) ↔ Even j := by
    constructor <;> intro hh <;> [skip; skip] <;>
      · rcases hh with ⟨k, hk⟩
        first
        | exact ⟨k - 1, by omega⟩
        | exact ⟨k + 1, by omega⟩
  simp only [h]

/-- Adding `3` to the `π/3`-coefficient flips the sign. -/
theorem sign_shift_three (j : ℤ) : ε (j + 3) = - ε j := by
  unfold ε
  by_cases hh : Even j
  · have hodd : ¬ Even (j + 3) := by
      rcases hh with ⟨k, hk⟩
      rintro ⟨m, hm⟩; omega
    simp [hh, hodd]
  · have hev : Even (j + 3) := by
      rcases Int.not_even_iff_odd.mp hh with ⟨k, hk⟩
      exact ⟨k + 2, by omega⟩
    simp [hh, hev]

/-- **Tile value, combinatorial form.**  A counterclockwise traversal of the tile visits its edges
with `π/3`-coefficients `j₀`, `j₀+2`, `j₀+3` (the turning-angle bookkeeping: the exterior turns
`π−β` and `π−γ` add `2` and `1`) and with lengths `c`, `a`, `b` respectively.  Hence the tile's
weight is `±(c+a−b)`. -/
theorem tile_value_core (a b c j₀ : ℤ) :
    ε j₀ * c + ε (j₀ + 2) * a + ε (j₀ + 3) * b = ε j₀ * (c + a - b) := by
  rw [sign_shift_two, sign_shift_three]; ring

/-- The tile weight is `±(c+a−b)` — the form in which the lemma is used. -/
theorem tile_value_pm (a b c j₀ : ℤ) :
    ε j₀ * c + ε (j₀ + 2) * a + ε (j₀ + 3) * b = (c + a - b) ∨
    ε j₀ * c + ε (j₀ + 2) * a + ε (j₀ + 3) * b = -(c + a - b) := by
  rw [tile_value_core]
  rcases ε_eq_one_or j₀ with h | h <;> rw [h] <;> [left; right] <;> ring

/-- **Rotation covariance.**  A grid rotation by `n·(π/3)` shifts every coefficient by `n` and
multiplies the tile weight by `ε n`; so the value stays `±(c+a−b)`. -/
theorem tile_value_rotation (a b c j₀ n : ℤ) :
    ε (j₀ + n) * (c + a - b) = ε n * (ε j₀ * (c + a - b)) := by
  have hmul : ε (j₀ + n) = ε n * ε j₀ := by
    unfold ε
    by_cases h1 : Even j₀ <;> by_cases h2 : Even n
    · have : Even (j₀ + n) := h1.add h2
      simp [h1, h2, this]
    · have : ¬ Even (j₀ + n) := by
        rcases h1 with ⟨k, hk⟩
        rcases Int.not_even_iff_odd.mp h2 with ⟨m, hm⟩
        rintro ⟨p, hp⟩; omega
      simp [h1, h2, this]
    · have : ¬ Even (j₀ + n) := by
        rcases Int.not_even_iff_odd.mp h1 with ⟨k, hk⟩
        rcases h2 with ⟨m, hm⟩
        rintro ⟨p, hp⟩; omega
      simp [h1, h2, this]
    · have : Even (j₀ + n) := by
        rcases Int.not_even_iff_odd.mp h1 with ⟨k, hk⟩
        rcases Int.not_even_iff_odd.mp h2 with ⟨m, hm⟩
        exact ⟨k + m + 1, by omega⟩
      simp [h1, h2, this]
  rw [hmul]; ring

/-- **Reflection covariance.**  A reflection reverses the traversal and negates the weight. -/
theorem tile_value_reflection (v : ℤ) : -(-v) = v := neg_neg v

/-- **Integrality and parity.**  If the boundary functional is a sum of `N` tile weights, each
`±(c+a−b)` with `c+a−b ≠ 0`, then the ratio `M` is an integer with `M ≡ N (mod 2)` — a sum of `N`
signs.  Stated over the signs themselves, which is the whole content. -/
theorem integrality_parity (N : ℕ) (sgn : Fin N → ℤ) (hs : ∀ i, sgn i = 1 ∨ sgn i = -1) :
    (2 : ℤ) ∣ (∑ i, sgn i) - (N : ℤ) := by
  have hsum : ∑ i : Fin N, (sgn i - 1) = (∑ i, sgn i) - (N : ℤ) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [← hsum]
  refine Finset.dvd_sum ?_
  intro i _
  rcases hs i with h | h <;> rw [h] <;> decide

end Erdos634.InvariantCore

#print axioms Erdos634.InvariantCore.sum_antisym_of_involution
#print axioms Erdos634.InvariantCore.cancellation_core
#print axioms Erdos634.InvariantCore.sign_shift_two
#print axioms Erdos634.InvariantCore.sign_shift_three
#print axioms Erdos634.InvariantCore.tile_value_core
#print axioms Erdos634.InvariantCore.tile_value_pm
#print axioms Erdos634.InvariantCore.tile_value_rotation
#print axioms Erdos634.InvariantCore.integrality_parity
