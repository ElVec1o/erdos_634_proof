import Mathlib.Tactic

/-!
# Corner figures and edge unsplittability for the base-`β` target

Erdős #634, base-`β` branch.  The tile `T` satisfies `3α + 2β = π`, so writing `θ = α/2`,

    α = 2θ,    β = π/2 − 3θ,    γ = π/2 + θ,

with primitive integer sides `(a,b,c) = (ef, f² − e², f²)`, `gcd(e,f) = 1`, `1 ≤ e < f`, where `a`
is opposite `α`, `b` opposite `β`, `c` opposite `γ`.  Edge–vertex incidence: `a` joins the `β` and
`γ` corners, `b` joins `α` and `γ`, `c` joins `α` and `β`.

Since `θ/π` is irrational, an angle relation

    p·α + q·β + r·γ  =  (2p − 3q + r)·θ + (q + r)·π/2

splits into two **integer** equations.  This file solves the four that occur in the boundary
analysis, and proves that `b` is unsplittable in the edge semigroup.

## Scope of this file

Everything proved here is arithmetic.  The geometric input — that the tile angles meeting at a
point sum to `2π`, to `π`, or to the corner angle, with non-negative integer multiplicities — is
`Dissection.lean` (`vertex_multiplicities` and its corollaries).

**STATUS (corrected 2026-08-24).**  This paragraph used to end "Mathlib has no theory of planar
dissections and that step is not formalized anywhere."  That is **false as of 2026-08-16**: the
angle-sum half is proved outright by `Dissection.hasAngleSums` (`AngleSumDissection.lean`), via
the vertex-sector area computation in `VertexSector.lean`, which needs no theory of planar
dissections from Mathlib.  What follows is the arithmetic that step feeds into.

## Contents

* `corner_beta_unique` — a corner of angle `β` carries a **single tile, presenting `β`**; its two
  edges there are `a` and `c`.
* `corner_apex_unique` — a corner of angle `3α` carries **exactly three tiles, each presenting
  `α`**; their edges there are `b` and `c`.
* `pi_vertex_figures`, `pi_vertex_gamma_le_one` — a junction interior to a side is `(3,2,0)` or
  `(1,1,1)`; in particular it carries **at most one `γ`**.
* `two_pi_vertex_figures` — an interior vertex is one of `(6,4,0)`, `(4,3,1)`, `(2,2,2)`, `(0,1,3)`.
* `b_unsplittable` — `b` is not a sum of two or more tile edges.

## The two geometric consequences these were built for

Both are proved on paper from the statements below together with `Dissection.lean`; they are
*not* formalized here, because their proofs quantify over the boundary walk of a dissection.

**(γ-trap.)  Every side of the target carries at least one `c`-edge.**  Each `a`- or `b`-edge places
a `γ` at exactly one of its two endpoints (they are the two edges incident to `γ`); each interior
junction absorbs at most one `γ` (`pi_vertex_gamma_le_one`); and **no corner of the target carries
a `γ` at all** (`corner_beta_unique` gives `β` at the two base corners, `corner_apex_unique` gives
`α` at the apex).  So if a side had no `c`-edge, `E₁` could not place its `γ` at the corner `J₀`,
forcing `E₁ → J₁`; that junction is then full, forcing `E₂ → J₂`; inductively `Eₙ → Jₙ`, the far
corner — which carries no `γ`.  Contradiction.

**(Corner parallelogram.)**  The `β`-corner tile is unique (`corner_beta_unique`) and its two edges
at the corner are `a` and `c`, so its remaining vertices lie one on each of the two sides meeting
there; hence its `b`-edge is a chord with **both endpoints on the boundary**.  An edge straddling
that chord would have to extend beyond one endpoint and leave the triangle, so the chord is exactly
matched, and by `b_unsplittable` it is matched by a **single** tile.  The `γ`-cap at each end
(`pi_vertex_gamma_le_one`) then forces that tile's `α` and `γ` to be interchanged relative to the
corner tile, so their union is a parallelogram with sides `a` and `c`.  Consequently the first
*two* edges of each side at a `β`-corner lie in `{a, c}`.

Checked against both genuine certificates (the 44- and 99-tilings, exact arithmetic in `ℚ(√15)`):
the first-two-edges rule holds on 6/6 sides, and at each of the 4 base corners exactly one of the
two sides begins with a `c`-edge.

Axiom-clean.
-/

namespace Erdos634.BaseBetaCorners

/-! ### The corner and vertex figures -/

/-- **A corner of angle `β` carries exactly one tile, presenting `β`.**

`p·α + q·β + r·γ = β` splits into `2p − 3q + r = −3` and `q + r = 1`.  The case `(q,r) = (0,1)`
would need `2p = −4`, so only `(p,q,r) = (0,1,0)` survives.

Geometric consequence: the two edges of that tile at the corner are the ones incident to `β`,
namely `a` and `c` — so each of the two sides meeting at a base corner begins with an `a`- or a
`c`-edge, and (since the tile has one of each) *exactly one* of the two begins with `c`. -/
theorem corner_beta_unique (p q r : ℕ) (h1 : 2 * (p : ℤ) - 3 * q + r = -3) (h2 : q + r = 1) :
    p = 0 ∧ q = 1 ∧ r = 0 := by omega

/-- **The apex, of angle `3α`, carries exactly three tiles, each presenting `α`.**

`p·α + q·β + r·γ = 3α` splits into `2p − 3q + r = 6` and `q + r = 0`, forcing `q = r = 0`, `p = 3`.

Geometric consequence: the edges of those tiles at the apex are the ones incident to `α`, namely
`b` and `c`; in particular the apex carries no `γ`. -/
theorem corner_apex_unique (p q r : ℕ) (h1 : 2 * (p : ℤ) - 3 * q + r = 6) (h2 : q + r = 0) :
    p = 3 ∧ q = 0 ∧ r = 0 := by omega

/-- **Junctions interior to a side of the target are `(3,2,0)` or `(1,1,1)`.**

`p·α + q·β + r·γ = π` splits into `2p − 3q + r = 0` and `q + r = 2`; the case `(q,r) = (0,2)` would
need `p = −1`. -/
theorem pi_vertex_figures (p q r : ℕ) (h1 : 2 * (p : ℤ) - 3 * q + r = 0) (h2 : q + r = 2) :
    (p = 3 ∧ q = 2 ∧ r = 0) ∨ (p = 1 ∧ q = 1 ∧ r = 1) := by omega

/-- **A junction interior to a side carries at most one `γ`.**

This is the `γ`-trap proper: it is what stops two `a`- or `b`-edges from placing their `γ` at the
same junction, and hence what makes the forcing chain run. -/
theorem pi_vertex_gamma_le_one (p q r : ℕ) (h1 : 2 * (p : ℤ) - 3 * q + r = 0) (h2 : q + r = 2) :
    r ≤ 1 := by omega

/-- **Vertices interior to the target.**  `p·α + q·β + r·γ = 2π` splits into `2p − 3q + r = 0` and
`q + r = 4`, with exactly four solutions. -/
theorem two_pi_vertex_figures (p q r : ℕ) (h1 : 2 * (p : ℤ) - 3 * q + r = 0) (h2 : q + r = 4) :
    (p = 6 ∧ q = 4 ∧ r = 0) ∨ (p = 4 ∧ q = 3 ∧ r = 1) ∨ (p = 2 ∧ q = 2 ∧ r = 2)
      ∨ (p = 0 ∧ q = 1 ∧ r = 3) := by omega

/-! ### Unsplittability of the `β`-edge -/

/-- **`b` is unsplittable in the edge semigroup.**

Stated with `b` as a variable satisfying `b + e² = f²`, which avoids truncated subtraction.  If

    nₐ·(e·f) + n_b·b + n_c·f²  =  b

with all coefficients in `ℕ`, then `(nₐ, n_b, n_c) = (0, 1, 0)`.

Three steps.  `n_b = 0` is impossible: the surviving terms are both divisible by `f`, so `f ∣ b`,
hence `f ∣ e²` by `b + e² = f²`; but `gcd(e,f) = 1` forces `f = 1`, contradicting `1 ≤ e < f`.
`n_b ≥ 2` is impossible: `b > 0`, so the left side already exceeds `b`.  With `n_b = 1` the
remaining terms sum to zero, and `e·f > 0`, `f² > 0` give `nₐ = n_c = 0`.

This is what makes the corner parallelogram work: the `β`-corner tile's `b`-chord admits no
subdivision, so — its endpoints both lying on the boundary, which rules out straddling — it is
matched by exactly one tile. -/
theorem b_unsplittable (e f b na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = b) :
    na = 0 ∧ nb = 1 ∧ nc = 0 := by
  have hf2 : 2 ≤ f := by omega
  have hbpos : 0 < b := by
    have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
    omega
  -- `n_b` cannot be `0`
  have hnb0 : nb ≠ 0 := by
    intro h
    subst h
    have hdvd : f ∣ b := ⟨na * e + nc * f, by rw [← heq]; ring⟩
    have hsq : f ^ 2 = f * f := by ring
    have he2 : 1 ≤ e ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hde : f ∣ e ^ 2 := by
      obtain ⟨k, hk⟩ := hdvd
      have hfk : f * k < f * f := by omega
      have hkf : k ≤ f := le_of_lt (lt_of_mul_lt_mul_left hfk (Nat.zero_le f))
      refine ⟨f - k, ?_⟩
      have hdist : f * (f - k) + f * k = f * f := by
        rw [← Nat.mul_add]; congr 1; omega
      omega
    have hcop2 : Nat.Coprime f (e ^ 2) := Nat.Coprime.pow_right 2 hcop.symm
    have : f = 1 := Nat.Coprime.eq_one_of_dvd hcop2 hde
    omega
  -- `n_b` cannot be `≥ 2`
  have hnb1 : nb = 1 := by
    by_contra h
    have h2 : 2 ≤ nb := by omega
    have : 2 * b ≤ nb * b := Nat.mul_le_mul_right b h2
    omega
  subst hnb1
  -- the remaining terms vanish
  have hrest : na * (e * f) + nc * f ^ 2 = 0 := by omega
  have hef0 : 0 < e * f := Nat.mul_pos (by omega) (by omega)
  have hf20 : 0 < f ^ 2 := by positivity
  refine ⟨?_, rfl, ?_⟩
  · by_contra h
    have : 0 < na * (e * f) := Nat.mul_pos (by omega) hef0
    omega
  · by_contra h
    have : 0 < nc * f ^ 2 := Nat.mul_pos (by omega) hf20
    omega

end Erdos634.BaseBetaCorners

#print axioms Erdos634.BaseBetaCorners.corner_beta_unique
#print axioms Erdos634.BaseBetaCorners.corner_apex_unique
#print axioms Erdos634.BaseBetaCorners.pi_vertex_figures
#print axioms Erdos634.BaseBetaCorners.pi_vertex_gamma_le_one
#print axioms Erdos634.BaseBetaCorners.two_pi_vertex_figures
#print axioms Erdos634.BaseBetaCorners.b_unsplittable
