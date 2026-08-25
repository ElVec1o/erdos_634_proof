import Mathlib.Tactic

/-!
# The corner wall: arithmetic cores of the straddle constraints

Erdős #634, base-`β` branch.  Hypothesis (walls) asks that a corner block be **complete** — that no
tile crosses the block's inner wall.  This file holds the arithmetic engines of five constraints on
a hypothetical straddle, with the geometric input isolated into hypotheses, the interface discipline
of `LambdaFactor.lean` and `InvariantCore.lean`.

Setting: the tile is `(a,b,c) = (ef, f²−e², f²)`; the east wall has length `e·b`, the west `f·b`.

* `residue_mod_f`, `residue_mod_e` — the two residue lemmas on a straight edge-union.  The first is
  the engine of the sieve; the second is its companion, non-degenerate exactly where the first
  collapses.
* `no_single_straddler` — area quantization: one straddler is impossible.
* `chain_bound_*` — straddlers group into chains, and chains are boundedly many.
* `multiplier_closure` — the count identity behind "`m` realizable ⟹ `mk` realizable".
* `Q3_eq_neg_b` — the cut-fraction recursion's third term.

Axiom-clean.
-/

namespace Erdos634.WallStraddle

/-! ## The two residue lemmas

A straight segment of length `L` inside the tiling, covered by tile edges, satisfies
`L = n_a·a + n_b·b + n_c·c`.  Reducing mod `f` kills the `a` and `c` terms; reducing mod `e` kills
the `a` term and merges `b` with `c`. -/

/-- **Residue mod `f`.**  `f ∣ L + n_b·e²`, i.e. `n_b ≡ −L·e⁻² (mod f)` when `gcd(e,f)=1`. -/
theorem residue_mod_f (na nb nc e f L : ℤ)
    (h : L = na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2) :
    f ∣ (L + nb * e ^ 2) :=
  ⟨na * e + nb * f + nc * f, by rw [h]; ring⟩

/-- **Residue mod `e`.**  `e ∣ L − (n_b + n_c)·f²`, i.e. `n_b + n_c ≡ L·f⁻² (mod e)` when
`gcd(e,f)=1`.  This is the companion the sieve needs on the **west** wall, where the mod-`f` anchor
degenerates: there `L = f·b` and `f ∣ L`, so the mod-`f` residue carries no information. -/
theorem residue_mod_e (na nb nc e f L : ℤ)
    (h : L = na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2) :
    e ∣ (L - (nb + nc) * f ^ 2) :=
  ⟨na * f - nb * e, by rw [h]; ring⟩

/-! ## Area quantization

The corner region has area exactly `k²·A` (`k = e` east, `k = f` west).  Tiles fully inside
contribute whole units of `A`; a straddler contributes strictly between `0` and `A`.  So the
straddlers' inside-areas sum to an exact integer multiple of `A`. -/

/-- **One straddler is impossible.**  With `K` the region's tile-count and `n` the number of tiles
fully inside, a single straddler would contribute `K − n` units of area with `0 < K − n < 1`. -/
theorem no_single_straddler (K n : ℤ) (h1 : 0 < K - n) (h2 : K - n < 1) : False := by omega

/-- The general form: the straddlers' inside-fraction sum `j` satisfies `1 ≤ j ≤ s − 1`, so `s ≥ 2`.
-/
theorem two_straddlers (s j : ℤ) (h1 : 1 ≤ j) (h2 : j ≤ s - 1) : 2 ≤ s := by omega

/-! ## Chains

Traversing the wall, it alternately runs **along** tile edges (a *gap*) and **through** tile
interiors (a *chain*).  A straight segment can leave an edge it coincides with only at that edge's
endpoint, so every chain begins and ends at a tiling vertex.  Consecutive chains are separated by a
gap of positive length, and every gap is an edge-union, hence of length at least `min(a,b)`.  With
`C` chains inside a wall of length `W` that forces `(C−1)·min(a,b) ≤ W`.

This is what makes the analysis finite: the number of *straddlers* is unbounded — chords can be
arbitrarily short near a vertex — but the number of *chains* is not. -/

/-- **The chain bound.**  If `(C−1)·m ≤ W` and `W < k·m` with `0 < m`, then `C ≤ k`. -/
theorem chain_bound (C W m k : ℤ) (hm : 0 < m) (h : (C - 1) * m ≤ W) (hk : W < k * m) :
    C ≤ k := by nlinarith

/-- At `(e,f) = (3,7)` — the member of `N = 138` — the east wall has length `e·b = 120` and
`min(a,b) = min(21,40) = 21`, so at most six chains. -/
theorem chain_bound_east_3_7 (C : ℤ) (h : (C - 1) * 21 ≤ 120) : C ≤ 6 := by omega

/-- At `(5,6)` — the member of `N = 83` — the east wall has length `55` and `min(a,b) = 11`. -/
theorem chain_bound_east_5_6 (C : ℤ) (h : (C - 1) * 11 ≤ 55) : C ≤ 6 := by omega

/-- The west wall at `(3,7)`: length `f·b = 280`, same gap floor. -/
theorem chain_bound_west_3_7 (C : ℤ) (h : (C - 1) * 21 ≤ 280) : C ≤ 14 := by omega

/-! ### A negative: the chain-endpoint condition is nearly vacuous

A chain can begin at a vertex `V` only if some edge direction at `V` has **no opposite** — the wall
arrives along an edge in direction `−ω^ℓ` and leaves in direction `+ω^ℓ`, which must therefore not be
an edge direction.  One might hope this pins chain endpoints to rare vertex types.  It does not.

Writing `π = 1` and `θ = α/2`, the angles are `α = (0,2)`, `β = (1/2,−3)`, `γ = (1/2,1)` in the basis
`(rational·π, multiple of θ)`, and a direction has an opposite iff some partial sum differs from it
by `(1,0)`.  Enumerating every cyclic arrangement of each `2π` vertex type:

    type                cyclic words   admit an endpoint
    β+3γ                        1            1  (100%)
    2α+2β+2γ                   16           14  ( 88%)
    4α+3β+γ                    35           35  (100%)
    6α+4β                      22           20  ( 91%)

The only arrangements that cannot host a chain endpoint are the two `2α+2β+2γ` and the two `6α+4β`
words whose direction set is closed under `+π` — precisely the vertices sitting in the interior of a
straight line of the tiling.  So the local condition excludes four configurations out of 74 and is
not a route to Hypothesis (walls).  Recorded so the enumeration is not repeated. -/

/-! ## The multiplier closure

The target at multiplier `m` has sides `(f³m, f³m, e·m·N₀)`; at `mk` it is that triangle scaled by
`k`, which dissects into `k²` congruent copies of it.  Tiling each copy gives a tiling of the larger
target by the *same* tile, so realizable multipliers are closed under multiplication and the
realizable set of each family is generated by its **primitive** multipliers. -/

/-- **The count identity.**  `k²` copies of an `m²N₀`-tiling assemble into an `(mk)²N₀`-tiling. -/
theorem multiplier_closure (m k N₀ : ℤ) : (m * k) ^ 2 * N₀ = k ^ 2 * (m ^ 2 * N₀) := by ring

/-- Family `(1,2)`, `N₀ = 11`: the two certified tilings `m = 2` (`N = 44`) and `m = 3` (`N = 99`)
generate `11m²` for every `m` divisible by `2` or `3`.  Sample: `176 = 4²·11` is the `m=2` tiling
scaled by two, not an independent construction. -/
theorem counts_1_2 : (4:ℤ) ^ 2 * 11 = 176 ∧ (6:ℤ) ^ 2 * 11 = 396 ∧ (9:ℤ) ^ 2 * 11 = 891 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩


/-! ### The skeleton in the certified 44-tiling: counts hold, walls do not

At `(e,f,m) = (1,2,2)` the target is `(16,16,22)` with apex `(11,3)` in the chart.  The skeleton
predicts a west block of `(fm)² = 16` tiles on the triangle `(0,0),(8,0),(11,3)`, an east block of
`(em)² = 4` on `(22,0),(14,0),(77/4,3/4)`, and a middle quadrilateral carrying `2bm² = 24`.

Classifying all 44 tiles of the `N44C` certificate by centroid gives west 16, east 4, middle 24,
none unclassified.  **The classification is by centroid only**: the exact incidence sweep
(`code/interface_census.py`) shows the wall lines are *crossed* — three tiles straddle the west
wall `(8,0)–(11,3)` and three the east wall `(14,0)–(77/4,3/4)` — so neither corner block is a
region of the tiling and the skeleton is *not* realised edge-exactly.  What the tiling does
respect is the **cevian** from the apex to `(14,0)`: no tile crosses it, its west side reads
`c·c·c` and its east side `a·a·c·c` — the interface equation `3c = 2a + 2c`, i.e. `c = 2a`,
which holds exactly on `f = 2e`.  The respected macro-structure is therefore the cevian split
(east piece = the tile at scale `fm`, west piece = the certified `CevianTiling28`), and the
earlier reading of this passage as "the skeleton is exactly realised" is withdrawn.  The middle's
24 tiles (by centroid) share 22 full edges; no perfect parallelogram matching exists. -/

/-- The `(1,2,2)` skeleton counts: `16 + 4 + 24 = 44`. -/
theorem skeleton_44 : (2*2:ℤ)^2 + (1*2)^2 + 2*3*2^2 = 44 := by norm_num

/-! ## The cut-fraction recursion

Writing `ω^k = p_k + q_k·ω` with `f·ω² + e·ω + f = 0`, the chord of a straddler forces the
`ω`-coefficient to vanish, so its two cut fractions satisfy `u/v = s₂·q_{d₂}/(s₁·q_{d₁})` — one free
parameter per straddler, not two.  Clearing denominators via `q_k = Q_k/f^{k−1}` gives
`Q_{k+1} = −e·Q_k − f²·Q_{k−1}`, `Q_0 = 0`, `Q_1 = 1`. -/

/-- `Q₃ = −b`.  The third term of the recursion is minus the tile's middle side. -/
theorem Q3_eq_neg_b (e f : ℤ) : -e * (-e) - f ^ 2 * 1 = -(f ^ 2 - e ^ 2) := by ring

/-- `Q_{k+1} ≡ −e·Q_k (mod f)`, so `Q_k ≡ (−e)^{k−1} (mod f)`; with `gcd(e,f) = 1` no `Q_k` is
divisible by `f`, hence `v_q(q_k) = −(k−1)·v_q(f)` exactly for every prime `q ∣ f`. -/
theorem Q_step_mod_f (Qk Qk1 e f : ℤ) (h : Qk1 = -e * Qk - f ^ 2 * Qk) :
    f ∣ (Qk1 + e * Qk) :=
  ⟨-(f * Qk), by rw [h]; ring⟩


/-! ## Consequence: a `b`-edge on a short wall forces a `b` opposite it

`residue_mod_f` above is stated and used for the corner wall.  Applied to **both sides of any**
straight edge-union it says more, and the consequence is the first tool here that is simultaneously
scale-sensitive (it compares against `f³`, the equal side) and boundary-aware (against `3f² - 1`,
the base).  `Crux1`'s sweep records that CRUX-1 needs exactly such a tool.

At `e = 1`: both sides of a wall of length `L` satisfy `f ∣ L + n_b`, so the two `b`-counts agree
mod `f`.  If one side carries none, the other carries a multiple of `f`, hence at least `f`, hence
the wall is at least `f·b = f³ - f` long.  But the widest chord of the target is the base, `3f² - 1`,
and `f³ - f > 3f² - 1` once `f ≥ 4`.  So on any wall short enough to fit across the target,

  **a `b`-edge on one side forces a `b`-edge on the other.**

This bites on the `c`-under-run configuration of CRUX-1: the blocking `c`-tile's `b`-edge is nearly
horizontal, so its wall is bounded by the target's width, and a `b`-edge is forced directly opposite
it.  What that forced `b` costs is not settled here.
-/


/-- **The two sides of a wall carry congruent `b`-counts.**  At `e = 1` the residue lemma
(`WallStraddle.residue_mod_f`) gives `f ∣ L + n_b` on each side of a straight edge-union of length
`L`; subtracting, the counts agree mod `f`. -/
theorem b_counts_congruent (f L n1 n2 : ℤ) (h1 : f ∣ L + n1) (h2 : f ∣ L + n2) : f ∣ (n1 - n2) := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k1 - k2, by linarith⟩

/-- **A wall with `b` on one side and none on the other is nearly as long as an equal side.**
`f ∣ n₁` with `n₁ ≥ 1` forces `n₁ ≥ f`, so the length is at least `f·b = f³ - f`. -/
theorem b_asymmetric_forces_long_wall (f L n1 : ℤ) (hf : 3 ≤ f) (hn : 1 ≤ n1)
    (hdvd : f ∣ n1) (hlen : n1 * (f ^ 2 - 1) ≤ L) : f ^ 3 - f ≤ L := by
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : 1 ≤ k := by nlinarith
  have hn1f : f ≤ n1 := by nlinarith
  have hpos : (0:ℤ) ≤ f ^ 2 - 1 := by nlinarith
  have hmul : f * (f ^ 2 - 1) ≤ n1 * (f ^ 2 - 1) := mul_le_mul_of_nonneg_right hn1f hpos
  nlinarith [hlen, hmul]

/-- **But no such wall fits across the target.**  The base is the widest chord, of length `3f² - 1`,
and `f³ - f > 3f² - 1` for `f ≥ 4`.  So a wall confined to the target's width cannot be that long,
and its `b`-counts must therefore be nonzero on **both** sides. -/
theorem long_wall_exceeds_width (f : ℤ) (hf : 4 ≤ f) : 3 * f ^ 2 - 1 < f ^ 3 - f := by nlinarith

/-- Assembled: a wall whose length is bounded by the target's width carries a `b` on both sides or
neither. -/
theorem b_on_both_sides_or_neither (f L n1 n2 : ℤ) (hf : 4 ≤ f)
    (h1 : f ∣ L + n1) (h2 : f ∣ L + n2)
    (hwidth : L ≤ 3 * f ^ 2 - 1) (hn0 : 0 ≤ n2)
    (hlen : n1 * (f ^ 2 - 1) ≤ L) (hn : 1 ≤ n1) : 1 ≤ n2 := by
  by_contra h
  push_neg at h
  have hn2 : n2 = 0 := by omega
  subst hn2
  have hdvd : f ∣ n1 := by simpa using b_counts_congruent f L n1 0 h1 h2
  have hlong := b_asymmetric_forces_long_wall f L n1 (by omega) hn hdvd hlen
  have := long_wall_exceeds_width f hf
  omega

end Erdos634.WallStraddle

#print axioms Erdos634.WallStraddle.residue_mod_f
#print axioms Erdos634.WallStraddle.residue_mod_e
#print axioms Erdos634.WallStraddle.no_single_straddler
#print axioms Erdos634.WallStraddle.chain_bound
#print axioms Erdos634.WallStraddle.multiplier_closure

namespace Erdos634.WallStraddle

/-! ## The middle region: the construction side

The two corner blocks and the region between them partition the target exactly.  The west block is
the tile at scale `f` (its `c`-side is the whole equal side, its `a`-side sits on the base), the east
block is the tile at scale `e` (`c`-side on the base, `a`-side on the equal side), and what is left
is a quadrilateral whose four sides are `f·b`, `e·b`, `e·b`, `f·b` — two of them the blocks' walls.

The tile counts add up on the nose, and the middle's count is **even** for every `(e,f)`, so the
middle is a candidate for `b` parallelograms of two tiles each.  That is the shape a general
`(e,f)` construction would take, and it is what the sufficiency question (which `N` occur) needs:
the certified `(1,2)` tilings would generalise to every family. -/

/-- **The three regions partition the count.**  `f² + e² + 2b = N₀`. -/
theorem region_count (e f : ℤ) :
    f ^ 2 + e ^ 2 + 2 * (f ^ 2 - e ^ 2) = 3 * f ^ 2 - e ^ 2 := by ring

/-- **The middle base segment is `e·b`.**  The base has length `e·N₀` and each block occupies
`e·f²` of it. -/
theorem middle_base (e f : ℤ) :
    e * (3 * f ^ 2 - e ^ 2) - 2 * (e * f ^ 2) = e * (f ^ 2 - e ^ 2) := by ring

/-- **The middle carries an even number of tiles**, hence could be `b` two-tile parallelograms. -/
theorem middle_even (e f : ℤ) : ∃ k : ℤ, 2 * (f ^ 2 - e ^ 2) = 2 * k := ⟨f ^ 2 - e ^ 2, rfl⟩

end Erdos634.WallStraddle
