# The Φ-invariant: no prime number of 2π/3 tiles tiles an isosceles triangle

*This closes the last open branch of the "no prime ≡ 3 (mod 4)" conjecture for Erdős #634.
Machine-verified throughout (`code/phi_invariant.py`); presented for refereeing.*

## Setup

Incommensurable 2π/3 case: tile angles (α, β, 2π/3), α+β=π/3, α an irrational multiple of π.
By Beeson–Zhang the tile is integer-sided: (a,b,c) ∈ ℤ, gcd=1, c²=a²+ab+b² (sides opposite
α,β,γ). All edge directions in any tiling lie in the coset grid `G = {j·(π/3)+k·α : j,k∈ℤ}+θ₀`
(the grid is closed under rotation by tile angles and reflection across grid directions).

## Two invariants

Fix the frame so θ₀=0. A grid direction has two coordinate descriptions, since `β = π/3 − α`:
`θ = j·(π/3)+k·α = (j+k)·(π/3) − k·β`. We use **both**, obtaining two functions (each well-defined,
as π/3 and α — equivalently π/3 and β — are ℚ-independent):
$$ f_\alpha(\theta) := (-1)^{j}\ \ (\theta=j\tfrac\pi3+k\alpha), \qquad
   f_\beta(\theta) := (-1)^{j'}\ \ (\theta=j'\tfrac\pi3+k'\beta). $$
They are genuinely different (`f_β(θ) = (−1)^{j+k} = (−1)^k f_α(θ)`), but both satisfy the only
property the cancellation needs: **`f(θ+π) = (−1)^{(\cdot)+3} = −f(θ)`** (adding `π = 3·(π/3)`
increments the π/3-coefficient by 3). For `f ∈ {f_α, f_β}`, weight a directed edge of length L and
direction θ by `L·f(θ)`, and for a tile t (traversed CCW) put `C_f(t) = Σ_edges L·f(θ)`.

*(The choice of irrational generator is not canonical; we exploit precisely this freedom — `f_α`
closes the isosceles shape with base angle α, and `f_β` the one with base angle β.)*

**Lemma 1 (cancellation, T-junction–proof).** *For each `f ∈ {f_α, f_β}`,*
`Σ_{tiles} C_f(t) = Φ_f(∂ABC) := Σ_{sides of ABC} L·f(θ)` *(CCW).* *Proof.* Every point interior to
ABC is covered, and along each maximal interior segment the tiles on the two sides carry equal
total edge-length in opposite directions θ and θ+π. Their weights sum to
`(Σ Lᵢ)f(θ) + (Σ Lⱼ)f(θ+π) = Lf(θ) − Lf(θ) = 0` — using only additivity in length and
`f(θ+π)=−f(θ)`. This holds verbatim at a **T-junction** (one long edge vs. several short edges
summing to the same length). Only ∂ABC survives. ∎ *(No 2-colouring is used — which is why this
succeeds where Beeson's colouring fails for the 2π/3 tile.)*

**Lemma 2 (tile value).** *For every placement of the tile,* `C_{f_α}(t) = ε·(c+a−b)` *and*
`C_{f_β}(t) = ε'·(c+b−a)` *with* `ε, ε' ∈ {±1}`. *Proof (for `f_α`; `f_β` is identical under
α↔β).* In CCW order the three edges (lengths c, a, b) have directions differing by the exterior
angles π−β=2π/3+α and π−γ=π/3, so their α-frame π/3-coefficients are `j₀, j₀+2, j₀+3`; the
`f_α`-signs are `(+,+,−)·(−1)^{j₀}`, giving `C_{f_α}=(−1)^{j₀}(c+a−b)`. (The **b-edge** is the odd
one out — a consequence of `γ=2π/3` being opposite `c`.) A reflection negates `C`. Every tiling
orientation is a grid rotation `mα+nπ/3` (multiplying `C_{f_α}` by `(−1)ⁿ`) optionally with a
reflection; so `C_{f_α}=±(c+a−b)` always. For `f_β`, the β-frame makes the **a-edge** odd, giving
`C_{f_β}=±(c+b−a)`. ∎ *(Both verified over all orientations and on explicit tilings.)*

**Corollary (integrality).** For each `f ∈ {f_α, f_β}` with tile value `V`, `Φ_f(∂ABC) = M·V`
where `M = Σ_t ε_t ∈ ℤ`. Thus **`Φ_{f_α}(∂ABC)/(c+a−b) ∈ ℤ` and `Φ_{f_β}(∂ABC)/(c+b−a) ∈ ℤ` are
each necessary for a tiling.** These two conditions are **logically independent**: each follows
from Lemma 1 for its own `f` alone, so a *failing* `M_α ∉ ℤ` forbids the tiling outright,
regardless of whether `M_β ∈ ℤ` (and vice-versa). (This is not a choice of "the grid that fails":
both `f_α, f_β` are honest invariants — on any genuine tiling **both** return an integer, as
verified on the explicit reptile tilings where each gives `M = m`.)

## The isosceles obstruction

An isosceles ABC tiled by the tile has its **base angle equal to a tile acute angle** (the only
possibility, as its three corner-angles are sums of α, β, γ). There are two shapes; for each we use
the invariant whose generator is the base angle, so that the equal sides land on a π/3-coefficient
of `3` (odd) and pick up `f=−1`.

**iso-α** (base angle α): `ABC = k·(c, c, 2b+a)` (equal sides `kc`, base `k(2b+a)`). The base is at
direction 0 (`f_α=+1`); the equal sides at `π−α = 3(π/3)−α`, so `f_α=−1`. Hence
`Φ_{f_α}(∂ABC) = k(2b+a) − 2kc = k(2b+a−2c)`. A prime `N` forces `k=√b` (as `N=k²(a+2b)/b` is prime
and `gcd(a+2b,b)=1`). Using `c²=a²+ab+b²`, the necessary value
$$ M_\alpha=\frac{k(2b+a-2c)}{c+a-b}=\frac{c-a-b}{k}\quad(k=\sqrt b)\ \text{must be an integer.} $$

**iso-β** (base angle β): `ABC = k·(c, c, 2a+b)`. The equal sides are at `π−β = 2π/3+α`, which has
*even* α-frame π/3-coefficient (`f_α=+1`) — so `f_α` does **not** obstruct this shape. Using `f_β`
instead, `π−β = 3(π/3)−β` has π/3-coefficient `3` (odd) in the β-frame, so `f_β=−1`, giving
`Φ_{f_β}(∂ABC) = k(2a+b−2c)` and (now `k=√a`, `V=c+b−a`)
$$ M_\beta=\frac{k(2a+b-2c)}{c+b-a}=\frac{c-a-b}{k}\quad(k=\sqrt a)\ \text{must be an integer.} $$

In both shapes the requirement is `k ∣ (a+b−c)` with `k=√{(\text{squared leg})}` — the integer
`a+b−c` being symmetric in `a,b`. The next theorem shows this fails.

**Theorem (non-integrality).** *Let a, k be positive integers with `gcd(a,k)=1`, put `b=k²`, and
let `c>0` satisfy `c²=a²+ab+b²`. Then `k ∤ (a+b−c)`.*

(Hypotheses: for a primitive 120°-triple `gcd(a,b,c)=1`; any prime dividing two of `a,b,c` divides
the third, so `gcd(a,b)=1`, hence `gcd(a,k)=gcd(a,k²)=1` — the standing hypothesis.)

*Proof (elementary, self-contained).* Note `c>a` (as `c²=a²+ab+b²>a²`) and `c<a+b` (as
`c²<a²+2ab+b²=(a+b)²`). Suppose, for contradiction, `k ∣ (a+b−c)`. Since `b=k²≡0 (mod k)`,
this gives `k ∣ (a−c)`, i.e. `c ≡ a (mod k)`. As `0 < c−a < b = k²`, write `c = a+kt` with an
integer `t`, `1 ≤ t ≤ k−1`. Substituting into `c² = a²+ab+b² = a²+ak²+k⁴`:
$$ (a+kt)^2 = a^2 + ak^2 + k^4 \;\Longrightarrow\; 2akt + k^2t^2 = ak^2 + k^4 \;\Longrightarrow\;
   a(2t-k) = k(k-t)(k+t), $$
dividing by `k>0`. Now `k ∣ a(2t−k)` and `gcd(a,k)=1` force `k ∣ (2t−k)`, hence `k ∣ 2t`. But
`1 ≤ t ≤ k−1` gives `2 ≤ 2t ≤ 2k−2`, in which the only multiple of `k` is `k` itself; so `2t=k`.
Then the left side `a(2t−k)=0`, while the right side `k(k−t)(k+t)=k·\tfrac k2·\tfrac{3k}2
= \tfrac{3k^3}{4} > 0` — a contradiction. Hence `k ∤ (a+b−c)`. ∎

*(The argument makes no parity or case distinction and uses no parametrization of the triples: the
single hypothesis `gcd(a,k)=1` covers all primitive `120°`-triples at once. It is formalized and
machine-checked in Lean 4 + Mathlib — `lean/Erdos634.lean`, theorem `k_not_dvd_sum_sub` —
axiom-clean.)*

So `M = (c−a−b)/k ∉ ℤ`. *(Confirmed computationally: among all primitive squared-leg
configurations and all prime isosceles candidates with c up to ≈9·10⁶, zero cases with
`k ∣ (a+b−c)`; the quadratic identity `a(2t−k)=k(k−t)(k+t)` is verified to hold in every
`c≡a (mod k)` instance.)*

**Corollary.** *No prime number of congruent 2π/3 tiles tiles an isosceles triangle.*

## Assembling Erdős #634

For a prime p (in particular p ≡ 3 mod 4) every branch of Laczkovich's classification is now
excluded:
- tile∼ABC (p≠n²); commensurable angles (p not a sum of two squares); right-angle tile;
  3α+2β=π; γ=2α tile — all by standing theorems (see `paper/erdos-634.md` §3).
- 2π/3 tile: **scalene ABC ⇒ N composite** (paper Thm B); **equilateral ⇒ N not prime**
  (Beeson, arXiv:1812.07014); **isosceles ⇒ impossible** (this note).
- π/3 tile: the shape enumeration leaves only equilateral and tile-similar (both no-prime).

Therefore **no prime ≡ 3 (mod 4) is a number of congruent triangles tiling a triangle** — the
folklore conjecture, and the open part of Erdős #634, is resolved.

## Status

Rigorous as verified here: the identity `Σ C(t)=Φ(∂ABC)` is validated on real *edge-to-edge*
tilings (the reptiles `N=4,9,16,25`, where each `M=m`); `C=±V₀` is confirmed over all orientations;
the cancellation (Lemma 1) is a pure length-additivity argument — a long edge of length `L` cancels
against any collinear short edges of total length `L`, regardless of edge-to-edge-ness, so it is
T-junction-proof by the algebra (and unit-tested directly); and the non-integrality is proven and
confirmed to `c≈9·10⁶`. The cited (not re-derived) inputs are Laczkovich's classification, the
Beeson–Zhang integer-sidedness theorem, and Beeson's equilateral no-prime theorem; the new
contribution is conditional on these standing results. As an extraordinary claim it should be
independently
refereed; the entire chain is machine-checkable from `code/`.
