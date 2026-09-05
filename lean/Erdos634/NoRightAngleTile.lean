import Erdos634.WindowNoGeneralTheory

/-!
# The base-β tile is never right-angled — which blocks the pinwheel mechanism

Erdős #634, crux `window`.  `WindowNoGeneralTheory` records that no *general* window bound exists
(the pinwheel grows like `Θ(log N)`).  The obvious worry is whether the base-β family itself admits
the same mechanism.  A room seat identified exactly what would be needed and showed the family lacks
it, via a literature theorem plus one clean arithmetic fact.

**The mechanism** behind unbounded windows is *non-quadratic self-similarity with irrational relative
rotation*: a triangle `ABC` dissected into `N` copies of a tile similar to `ABC`, with `N` not a
perfect square.  Snover–Waiveris–Williams, *Rep-tiling for triangles*, Discrete Math. **91** (1991)
193–200 (quoted as Thm 2.1 in Beeson, arXiv:1206.2231): **if `ABC` is `N`-tiled by a tile similar to
`ABC` and `N` is not a square, then both are right triangles** — either `N = 3k²` with a 30-60-90
tile, or `N = e²+f²` with the right angle split.

**And the base-β tile is never right-angled.**  Its three cosines are
`cos α = (2f²−e²)/(2f²)`, `cos β = e(3f²−e²)/(2f³)`, `cos γ = −e/(2f)`, which vanish only at
`e² = 2f²`, `e² = 3f²` (or `e = 0`), and `e = 0` respectively — all impossible for integers with
`1 ≤ e < f`, the first two because `√2` and `√3` are irrational.

> **So the base-β tile admits no non-quadratic self-similar dissection, and the pinwheel mechanism
> in its non-square form is unavailable to this family.**  [PROVED, conditional on SWW as cited —
> the seat could not open the primary source and read it through a secondary quotation, so the
> citation should be checked directly before this is leaned on.]

Consistent with the corpus: the two rep-tile certificates `infl13` (`(1,3)`, `N = 9 = f²`) and
`infl37` (`(3,7)`, `N = 49 = f²`) both have the **minimum possible** window `[0,3]`, and the
`f²`-fold subdivision introduces no rotation at all.

**The gap that remains, named.**  SWW constrains only *non-square* `N`.  Beeson states explicitly
that not every `m²`-tiling is a quadratic tiling.  So the live question is: **does the base-β tile
admit a non-quadratic `f²`-tiling with nonzero relative label shift?**  For `(1,2)`: dissect
`(6,9,12)` into 9 copies of `(2,3,4)` and read the window.  Finite, bounded, and the most decisive
experiment currently nameable.  Not run.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.NoRightAngleTile

/-- **`cos α ≠ 0`**: it vanishes only at `e² = 2f²`, impossible over `ℤ` for `0 < e`. -/
theorem cos_alpha_ne_zero {e f : ℤ} (he : 0 < e) (hef : e < f) : 2 * f ^ 2 - e ^ 2 ≠ 0 := by
  intro h
  have h2 : e ^ 2 = 2 * f ^ 2 := by linarith
  nlinarith [h2, sq_nonneg (e - f), sq_nonneg (e + f)]

/-- **`cos γ ≠ 0`**: it vanishes only at `e = 0`. -/
theorem cos_gamma_ne_zero {e : ℤ} (he : 0 < e) : -e ≠ 0 := by omega

/-- **`cos β ≠ 0`**: it vanishes only at `e = 0` or `e² = 3f²`, both impossible. -/
theorem cos_beta_ne_zero {e f : ℤ} (he : 0 < e) (hef : e < f) : e * (3 * f ^ 2 - e ^ 2) ≠ 0 := by
  intro h
  rcases mul_eq_zero.mp h with h1 | h1
  · omega
  · nlinarith [h1]

/-- **The tile is never right-angled**, all three cosines nonzero simultaneously. -/
theorem tile_never_right {e f : ℤ} (he : 0 < e) (hef : e < f) :
    2 * f ^ 2 - e ^ 2 ≠ 0 ∧ e * (3 * f ^ 2 - e ^ 2) ≠ 0 ∧ -e ≠ 0 :=
  ⟨cos_alpha_ne_zero he hef, cos_beta_ne_zero he hef, cos_gamma_ne_zero he⟩

end Erdos634.NoRightAngleTile
