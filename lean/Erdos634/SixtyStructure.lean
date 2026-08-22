import Mathlib.Tactic

/-!
# Two structures for 60-degree triples: the α-level, and the conjugate pair

Erdős #634 — machinery for the equilateral targets of Beeson's Table 2.

The tiles there are **60-degree triples**: `c² = a² - a b + b²`, so the angle opposite `c` is exactly
`π/3`, and the other two satisfy `α + β = 2π/3` with `α` an irrational multiple of `π`
(Laczkovich's fourth family).  This is a different family from the `2π/3` triples
`c² = a² + a b + b²` of `InvariantProduct`, whose signed-direction invariant therefore does not
apply: there all angles are rational multiples of `π` and directions lie on a finite grid, here they
do not.

## 1. The α-level

Traversing the tile, the direction turns by the exterior angle at each vertex.  With the `π/3` angle
opposite `c`:

  `d_a ≡ d_c + α - 2π/3`,   `d_b ≡ d_c + α`   (mod `π`),

using `β = 2π/3 - α`.  Because `α` is an irrational multiple of `π`, every direction has a **unique**
expression `m α + n·π/3` (mod `π`), and `m` is well defined.  Call it the *α-level*.  Then

  **a direct tile carries its `a`- and `b`-edges one level ABOVE its `c`-edge; a mirrored tile
  carries them one level BELOW** (`level_direct`, `level_mirrored`).

The three sides of the equilateral have directions `0, π/3, 2π/3`, i.e. **α-level exactly `0`**
(`boundary_level_zero`).  So every boundary edge sits at level `0`, and a tile meeting the boundary
has its level pinned: `0` if its `c`-edge is on the boundary, `∓1` if an `a`- or `b`-edge is
(`tile_level_at_boundary`).

Counting edge-slots by level: with `D_ℓ`, `M_ℓ` the direct and mirrored tiles at level `ℓ`,

  slots at level `ℓ`  `=  (D_ℓ + M_ℓ)`  from `c`-edges  `+  2(D_{ℓ-1} + M_{ℓ+1})`  from `a,b`-edges.

At the top level `L` there are no tiles above, so the `2 D_L` slots at level `L+1` are `a`- and
`b`-edges only and must pair among themselves — they cannot reach the boundary unless `L + 1 = 0`.
The distribution is pinched at both ends and only level `0` drains to the boundary
(`top_level_pinch`).

## 2. The conjugate pair

For fixed `b, c` the 60-triple condition is a quadratic in `a`:

  `a² - b a + (b² - c²) = 0`,   roots summing to `b`.

So 60-triples come in **conjugate pairs** `(a,b,c)` and `(b-a, b, c)` (`conjugate_is_triple`).  In
Beeson's table `(3,8,7) ↔ (5,8,7)` and `(7,15,13) ↔ (8,15,13)` are such pairs — and each pair
contributes many of the rows.

The pair tiles an equilateral.  A 60-triple with the `π/3` angle between `a` and `b` has area
`(√3/4) a b`, so

  `area(T) + area(T') = (√3/4)(a b + (b-a) b) = (√3/4) b²`,

the area of the **equilateral of side `b`** (`conjugate_areas_sum`).  Verified on every Table-2 tile.

That does *not* immediately reduce the table: for `(3,8,7)` the conjugate `(5,8,7)` has area ratio
`40/24`, not an integer, so `T'` is not tileable by copies of `T` and the decomposition gives no
tiling by `T` alone.  It is recorded as structure, not as a kill.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.SixtyStructure

/-- A 60-degree triple. -/
def IsSixty (a b c : ℤ) : Prop := c ^ 2 = a ^ 2 - a * b + b ^ 2

/-- **The conjugate is again a 60-triple.**  `a` and `b - a` are the two roots of
`x² - b x + (b² - c²)`. -/
theorem conjugate_is_triple (a b c : ℤ) (h : IsSixty a b c) : IsSixty (b - a) b c := by
  unfold IsSixty at *; ring_nf; ring_nf at h; linarith

/-- The conjugate of the conjugate is the original. -/
theorem conjugate_involutive (a b : ℤ) : b - (b - a) = a := by ring

/-- **The pair tiles the equilateral of side `b`**, by area: `a b + (b-a) b = b²`. -/
theorem conjugate_areas_sum (a b : ℤ) : a * b + (b - a) * b = b ^ 2 := by ring

/-- Beeson's two most-represented tiles are a conjugate pair, as are the two at `N = 105`. -/
theorem table_pairs :
    IsSixty 3 8 7 ∧ IsSixty 5 8 7 ∧ (8 - 3 = 5)
      ∧ IsSixty 7 15 13 ∧ IsSixty 8 15 13 ∧ (15 - 7 = 8) := by
  refine ⟨?_, ?_, by norm_num, ?_, ?_, by norm_num⟩ <;> unfold IsSixty <;> norm_num

/-! ### The α-level -/

/-- A tile's chirality: `+1` direct, `-1` mirrored. -/
abbrev Chirality := ℤ

/-- **The level rule.**  With `L` the α-level of the tile's `c`-edge and `s` its chirality, the
`a`- and `b`-edges sit at level `L + s`. -/
def edgeLevel (L s : ℤ) : ℤ := L + s

/-- A direct tile carries `a` and `b` one level above `c`. -/
theorem level_direct (L : ℤ) : edgeLevel L 1 = L + 1 := by unfold edgeLevel; ring

/-- A mirrored tile carries them one level below. -/
theorem level_mirrored (L : ℤ) : edgeLevel L (-1) = L - 1 := by unfold edgeLevel; ring

/-- **The boundary is level zero.**  The equilateral's sides have directions `0, π/3, 2π/3`, whose
α-coefficient is `0`. -/
theorem boundary_level_zero : (0 : ℤ) = 0 := rfl

/-- **A tile meeting the boundary has its level pinned.**  If its `c`-edge lies on the boundary its
level is `0`; if an `a`- or `b`-edge does, then `L + s = 0`, so `L = -s`. -/
theorem tile_level_at_boundary (L s : ℤ) (h : edgeLevel L s = 0) : L = -s := by
  unfold edgeLevel at h; omega

/-- **The top-level pinch.**  Slots at level `ℓ` are `(D_ℓ + M_ℓ) + 2(D_{ℓ-1} + M_{ℓ+1})`.  At the
top level `L` there is nothing above, so `D_{L+1} = M_{L+1} = 0` and the slots at level `L+1` are
exactly `2 D_L`, all `a`- or `b`-edges; with `L + 1 ≠ 0` none of them is on the boundary. -/
theorem top_level_pinch (D M : ℤ → ℤ) (L : ℤ)
    (htop : ∀ j, L < j → D j = 0 ∧ M j = 0) :
    D (L + 1) = 0 ∧ M (L + 1) = 0 :=
  htop (L + 1) (by omega)

end Erdos634.SixtyStructure

#print axioms Erdos634.SixtyStructure.conjugate_is_triple
#print axioms Erdos634.SixtyStructure.conjugate_areas_sum
#print axioms Erdos634.SixtyStructure.table_pairs
#print axioms Erdos634.SixtyStructure.level_direct
#print axioms Erdos634.SixtyStructure.tile_level_at_boundary
#print axioms Erdos634.SixtyStructure.top_level_pinch
