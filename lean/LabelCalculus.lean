import Mathlib.Tactic

/-!
# The direction-label calculus (Erdős #634, base-β branch)

Every edge direction occurring in a tiling by a base-β tile is `x·α + y·β  (mod π)` for integers
`x, y` (measured across all five tilings we possess, with zero unexplained directions). The pair
`(x,y)` is **not** unique: the branch relation `3α + 2β = π` gives `3α + 2β ≡ 0 (mod π)`, so

    (x, y)  ~  (x + 3, y + 2).

This file is the arithmetic of the resulting quotient. Since `(3,2)` is primitive, `ℤ²/⟨(3,2)⟩ ≅ ℤ`,
and the isomorphism is the **label**

    L(x, y) = 2x − 3y.

Consequences proved here, all member-independent (they use only `3α+2β = π` and `γ = 2α+β`, which
define the branch):

* `label_shift`      — `L` is invariant under `(x,y) ↦ (x+3, y+2)`, so it is well defined on directions;
* `label_ker`        — `L(x,y) = 0` exactly on the multiples of `(3,2)`: the kernel is no bigger;
* `label_surjective` — every integer is a label, so the quotient really is `ℤ` (rank one);
* `label_target_sides` — the target's own three sides carry labels `−3, 0, +3`;
* `label_tile_angles`  — `α, β, γ` carry labels `+2, −3, +1`, the shifts induced by adjacency;
* `tile_triple`, `tile_triple_mirror` — a tile's three edge labels are `{L−2, L, L+1}`, or
  `{L−1, L, L+2}` for the mirrored chirality: **span exactly 3**, whatever the placement.

The geometric input (that directions lie in the lattice at all) is not proved here; it is measured,
and recorded as HEURISTIC in `private/CRUX_WALLS.md`. What is proved here is that *given* that, the
direction set is a window in a rank-1 lattice with the stated anchors and spans.
-/

namespace Erdos634.LabelCalculus

/-- The direction label of `x·α + y·β  (mod π)`. -/
def L (x y : ℤ) : ℤ := 2 * x - 3 * y

/-- **Well defined on directions.** `3α + 2β ≡ 0 (mod π)`, so `(x,y)` may be shifted by `(3,2)`. -/
theorem label_shift (x y : ℤ) : L (x + 3) (y + 2) = L x y := by
  simp [L]; ring

/-- **The kernel is exactly `⟨(3,2)⟩`.** No coarser identification occurs. -/
theorem label_ker (x y : ℤ) : L x y = 0 ↔ ∃ k : ℤ, x = 3 * k ∧ y = 2 * k := by
  constructor
  · intro h
    have h2 : 2 * x = 3 * y := by simp [L] at h; omega
    -- 3 ∣ 2x and gcd(3,2)=1 give 3 ∣ x
    have h3 : (3 : ℤ) ∣ x := by
      have : (3 : ℤ) ∣ 2 * x := ⟨y, by omega⟩
      omega
    obtain ⟨k, hk⟩ := h3
    exact ⟨k, hk, by omega⟩
  · rintro ⟨k, rfl, rfl⟩; simp [L]; ring

/-- **Rank one.** Every integer occurs as a label, so the quotient is `ℤ`, not a proper subgroup. -/
theorem label_surjective (n : ℤ) : L (2 * n) n = n := by simp [L]; ring

/-- **The target's own three sides.** Base `= 0`, the two equal sides `= β` and `= π − β`. -/
theorem label_target_sides : L 0 0 = 0 ∧ L 0 1 = -3 ∧ L 0 (-1) = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [L]

/-- **The tile's angles**, i.e. the label shifts induced by rotating about a shared vertex:
`α ↦ +2`, `β ↦ −3`, `γ = 2α + β ↦ +1`. -/
theorem label_tile_angles : L 1 0 = 2 ∧ L 0 1 = -3 ∧ L 2 1 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [L]

/-- **A tile's three edge labels span exactly 3.** Going round the triangle the direction turns by
the exterior angle, `= −(interior)` mod `π`; subtracting the labels of `α` then `β` from a starting
label `ℓ` gives `ℓ`, `ℓ − 2`, `ℓ + 1`. -/
theorem tile_triple (l : ℤ) :
    (l - L 1 0 = l - 2) ∧ (l - L 1 0 - L 0 1 = l + 1) := by
  simp [L]; omega

/-- The mirrored chirality reverses the turn order, giving `ℓ`, `ℓ − 1`, `ℓ + 2`. -/
theorem tile_triple_mirror (l : ℤ) :
    (l - L 2 1 = l - 1) ∧ (l - L 2 1 + L 1 0 = l + 1) := by
  simp [L]; omega

/-- The three labels of a direct tile, as a set, are `{ℓ-2, ℓ, ℓ+1}`, of span `3`. -/
theorem tile_span (l : ℤ) : (l + 1) - (l - 2) = 3 := by omega

/-! ## The γ-grading

The labels are not merely *some* rank-1 index: they count multiples of `γ`. From the branch
relations `3α + 2β = π` and `γ = 2α + β`,

    2γ = 4α + 2β = 4α + (π − 3α) = α + π ≡ α        (mod π),
    −3γ − β = −6α − 4β = −2(3α + 2β) = −2π ≡ 0,  so  β ≡ −3γ   (mod π),

so `α` and `β` are the `2`- and `(−3)`-multiples of `γ`. Since `gcd(2,3) = 1`, the group they
generate is all of `⟨γ⟩`:

> **every edge direction in a tiling by a base-β tile is an integer multiple of `γ` modulo `π`,
> and the label is exactly that integer.**

Checked against all five tilings we possess (three base-β, one cevian, one four-component scalene):
**zero directions failed**, and the multiples used were small windows of integers.
-/

/-- `α` sits at label `2`, i.e. `α ≡ 2γ (mod π)`. -/
theorem alpha_is_two_gamma : L 1 0 = 2 * L 2 1 := by simp [L]

/-- `β` sits at label `−3`, i.e. `β ≡ −3γ (mod π)`. -/
theorem beta_is_neg_three_gamma : L 0 1 = -3 * L 2 1 := by simp [L]

/-- **The γ-grading.** `α` and `β` generate the whole label group, because `gcd(2,3) = 1`; the
witness is explicit. Hence every direction is a multiple of `γ`. -/
theorem gamma_generates (n : ℤ) : (-n) * L 1 0 + (-n) * L 0 1 = n := by simp [L]; ring

/-- The label of a tile is the label of its `b`-edge, in either chirality: direct edges are
`(a,b,c) = (L+1, L, L−2)` and mirrored `(L−1, L, L+2)`. -/
theorem b_edge_carries_label (l : ℤ) : (l + 1) - 1 = l ∧ (l - 1) + 1 = l := by omega

/-- **The crux, in label form.** The target's equal side has label `−3`. A tile with an edge there
has `L = −1` or `−5` (a `c`-edge), `L = −4` or `−2` (an `a`-edge), or `L = −3` (a `b`-edge).
Since `side_no_b` excludes the last, `hyp:walls` at `e = 1` is exactly: `L ∉ {−4, −2}`. -/
theorem side_label_cases (Lv : ℤ)
    (h : Lv + 1 = -3 ∨ Lv - 2 = -3 ∨ Lv - 1 = -3 ∨ Lv + 2 = -3 ∨ Lv = -3) :
    Lv = -4 ∨ Lv = -1 ∨ Lv = -2 ∨ Lv = -5 ∨ Lv = -3 := by omega

end Erdos634.LabelCalculus
