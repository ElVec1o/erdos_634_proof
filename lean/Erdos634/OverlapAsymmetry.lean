import Erdos634.ChordChart

/-!
# The overlap exclusion is genuinely one-sided, and cannot be applied "in both directions"

`OrientationGauge` (2026-09-09) removed the `base` hypothesis of
`StripIteration.interior_rigidity_of_predecessor` by re-choosing the model, and left the whole
burden on the *pairwise, symmetric* hypothesis of `interior_rigidity_of_adjacent`:

```
adj : ∀ j, ¬ (D.tile (idx (j+1))).OppOrient (D.tile (idx j))
```

The existing geometric input is `LayerLink.strip_layer_rigid`'s `overlap`, which is *asymmetric*:
it excludes only the combination **(predecessor unreflected, successor reflected)**.  The obvious
hope is that the reverse combination is excluded by the same argument read backwards, so that
`overlap` applied twice would already give `adj`.

**It is not, and this file proves it, twice over — geometrically and logically.**

## 1. The geometric half: the reverse pair is separated by a line

Put the shared foot `F` at the origin, the predecessor on `[-a, 0]` and the successor on `[0, a]`,
both bodies above the floor (`a = ef`).  `ChordChart` pins the two apex abscissae relative to a
tile's own left foot: unreflected `x_u = S/2 > a` (`predecessor_apex_right_of_foot`, i.e.
`StripRigid.shift_gt_two_a`), reflected `x_r < 0` (`reflected_apex_left_of_mast`).

* **Excluded pair** (predecessor unreflected, successor reflected): predecessor's apex at
  `-a + x_u > 0`, successor's apex at `x_r < 0`.  The apexes *straddle* the vertical through `F`,
  both corner cones at `F` contain `(0,1)`, and the interiors meet — this is `ChordChart`'s
  bridge (ii), and it is the entire content of `overlap`.
* **Reverse pair** (predecessor reflected, successor unreflected): predecessor's apex at
  `-a + x_r < -a < 0`, successor's apex at `x_u > a > 0`.  Now *all three* vertices of the
  predecessor have `x ≤ 0` and *all three* vertices of the successor have `x ≥ 0`.  The vertical
  through `F` is a separating line: the two bodies meet only at `F` itself, and their interiors are
  disjoint (`reverse_pair_separated`).

So the reverse combination is not merely unproved by the overlap argument — it is a *legal* planar
configuration for the overlap argument, which therefore cannot exclude it by any reading.  The
asymmetry is real geometry (the floor has a direction), not a gauge artifact.

## 2. The logical half: independence of the symmetric statement

Abstractly, write `u j = true` for "tile `j` is unreflected **in the chart**" (a frame-absolute
notion — not `Tri.Reflected D.model`, which `OrientationGauge` correctly showed is gauge).  The
overlap exclusion is exactly

```
step : ∀ j, u j = true → u (j+1) = true
```

and the symmetric adjacency hypothesis is `∀ j, u (j+1) = u j`.  `step` does **not** imply it:
`u = (fun j => decide (1 ≤ j))` satisfies `step` and flips between `j = 0` and `j = 1`
(`asym_does_not_imply_sym`).  Applying an implication "in the other direction" is not a proof
technique; here the failing instance is realized by the separated configuration of part 1.

## 3. What `step` alone *does* give, and what is actually still needed

`step` says `u` is monotone, so the orientation pattern along a run is exactly **a reflected
prefix followed by an unreflected suffix, with at most one flip** (`at_most_one_flip`,
`monotone_of_step`).  Everything downstream of the first unreflected tile is then rigid
(`rigid_from_first_unreflected`).

Hence the honest accounting of `OrientationGauge`'s gauge move: it removed a hypothesis stated
against `D.model`, which was indeed contentless, but the geometry it must be replaced by is the
frame-absolute statement **"some tile of the run — equivalently its first — is chart-unreflected"**.
That is not gauge: `Tri` orientations compared against the *target's* floor direction are pinned by
the target, unlike comparison against `D.model`.  In the `a`-strip that statement is supplied by
the mast (`StripRigid.reflected_crosses_mast`, `j ≤ 2`); at an interior floor there is no mast, and
nothing in the corpus supplies it.  **That, and not a symmetric pairwise exclusion, is the
remaining content of "reach 4"'s interior-rigidity step.**

Negative result: it closes off "apply `overlap` twice" as a route, with a witness rather than a
failed attempt.  No label moves; `cor:walls16` and `thm:strippbound` stay CONJECTURE.

Date: 2026-09-09.  Axiom-clean, no `sorry`.
-/

namespace Erdos634.OverlapAsymmetry

open Erdos634.ChordChart

/-! ## Part 1 — the reverse pair is separated by the vertical through the shared foot -/

/-- **Every point of the predecessor lies weakly left of the shared foot**, when the predecessor
is *reflected*.  Its vertices are `(-a, 0)`, `(0,0)` and `(-a + xr, c)` with `xr < 0`, so all three
abscissae are `≤ 0`; a convex combination inherits the bound. -/
theorem reflected_predecessor_left (a xr c s t v : ℝ) (ha : 0 < a) (hr : xr < 0)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hv : 0 ≤ v) (hsum : s + t + v = 1) :
    s * (-a) + t * 0 + v * (-a + xr) ≤ 0 := by
  have h1 : s * (-a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs (by linarith)
  have h2 : v * (-a + xr) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv (by linarith)
  linarith

/-- **Every point of the successor lies weakly right of the shared foot**, when the successor is
*unreflected*.  Its vertices are `(0,0)`, `(a, 0)` and `(xu, c)` with `xu > a > 0`. -/
theorem unreflected_successor_right (a xu c s t v : ℝ) (ha : 0 < a) (hu : a < xu)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hv : 0 ≤ v) (hsum : s + t + v = 1) :
    0 ≤ s * 0 + t * a + v * xu := by
  have h1 : 0 ≤ t * a := mul_nonneg ht ha.le
  have h2 : 0 ≤ v * xu := mul_nonneg hv (by linarith)
  linarith

/-- **The reverse pair is separated.**  A point of the reflected predecessor and a point of the
unreflected successor can agree only on the line `x = 0` through the shared foot: the vertical is a
separating line, so the two bodies have disjoint interiors.  The overlap argument of `ChordChart`
therefore has nothing to say about this configuration — its hypothesis `upward_in_cone` needs the
two apexes on *opposite* sides of the vertical, and here they are on the sides that make both
corner cones avoid `(0,1)`. -/
theorem reverse_pair_separated (a xr xu c : ℝ) (ha : 0 < a) (hr : xr < 0) (hu : a < xu)
    (s t v s' t' v' : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hv : 0 ≤ v) (hsum : s + t + v = 1)
    (hs' : 0 ≤ s') (ht' : 0 ≤ t') (hv' : 0 ≤ v') (hsum' : s' + t' + v' = 1)
    (hEq : s * (-a) + t * 0 + v * (-a + xr) = s' * 0 + t' * a + v' * xu) :
    s * (-a) + t * 0 + v * (-a + xr) = 0 := by
  have h₁ := reflected_predecessor_left a xr c s t v ha hr hs ht hv hsum
  have h₂ := unreflected_successor_right a xu c s' t' v' ha hu hs' ht' hv' hsum'
  linarith

/-- **The separation is realized by the actual base-`β` tile.**  Instantiating with `a = ef`,
`xu = S/2` and any reflected abscissa `xr < 0`: both sign facts are the ones `ChordChart` proves,
so the separated configuration is not hypothetical. -/
theorem reverse_pair_separated_member (e f xr : ℝ) (he : 0 < e) (hef : e < f) (hr : xr < 0) :
    0 < e * f ∧ e * f < (e * (3 * f ^ 2 - e ^ 2)) / (2 * f) ∧ xr < 0 := by
  have hf : 0 < f := lt_trans he hef
  have ha : 0 < e * f := mul_pos he hf
  refine ⟨ha, ?_, hr⟩
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [mul_pos he (sub_pos.mpr (by nlinarith : e ^ 2 < f ^ 2))]

/-! ## Part 2 — the asymmetric exclusion does not imply the symmetric one

`u j = true` reads "tile `j` is unreflected in the chart".  The overlap exclusion is `step`. -/

/-- **`step` makes the pattern monotone**: once a tile is unreflected, so is every later one. -/
theorem monotone_of_step (u : ℕ → Bool) (step : ∀ j, u j = true → u (j + 1) = true)
    (j k : ℕ) (hjk : j ≤ k) (hj : u j = true) : u k = true := by
  induction k with
  | zero => exact (Nat.le_zero.mp hjk) ▸ hj
  | succ n ih =>
      rcases Nat.lt_or_ge j (n + 1) with h | h
      · exact step n (ih (by omega))
      · have hjn : j = n + 1 := by omega
        exact hjn ▸ hj

/-- **Rigidity downstream of the first unreflected tile.**  This is all the overlap exclusion
gives without a frame-absolute base case. -/
theorem rigid_from_first_unreflected (u : ℕ → Bool)
    (step : ∀ j, u j = true → u (j + 1) = true) (j₀ : ℕ) (h : u j₀ = true) :
    ∀ k, j₀ ≤ k → u k = true := fun k hk => monotone_of_step u step j₀ k hk h

/-- **At most one flip.**  If `u` flips at `j` (from `false` to `true`) it can never flip back:
the run's orientation word is `false^p true^q`. -/
theorem at_most_one_flip (u : ℕ → Bool) (step : ∀ j, u j = true → u (j + 1) = true)
    (j k : ℕ) (hjk : j < k) (hj : u j = true) : u k = true :=
  monotone_of_step u step j k (le_of_lt hjk) hj

/-- **The asymmetric exclusion does not imply the symmetric one.**  The pattern
`false, true, true, …` satisfies `step` at every index and yet has adjacent tiles of opposite
orientation at `j = 0`.  So `overlap`, however many times it is applied and in whichever
direction, cannot yield `interior_rigidity_of_adjacent`'s hypothesis. -/
theorem asym_does_not_imply_sym :
    ∃ u : ℕ → Bool, (∀ j, u j = true → u (j + 1) = true) ∧ ¬ (∀ j, u (j + 1) = u j) := by
  refine ⟨fun j => decide (1 ≤ j), fun j _ => by simp, ?_⟩
  intro h
  have := h 0
  simp at this

/-- **What must replace the deleted `base`.**  With a frame-absolute base case at index `0`, the
asymmetric exclusion suffices — this is the existing induction, recorded here only to isolate the
one missing input.  It is *not* a new theorem; it is the statement of the remaining obligation. -/
theorem sym_of_step_and_frame_base (u : ℕ → Bool)
    (step : ∀ j, u j = true → u (j + 1) = true) (base : u 0 = true) :
    ∀ j, u j = true := fun j => monotone_of_step u step 0 j (Nat.zero_le j) base

end Erdos634.OverlapAsymmetry

#print axioms Erdos634.OverlapAsymmetry.reverse_pair_separated
#print axioms Erdos634.OverlapAsymmetry.reverse_pair_separated_member
#print axioms Erdos634.OverlapAsymmetry.monotone_of_step
#print axioms Erdos634.OverlapAsymmetry.asym_does_not_imply_sym
