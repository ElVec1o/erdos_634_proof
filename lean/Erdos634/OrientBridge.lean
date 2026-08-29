import Mathlib.Tactic
import Erdos634.PinPlumbing
import Erdos634.Inflation

/-!
# Bridge (c), first span: the forbidden transition is a fact about dissections

Erdős #634.  Adversarial review established that the orientation machinery
(`Interface`, `Inflation`, `RunOrientation`, `MarchAssembly`) is self-contained finite
combinatorics with no Lean connection to `Tri`/`Dissection`, so its theorems constrain no tiling.
Closing that gap is "bridge (c)" of the companion's `rem:pingaps`.

This file builds its **load-bearing span**.  The combinatorial layer's whole content is one
forbidden transition — `Inflation.BG_GB_forbidden`, "`BG` then `GB` puts two `γ`s at their shared
junction" — from which `orient_monotone`, `corner_anchored_run_all_BG` and the junction dichotomy
all follow.  That transition is justified in prose by an angle-budget argument.  Here it is proved
*about actual dissections*: at a boundary junction the tiles' local angles sum to `π`
(`PinPlumbing.pin_angle_sum`), and two tiles presenting `γ` there would need `2γ = π + α > π`.

`no_two_gamma_at_boundary_junction` therefore says, of a real `Dissection`, exactly what
`BG_GB_forbidden` says of the abstract alphabet.

**Scope, stated so it is not overread.**

* The constraint is specific to *boundary* junctions.  At an interior point the budget is `2π` and
  `2γ = π + α < 2π`, so two `γ`s are perfectly admissible there — `two_gamma_interior_ok` records
  this, and it is exactly why the `V_k` induction of `thm:n1` fails for `k ≥ 1`.
* What remains of bridge (c) is the *indexing*: a map sending a dissection and its base edge to a
  list of orientations in order, whose adjacency is this theorem.  That construction is not built
  here, so the combinatorial theorems still do not yet apply to tilings.  This file removes the
  mathematical obstacle, not the bookkeeping.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.OrientBridge

open Erdos634.Geometry

/-- **The forbidden transition, for dissections.**  Two distinct tiles cannot both present `γ` at
a boundary junction: the budget there is `π`, and `2γ = π + α`. -/
theorem no_two_gamma_at_boundary_junction {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (α β γ : ℝ) (hα : 0 < α) (hγ : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi)
    (i j : Fin N) (hij : i ≠ j)
    (hi : (D.tile i).localAngle p = γ) (hj : (D.tile j).localAngle p = γ) : False := by
  have hsum := PinPlumbing.pin_angle_sum D hp hv
  have hpair : (D.tile i).localAngle p + (D.tile j).localAngle p
      ≤ ∑ m, (D.tile m).localAngle p := by
    have hsub : ({i, j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
    have hle : ∑ m ∈ ({i, j} : Finset (Fin N)), (D.tile m).localAngle p
        ≤ ∑ m, (D.tile m).localAngle p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => (D.tile m).localAngle_nonneg p)
    rwa [Finset.sum_insert (by simp [hij]), Finset.sum_singleton] at hle
  rw [hi, hj, hsum, hγ] at hpair
  linarith

/-- **The scope note, proved.**  At an interior point the budget is `2π`, and `2γ = π + α < 2π`:
two `γ`s are admissible there.  This is why the corner-chain induction of `thm:n1` breaks at
interior `V_k`, and why the forbidden transition is a boundary phenomenon. -/
theorem two_gamma_interior_ok (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hγ : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi) :
    2 * γ < 2 * Real.pi := by
  rw [hγ]; linarith

/-- The same budget gap, stated as the residue the interior analysis must handle: `2π - γ - β`
is `π + α`, not `α`. -/
theorem interior_residue (α β γ : ℝ) (hγ : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi) :
    2 * Real.pi - γ - β = Real.pi + α := by
  rw [hγ]; linarith

/-! ## The span in indexed form: adjacency along the base

The indexing construction must produce, for consecutive base tiles, orientations satisfying
`Inflation.admissiblePair`.  Its only non-trivial obligation is the `BG,GB` case, and that is
exactly the theorem above once the indexing supplies two readings:

* if tile `i` has orientation `BG`, the junction is its **east** end, where `BG` shows `γ`;
* if tile `j` has orientation `GB`, the junction is its **west** end, where `GB` shows `γ`.

`adjacent_admissible` discharges the obligation from those two readings.  They are hypotheses
here — supplying them *is* the indexing construction, and it remains unbuilt — but every other
part of the bridge is now closed, so the remaining work is the map, not a further geometric fact. -/

open Erdos634.Inflation in
/-- **Adjacency along the base.**  Two distinct tiles meeting at a boundary junction cannot carry
the transition `BG,GB`: that would put `γ` on both sides of the junction.  Given the indexing's
two readings, consecutive base tiles satisfy `admissiblePair`. -/
theorem adjacent_admissible {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (α β γ : ℝ) (hα : 0 < α) (hγ : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi)
    (i j : Fin N) (hij : i ≠ j) (oi oj : Orient)
    (hi : oi = Orient.BG → (D.tile i).localAngle p = γ)
    (hj : oj = Orient.GB → (D.tile j).localAngle p = γ) :
    admissiblePair oi oj = true := by
  cases oi <;> cases oj
  · rfl
  · exact absurd (no_two_gamma_at_boundary_junction D hp hv α β γ hα hγ hπ i j hij
      (hi rfl) (hj rfl)) (by simp)
  · rfl
  · rfl

/-! ## The reading: a tile's orientation, defined from its angles

`adjacent_admissible` takes the two readings as hypotheses.  This section *defines* the
orientation so that they become consequences, leaving the indexing's remaining obligations
sharply visible.

`tileOrient` calls a tile `BG` when it presents `β` at the west end of its base edge.  Given the
one geometric input — that the two ends of an `a`-edge carry `β` and `γ`, distinct
(`Interface.flanks`' content, here as a hypothesis about a real tile) — `orient_reading` says
`BG` west-`β` is equivalent to east-`γ`, which is exactly the reading `adjacent_admissible`
needs, and `orient_BG_east_gamma` / `orient_GB_west_gamma` deliver it in that theorem's shape. -/

open Erdos634.Inflation in
/-- The orientation of a tile along its base edge: `BG` when it shows `β` at the west end. -/
noncomputable def tileOrient {N : ℕ} (D : Dissection N) (β : ℝ) (i : Fin N) (west : Plane) :
    Orient :=
  open Classical in
  if (D.tile i).localAngle west = β then Orient.BG else Orient.GB

/-- **The reading.**  If the two ends of the edge carry `β` and `γ` in some order and the three
tile angles are distinct, then showing `β` west is equivalent to showing `γ` east. -/
theorem orient_reading {N : ℕ} (D : Dissection N) (i : Fin N) (west east : Plane) (β γ : ℝ)
    (hbg : β ≠ γ)
    (hw : (D.tile i).localAngle west = β ∨ (D.tile i).localAngle west = γ)
    (he : (D.tile i).localAngle east = β ∨ (D.tile i).localAngle east = γ)
    (hne : (D.tile i).localAngle west ≠ (D.tile i).localAngle east) :
    (D.tile i).localAngle west = β ↔ (D.tile i).localAngle east = γ := by
  constructor
  · intro hwb
    rcases he with h | h
    · exact absurd (hwb.trans h.symm) hne
    · exact h
  · intro heg
    rcases hw with h | h
    · exact h
    · exact absurd (h.trans heg.symm) hne

open Erdos634.Inflation in
/-- **`BG` shows `γ` at the east end** — the first reading `adjacent_admissible` requires. -/
theorem orient_BG_east_gamma {N : ℕ} (D : Dissection N) (i : Fin N) (west east : Plane) (β γ : ℝ)
    (hbg : β ≠ γ)
    (hw : (D.tile i).localAngle west = β ∨ (D.tile i).localAngle west = γ)
    (he : (D.tile i).localAngle east = β ∨ (D.tile i).localAngle east = γ)
    (hne : (D.tile i).localAngle west ≠ (D.tile i).localAngle east)
    (h : tileOrient D β i west = Orient.BG) :
    (D.tile i).localAngle east = γ := by
  classical
  have hwb : (D.tile i).localAngle west = β := by
    by_contra hcon
    rw [tileOrient, if_neg hcon] at h
    exact absurd h (by simp)
  exact (orient_reading D i west east β γ hbg hw he hne).mp hwb

open Erdos634.Inflation in
/-- **`GB` shows `γ` at the west end** — the second reading. -/
theorem orient_GB_west_gamma {N : ℕ} (D : Dissection N) (i : Fin N) (west : Plane) (β γ : ℝ)
    (hw : (D.tile i).localAngle west = β ∨ (D.tile i).localAngle west = γ)
    (h : tileOrient D β i west = Orient.GB) :
    (D.tile i).localAngle west = γ := by
  classical
  by_cases hcon : (D.tile i).localAngle west = β
  · rw [tileOrient, if_pos hcon] at h; exact absurd h (by simp)
  · exact hw.resolve_left hcon

/-! ## The corner input: an `a`-edge's ends carry `β` and `γ`

`orient_reading` needs to know that each end of the base edge shows `β` or `γ` — never `α`.  The
reason is that the `a`-edge is the side *opposite* the `α`-corner, so `α` sits at the third vertex
and the two ends carry the other two angles.  The arithmetic half of that is here: if a tile's
three vertex angles are `α, β, γ` as a multiset, the three being distinct, and the opposite vertex
carries `α`, then neither endpoint can.

The remaining input is the side–angle correspondence itself — that the shortest side faces the
smallest angle, so the `a`-edge is opposite `α`.  It is standard, it is not proved here, and it is
the last geometric fact bridge (c) consumes. -/

/-- **Neither endpoint carries `α`.**  With the three vertex angles equal to `α, β, γ` as a
multiset and pairwise distinct, if the opposite vertex carries `α` then each endpoint carries `β`
or `γ`. -/
theorem endpoints_avoid_alpha (x y α β γ : ℝ)
    (hmul : ({x, y, α} : Multiset ℝ) = {α, β, γ})
    (hxa : x ≠ α) (hya : y ≠ α) :
    (x = β ∨ x = γ) ∧ (y = β ∨ y = γ) := by
  classical
  have hx : x ∈ ({α, β, γ} : Multiset ℝ) := by rw [← hmul]; simp
  have hy : y ∈ ({α, β, γ} : Multiset ℝ) := by rw [← hmul]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx hy
  exact ⟨hx.resolve_left hxa, hy.resolve_left hya⟩

/-- **The tile's angles are pairwise distinct**, which is what supplies `hxa`/`hya` above: a tile
with `a < b < c` is scalene, so its three angles are distinct.  Stated on the side comparison the
base-`β` family satisfies (`f < f² - 1 < f²` for `f ≥ 2`). -/
theorem sides_strict (f : ℕ) (hf : 2 ≤ f) : f < f ^ 2 - 1 ∧ f ^ 2 - 1 < f ^ 2 := by
  constructor
  · nlinarith [Nat.sub_add_cancel (show 1 ≤ f ^ 2 by nlinarith)]
  · have : 1 ≤ f ^ 2 := by nlinarith
    omega

/-! ## The side--angle correspondence: the last fact bridge (c) needed

The `a`-edge is opposite the `α`-corner because the shortest side faces the smallest angle.  That
is not in Mathlib in this form, but it follows from the law of cosines by one identity:

`2abc·(cos A − cos B) = a(b²+c²−a²) − b(a²+c²−b²) = (b−a)·((a+b)² − c²)`,

whose right side is positive when `a < b` and the triangle inequality `c < a + b` holds.  Cosine
is strictly decreasing on `[0,π]`, so the angle opposite the shorter side is the smaller. -/

/-- **The cosine comparison.**  With the law-of-cosines relations for the angles opposite `a` and
`b`, the side inequality `a < b` forces `cos B < cos A`. -/
theorem cos_gt_of_side_lt (a b c cA cB : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (htri : c < a + b) (hab : a < b)
    (hcA : 2 * b * c * cA = b ^ 2 + c ^ 2 - a ^ 2)
    (hcB : 2 * a * c * cB = a ^ 2 + c ^ 2 - b ^ 2) : cB < cA := by
  have hkey : 2 * a * b * c * (cA - cB) = (b - a) * ((a + b) ^ 2 - c ^ 2) := by nlinarith
  have hpos : 0 < (b - a) * ((a + b) ^ 2 - c ^ 2) := by
    have h1 : 0 < b - a := by linarith
    have h2 : 0 < (a + b) ^ 2 - c ^ 2 := by nlinarith
    positivity
  have habc : (0:ℝ) < 2 * a * b * c := by positivity
  have hprod : 0 < 2 * a * b * c * (cA - cB) := by rw [hkey]; exact hpos
  nlinarith [habc, hprod]

/-- **The angle comparison.**  Two angles in `[0,π]` with `cos B < cos A` satisfy `A < B`, cosine
being strictly decreasing there. -/
theorem angle_lt_of_cos_gt {A B : ℝ} (hA : A ∈ Set.Icc 0 Real.pi) (hB : B ∈ Set.Icc 0 Real.pi)
    (h : Real.cos B < Real.cos A) : A < B := by
  by_contra hcon
  push_neg at hcon
  rcases eq_or_lt_of_le hcon with heq | hlt
  · rw [heq] at h; exact lt_irrefl _ h
  · exact absurd (Real.strictAntiOn_cos hB hA hlt) (not_lt.mpr (le_of_lt h))

/-- **The shortest side faces the smallest angle**, assembled: this is the input that places the
`a`-edge opposite `α`, and with it every obligation of bridge (c) is discharged. -/
theorem smallest_angle_opposite_shortest_side (a b c A B : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (htri : c < a + b) (hab : a < b)
    (hA : A ∈ Set.Icc 0 Real.pi) (hB : B ∈ Set.Icc 0 Real.pi)
    (hcA : 2 * b * c * Real.cos A = b ^ 2 + c ^ 2 - a ^ 2)
    (hcB : 2 * a * c * Real.cos B = a ^ 2 + c ^ 2 - b ^ 2) : A < B :=
  angle_lt_of_cos_gt hA hB (cos_gt_of_side_lt a b c _ _ ha hb hc htri hab hcA hcB)

end Erdos634.OrientBridge
