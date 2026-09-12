import Erdos634.TileAt
import Erdos634.CellCoord
import Erdos634.CertCoord

/-!
# Placement completeness — the geometric half of H7, at the `Dissection` level

Erdős #634.  Every exhaustive refutation in this project (`N = 11, 23, 26, 47, 59, 66, 71, 107, …`,
Lemma P, the 45-lemma hitting set) rests on the constructor's branching rule, written out at
`paper/erdos-634.tex:1829-1836`:

> at the lexicographically least vertex `v` of the unfilled region — necessarily convex — every
> tile of any tiling whose closure contains `v` has a corner there (an edge through `v` would
> subtend angle `π`), so the clockwise-most of them has a corner at `v` with one side along the
> clockwise boundary ray; this leaves at most six placements.

Until this file that argument had **no Lean** (blocker (iv) of `PAPER_MAP.md`, F-4 in the
`e2b3` room).  This file proves it as a theorem about an arbitrary `Dissection`, in the corpus's
own language, with the constructor's conventions read off `build23.py` (`pick_point`: candidates
sorted by `y` then `x`; the ray `d₀` is the *start* of a free angular sector, i.e. the tile to be
placed lies **counter-clockwise** of `d₀`).

## The statement (`placement_completeness`)

Let `D : Dissection N`, `S : Finset (Fin N)` the placed tiles, `U = unfilled D S` the target minus
the placed tiles.  Let `v` be lexicographically least on `closure U` (`hlex`), and `d₀` a unit
vector such that points just **counter-clockwise** of `d₀` at `v` are in `U` arbitrarily close
to `v` (`hfree`) while a whole small wedge just **clockwise** of `d₀` misses `U` (`hblocked`).
Then some tile `j ∉ S` has a vertex at `v`, a second vertex on the ray `v + ℝ₊·d₀`, and its third
vertex strictly counter-clockwise of `d₀`.

The three facts of the paper's argument appear as separate theorems:

* **(a)** `exists_unplaced_of_mem_closure` — a point of `closure U` lies in some unplaced tile;
* **(c)** `lexmin_carrier_is_vertex` — a point of a triangle that is lexicographically least
  *on that triangle* is one of its vertices.  Combined with
  `carrier_subset_closure_unfilled` (**every unplaced tile lies inside `closure U`** — the
  step that replaces the paper's "an edge through `v` would subtend `π`"), this gives:
  every unplaced tile whose closure contains `v` has a corner there (`unplaced_corner_at_lexmin`);
* **(d)** `corner_edge_dichotomy` — for a triangle with a vertex at `v`, either the near-`d₀`
  counter-clockwise points avoid it, or it has an edge along `d₀` with the third vertex
  counter-clockwise; the "both sides" case is excluded by a measure argument
  (`not_isOpen_subset_frontiers`): an open wedge cannot sit inside the placed tiles' frontiers.

**(b)**, convexity of `U` at `v`, is never stated: the lexicographic hypothesis is used directly.

## What is and is not here

The theorem is unconditional at the `Dissection` level: no "configuration reached by the
constructor" appears anywhere.  What a *certificate* must supply, per node, is the discharge of
`hlex`, `hfree`, `hblocked` for its explicit `(S, v, d₀)` — finite coordinate arithmetic — and then
the six-placement enumeration (`SixPlacements.lean`) and the per-placement kills.  Both are done
at two instances in `SixPlacements.lean` / `LemmaPNode2.lean`: the real 44-tiling with `S = ∅`
(satisfiability control), and node 2 of Lemma P (a genuine jam kill).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PlacementCompleteness

open Erdos634.Geometry Erdos634.Geometry.Dissection Set MeasureTheory

/-! ## 1. Definitions: lexicographic order, the unfilled region, the perpendicular -/

/-- Lexicographic order on the plane, `y` first then `x` — `build23.py`'s `pick_point` sort key. -/
def LexLE (v p : Plane) : Prop := v 1 < p 1 ∨ (v 1 = p 1 ∧ v 0 ≤ p 0)

/-- The unfilled region after placing the tiles in `S`. -/
def unfilled {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) : Set Plane :=
  D.target.carrier \ ⋃ i ∈ S, (D.tile i).carrier

/-- The counter-clockwise perpendicular of a vector. -/
noncomputable def perp (d : Plane) : Plane := Erdos634.CertCoord.mkPt (-(d 1)) (d 0)

@[simp] theorem perp_zero (d : Plane) : perp d 0 = -(d 1) := by simp [perp]
@[simp] theorem perp_one (d : Plane) : perp d 1 = d 0 := by simp [perp]

theorem plane_ext {p q : Plane} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  refine PiLp.ext ?_
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem dist_sq_coord (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-! ## 2. A measure-theoretic lemma: no open set sits inside the placed tiles' frontiers -/

/-- **An open nonempty set is not contained in the union of finitely many tile frontiers.**
Tile frontiers are null (`Tri.volume_frontier`); an open nonempty set has positive measure. -/
theorem not_isOpen_subset_frontiers {N : ℕ} (D : Dissection N) (S : Finset (Fin N))
    {W : Set Plane} (hW : IsOpen W) (hne : W.Nonempty)
    (hsub : W ⊆ ⋃ i ∈ S, frontier (D.tile i).carrier) : False := by
  have hpos : 0 < volume W := hW.measure_pos volume hne
  have hnull : volume (⋃ i ∈ S, frontier (D.tile i).carrier) = 0 := by
    have h := (measure_biUnion_null_iff (μ := volume) (I := (S : Set (Fin N)))
      S.countable_toSet (s := fun i => frontier (D.tile i).carrier)).mpr
      (fun i _ => (D.tile i).volume_frontier)
    simpa using h
  exact absurd (measure_mono_null hsub hnull) hpos.ne'

/-- A point of an unplaced tile's interior that is in a placed tile lies on that placed tile's
frontier. -/
theorem mem_frontier_of_mem_interior_unplaced {N : ℕ} (D : Dissection N) (S : Finset (Fin N))
    {j : Fin N} (hj : j ∉ S) {p : Plane} (hp : p ∈ interior (D.tile j).carrier)
    (hpl : p ∈ ⋃ i ∈ S, (D.tile i).carrier) :
    p ∈ ⋃ i ∈ S, frontier (D.tile i).carrier := by
  rw [Set.mem_iUnion₂] at hpl ⊢
  obtain ⟨i, hi, hpi⟩ := hpl
  refine ⟨i, hi, subset_closure hpi, ?_⟩
  intro hint
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hint hp

/-! ## 3. Fact (a): the closure of the unfilled region is inside the unplaced tiles -/

/-- A point of the unfilled region lies in some unplaced tile. -/
theorem exists_unplaced_of_mem_unfilled {N : ℕ} (D : Dissection N) (S : Finset (Fin N))
    {p : Plane} (hp : p ∈ unfilled D S) : ∃ j, j ∉ S ∧ p ∈ (D.tile j).carrier := by
  obtain ⟨hpt, hnot⟩ := hp
  obtain ⟨j, hj⟩ := D.exists_tile_mem hpt
  refine ⟨j, ?_, hj⟩
  intro hjS
  exact hnot (Set.mem_iUnion₂.mpr ⟨j, hjS, hj⟩)

/-- **(a)** A point of the *closure* of the unfilled region lies in some unplaced tile. -/
theorem exists_unplaced_of_mem_closure {N : ℕ} (D : Dissection N) (S : Finset (Fin N))
    {p : Plane} (hp : p ∈ closure (unfilled D S)) : ∃ j, j ∉ S ∧ p ∈ (D.tile j).carrier := by
  classical
  have hsub : unfilled D S ⊆ ⋃ j ∈ (Finset.univ.filter fun j => j ∉ S), (D.tile j).carrier := by
    intro q hq
    obtain ⟨j, hj, hqj⟩ := exists_unplaced_of_mem_unfilled D S hq
    exact Set.mem_iUnion₂.mpr ⟨j, by simp [hj], hqj⟩
  have hcl : IsClosed (⋃ j ∈ (Finset.univ.filter fun j => j ∉ S), (D.tile j).carrier) :=
    isClosed_biUnion_finset fun j _ => (D.tile j).isCompact.isClosed
  have := closure_minimal hsub hcl hp
  obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.mp this
  exact ⟨j, by simpa using hj, hpj⟩

/-! ## 4. Every unplaced tile lies inside the closure of the unfilled region -/

/-- **An unplaced tile's carrier is inside `closure (unfilled D S)`.**  Its interior minus the
placed tiles is inside `U`, and the placed tiles meet that interior only in a null set, so the
interior is inside `closure U`; the carrier is the closure of its interior. -/
theorem carrier_subset_closure_unfilled {N : ℕ} (D : Dissection N) (S : Finset (Fin N))
    {j : Fin N} (hj : j ∉ S) : (D.tile j).carrier ⊆ closure (unfilled D S) := by
  have hint : interior (D.tile j).carrier ⊆ closure (unfilled D S) := by
    intro x hx
    rw [mem_closure_iff]
    intro o ho hxo
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hW : IsOpen (o ∩ interior (D.tile j).carrier) := ho.inter isOpen_interior
    have hne : (o ∩ interior (D.tile j).carrier).Nonempty := ⟨x, hxo, hx⟩
    refine not_isOpen_subset_frontiers D S hW hne ?_
    intro y ⟨hyo, hyi⟩
    have hyt : y ∈ D.target.carrier :=
      Erdos634.BaseSelection.tile_subset_target D j (interior_subset hyi)
    have hyU : y ∉ unfilled D S := fun h => by
      have : y ∈ o ∩ unfilled D S := ⟨hyo, h⟩
      rw [hemp] at this; exact this
    have hpl : y ∈ ⋃ i ∈ S, (D.tile i).carrier := by
      by_contra hn; exact hyU ⟨hyt, hn⟩
    exact mem_frontier_of_mem_interior_unplaced D S hj hyi hpl
  have h1 : closure (interior (D.tile j).carrier) = closure (D.tile j).carrier :=
    (D.tile j).convex.closure_interior_eq_closure_of_nonempty_interior
      (D.tile j).interior_nonempty
  have h2 : closure (D.tile j).carrier = (D.tile j).carrier :=
    (D.tile j).isCompact.isClosed.closure_eq
  calc (D.tile j).carrier = closure (interior (D.tile j).carrier) := by rw [h1, h2]
    _ ⊆ closure (closure (unfilled D S)) := closure_mono hint
    _ = closure (unfilled D S) := closure_closure

/-! ## 5. Fact (c): a lexicographically least point of a triangle is a vertex -/

/-- **(c)** If `v ∈ T.carrier` is lexicographically `≤` every point of `T.carrier`, then `v` is a
vertex of `T`.  Two applications of the support-face lemma `SupportFace.mem_convexHull_max`:
first for `−y`, then for `−x` on the bottom face. -/
theorem lexmin_carrier_is_vertex (T : Tri) {v : Plane} (hv : v ∈ T.carrier)
    (hlex : ∀ p ∈ T.carrier, LexLE v p) : ∃ k, T.pts k = v := by
  classical
  set s : Finset Plane := Finset.univ.image T.pts with hs
  have hcar : T.carrier = convexHull ℝ (s : Set Plane) := by
    rw [Tri.carrier, hs, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hmem : ∀ w ∈ s, w ∈ T.carrier := fun w hw => by
    rw [hcar]; exact subset_convexHull ℝ _ hw
  -- the functional `−y`
  set f₁ : Plane →ₗ[ℝ] ℝ := crossL (Erdos634.CertCoord.mkPt (-1) 0) with hf₁
  have hf₁v : ∀ w : Plane, f₁ w = -(w 1) := fun w => by simp [hf₁, cross]
  have hle₁ : ∀ w ∈ s, f₁ w ≤ f₁ v := by
    intro w hw
    rw [hf₁v, hf₁v]
    rcases hlex w (hmem w hw) with h | ⟨h, _⟩ <;> linarith
  have hv₁ : v ∈ convexHull ℝ (s : Set Plane) := by rw [← hcar]; exact hv
  have hstep₁ := Erdos634.SupportFace.mem_convexHull_max f₁ (f₁ v) s hle₁ hv₁ rfl
  set s₁ := s.filter (fun w => f₁ w = f₁ v) with hs₁
  have hs₁mem : ∀ w ∈ s₁, w ∈ s ∧ w 1 = v 1 := fun w hw => by
    rw [hs₁, Finset.mem_filter] at hw
    refine ⟨hw.1, ?_⟩
    have := hw.2; rw [hf₁v, hf₁v] at this; linarith
  -- the functional `−x`
  set f₂ : Plane →ₗ[ℝ] ℝ := crossL (Erdos634.CertCoord.mkPt 0 1) with hf₂
  have hf₂v : ∀ w : Plane, f₂ w = -(w 0) := fun w => by simp [hf₂, cross]
  have hle₂ : ∀ w ∈ s₁, f₂ w ≤ f₂ v := by
    intro w hw
    obtain ⟨hws, hw1⟩ := hs₁mem w hw
    rw [hf₂v, hf₂v]
    rcases hlex w (hmem w hws) with h | ⟨_, h⟩
    · linarith
    · linarith
  have hstep₂ := Erdos634.SupportFace.mem_convexHull_max f₂ (f₂ v) s₁ hle₂ hstep₁ rfl
  set s₂ := s₁.filter (fun w => f₂ w = f₂ v) with hs₂
  have hs₂mem : ∀ w ∈ s₂, w ∈ s ∧ w = v := fun w hw => by
    rw [hs₂, Finset.mem_filter] at hw
    obtain ⟨hws, hw1⟩ := hs₁mem w hw.1
    have hw0 : w 0 = v 0 := by
      have := hw.2; rw [hf₂v, hf₂v] at this; linarith
    exact ⟨hws, plane_ext hw0 hw1⟩
  -- `s₂` is nonempty since `v` is in its hull
  have hne : s₂.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hstep₂
    simp at hstep₂
  obtain ⟨w, hw⟩ := hne
  obtain ⟨hws, hwv⟩ := hs₂mem w hw
  rw [hs, Finset.mem_image] at hws
  obtain ⟨k, _, hk⟩ := hws
  exact ⟨k, hk.trans hwv⟩

/-- **Every unplaced tile whose closure contains the lexicographic minimum of `closure U` has a
corner there.**  (The paper's "an edge through `v` would subtend angle `π`", proved instead by
`carrier_subset_closure_unfilled` + `lexmin_carrier_is_vertex`.) -/
theorem unplaced_corner_at_lexmin {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) {v : Plane}
    (hlex : ∀ p ∈ closure (unfilled D S), LexLE v p)
    {j : Fin N} (hj : j ∉ S) (hv : v ∈ (D.tile j).carrier) : ∃ k, (D.tile j).pts k = v :=
  lexmin_carrier_is_vertex (D.tile j) hv
    (fun p hp => hlex p (carrier_subset_closure_unfilled D S hj hp))

/-! ## 6. Barycentric coordinates of `p₀ + a·e₁ + b·e₂` -/

/-- The coordinates of a point written in the edge frame at vertex `0`. -/
theorem coord_edge_combo (T : Tri) (a b : ℝ) :
    T.basis.coord 0 (T.pts 0 + a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0)) = 1 - a - b ∧
    T.basis.coord 1 (T.pts 0 + a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0)) = a ∧
    T.basis.coord 2 (T.pts 0 + a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0)) = b := by
  have hx : T.pts 0 + a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0)
      = (![1 - a - b, a, b] : Fin 3 → ℝ) 0 • T.pts 0 + (![1 - a - b, a, b] : Fin 3 → ℝ) 1 • T.pts 1
        + (![1 - a - b, a, b] : Fin 3 → ℝ) 2 • T.pts 2 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    module
  have hsum : (![1 - a - b, a, b] : Fin 3 → ℝ) 0 + (![1 - a - b, a, b] : Fin 3 → ℝ) 1
      + (![1 - a - b, a, b] : Fin 3 → ℝ) 2 = 1 := by simp; ring
  refine ⟨?_, ?_, ?_⟩
  · have := Erdos634.Subdivision.Tri.coord_eq_of_combo T _ _ hsum hx 0; simpa using this
  · have := Erdos634.Subdivision.Tri.coord_eq_of_combo T _ _ hsum hx 1; simpa using this
  · have := Erdos634.Subdivision.Tri.coord_eq_of_combo T _ _ hsum hx 2; simpa using this

/-- Membership of `p₀ + a·e₁ + b·e₂` in the carrier and the interior, in terms of `(a, b)`. -/
theorem edge_combo_mem_iff (T : Tri) (a b : ℝ) :
    (T.pts 0 + a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0) ∈ T.carrier ↔
      0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1) ∧
    (T.pts 0 + a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0) ∈ interior T.carrier ↔
      0 < a ∧ 0 < b ∧ a + b < 1) := by
  obtain ⟨h0, h1, h2⟩ := coord_edge_combo T a b
  constructor
  · rw [T.carrier_eq_nonneg_coord]
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have := h 0; have := h 1; have := h 2
      rw [h0] at *; rw [h1] at *; rw [h2] at *
      refine ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨ha, hb, hab⟩ k
      fin_cases k
      · simp only [Fin.zero_eta]; rw [h0]; linarith
      · simp only [Fin.mk_one]; rw [h1]; linarith
      · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, h2]; linarith
  · rw [T.mem_interior_iff_coord_pos]
    constructor
    · intro h
      have := h 0; have := h 1; have := h 2
      rw [h0] at *; rw [h1] at *; rw [h2] at *
      refine ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨ha, hb, hab⟩ k
      fin_cases k
      · simp only [Fin.zero_eta]; rw [h0]; linarith
      · simp only [Fin.mk_one]; rw [h1]; linarith
      · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, h2]; linarith

end Erdos634.PlacementCompleteness

namespace Erdos634.PlacementCompleteness

open Erdos634.Geometry Erdos634.Geometry.Dissection Set MeasureTheory

/-! ## 7. The edge frame at vertex `0`: decomposing a vector along the two edges -/

/-- Any vector decomposes along the two edge vectors at vertex `0` (Cramer's rule). -/
theorem decompose_edge_frame (T : Tri) (u : Plane) :
    u = (cross u (T.pts 2 - T.pts 0) / T.det) • (T.pts 1 - T.pts 0)
        + (cross (T.pts 1 - T.pts 0) u / T.det) • (T.pts 2 - T.pts 0) := by
  have hΔ := T.det_ne_zero
  refine plane_ext ?_ ?_
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hΔ]
    simp only [cross, Tri.det, PiLp.sub_apply]; ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hΔ]
    simp only [cross, Tri.det, PiLp.sub_apply]; ring

/-- The coordinates of a decomposition. -/
theorem coords_of_decomp (T : Tri) {u : Plane} {a b : ℝ}
    (h : u = a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0)) :
    u 0 = a * (T.pts 1 - T.pts 0) 0 + b * (T.pts 2 - T.pts 0) 0 ∧
    u 1 = a * (T.pts 1 - T.pts 0) 1 + b * (T.pts 2 - T.pts 0) 1 := by
  constructor
  · have := congrArg (fun p : Plane => p 0) h; simpa using this
  · have := congrArg (fun p : Plane => p 1) h; simpa using this

theorem exists_delta_lin (a a' : ℝ) (h : 0 < a ∨ (a = 0 ∧ a' < 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ → 0 < a - s * a' := by
  rcases h with ha | ⟨ha, ha'⟩
  · refine ⟨a / (|a'| + 1), by positivity, fun s hs hsδ => ?_⟩
    have h1 : s * (|a'| + 1) < a := by
      rwa [lt_div_iff₀ (by positivity)] at hsδ
    have h2 : s * a' ≤ s * |a'| := mul_le_mul_of_nonneg_left (le_abs_self a') hs.le
    nlinarith
  · exact ⟨1, one_pos, fun s hs _ => by rw [ha]; nlinarith⟩

/-- **The clockwise wedge lies inside the tile** when the edge-frame coefficients of `d` are
positive, or zero with the perpendicular pointing inward. -/
theorem wedge_interior (T : Tri) (d n : Plane) (a b a' b' : ℝ)
    (hd : d = a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0))
    (hn : n = a' • (T.pts 1 - T.pts 0) + b' • (T.pts 2 - T.pts 0))
    (ha : 0 < a ∨ (a = 0 ∧ a' < 0)) (hb : 0 < b ∨ (b = 0 ∧ b' < 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      T.pts 0 + t • (d - s • n) ∈ interior T.carrier := by
  obtain ⟨δa, hδa, ha'⟩ := exists_delta_lin a a' ha
  obtain ⟨δb, hδb, hb'⟩ := exists_delta_lin b b' hb
  set M : ℝ := |a| + |b| + |a'| + |b'| + 1 with hM
  have hMpos : 0 < M := by positivity
  refine ⟨min δa (min δb (min 1 (1 / M))), by positivity, fun t s ht htδ hs hsδ => ?_⟩
  have hsa : s < δa := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hsb : s < δb := lt_of_lt_of_le hsδ ((min_le_right _ _).trans (min_le_left _ _))
  have hs1 : s < 1 := lt_of_lt_of_le hsδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htM : t < 1 / M := lt_of_lt_of_le htδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpt : T.pts 0 + t • (d - s • n)
      = T.pts 0 + (t * (a - s * a')) • (T.pts 1 - T.pts 0)
        + (t * (b - s * b')) • (T.pts 2 - T.pts 0) := by
    rw [hd, hn]; module
  rw [hpt, (edge_combo_mem_iff T _ _).2]
  have h1 := ha' s hs hsa
  have h2 := hb' s hs hsb
  refine ⟨mul_pos ht h1, mul_pos ht h2, ?_⟩
  have hsa' : -(s * a') ≤ s * |a'| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs a') hs.le; linarith
  have hsb' : -(s * b') ≤ s * |b'| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs b') hs.le; linarith
  have hsa1 : s * |a'| ≤ |a'| := mul_le_of_le_one_left (abs_nonneg a') hs1.le
  have hsb1 : s * |b'| ≤ |b'| := mul_le_of_le_one_left (abs_nonneg b') hs1.le
  have hsum : (a - s * a') + (b - s * b') ≤ M := by
    rw [hM]; linarith [le_abs_self a, le_abs_self b]
  have htM' : t * M < 1 := by rwa [lt_div_iff₀ hMpos] at htM
  calc t * (a - s * a') + t * (b - s * b') = t * ((a - s * a') + (b - s * b')) := by ring
    _ ≤ t * M := mul_le_mul_of_nonneg_left hsum ht.le
    _ < 1 := htM'

/-- **The counter-clockwise wedge misses the tile** when an edge-frame coefficient of `d` is
negative. -/
theorem wedge_exclusion (T : Tri) (d n : Plane) (a b a' b' : ℝ)
    (hd : d = a • (T.pts 1 - T.pts 0) + b • (T.pts 2 - T.pts 0))
    (hn : n = a' • (T.pts 1 - T.pts 0) + b' • (T.pts 2 - T.pts 0))
    (h : a < 0 ∨ b < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      T.pts 0 + t • (d + s • n) ∉ T.carrier := by
  have hpt : ∀ t s : ℝ, T.pts 0 + t • (d + s • n)
      = T.pts 0 + (t * (a + s * a')) • (T.pts 1 - T.pts 0)
        + (t * (b + s * b')) • (T.pts 2 - T.pts 0) := by
    intro t s; rw [hd, hn]; module
  rcases h with ha | hb
  · refine ⟨-a / (|a'| + 1), div_pos (neg_pos.mpr ha) (by positivity), fun t s ht htδ hs hsδ => ?_⟩
    rw [hpt, (edge_combo_mem_iff T _ _).1]
    rintro ⟨h1, -, -⟩
    have h2 : s * (|a'| + 1) < -a := by rwa [lt_div_iff₀ (by positivity)] at hsδ
    have h3 : s * a' ≤ s * |a'| := mul_le_mul_of_nonneg_left (le_abs_self a') hs.le
    have h4 : a + s * a' < 0 := by nlinarith
    have : t * (a + s * a') < 0 := mul_neg_of_pos_of_neg ht h4
    linarith
  · refine ⟨-b / (|b'| + 1), div_pos (neg_pos.mpr hb) (by positivity), fun t s ht htδ hs hsδ => ?_⟩
    rw [hpt, (edge_combo_mem_iff T _ _).1]
    rintro ⟨-, h1, -⟩
    have h2 : s * (|b'| + 1) < -b := by rwa [lt_div_iff₀ (by positivity)] at hsδ
    have h3 : s * b' ≤ s * |b'| := mul_le_mul_of_nonneg_left (le_abs_self b') hs.le
    have h4 : b + s * b' < 0 := by nlinarith
    have : t * (b + s * b') < 0 := mul_neg_of_pos_of_neg ht h4
    linarith

/-! ## 8. Fact (d): the corner/edge dichotomy at a vertex -/

theorem cross_anticomm (u w : Plane) : cross u w = -(cross w u) := by
  simp only [cross]; ring

theorem norm_sq_pos_of_det (T : Tri) :
    0 < (T.pts 1 - T.pts 0) 0 ^ 2 + (T.pts 1 - T.pts 0) 1 ^ 2 ∧
    0 < (T.pts 2 - T.pts 0) 0 ^ 2 + (T.pts 2 - T.pts 0) 1 ^ 2 := by
  have hΔ := T.det_ne_zero
  have hΔe : T.det = (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1
      - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0 := rfl
  constructor
  · by_contra hcon
    push_neg at hcon
    have h0 : (T.pts 1 - T.pts 0) 0 = 0 := by nlinarith [sq_nonneg ((T.pts 1 - T.pts 0) 0), sq_nonneg ((T.pts 1 - T.pts 0) 1)]
    have h1 : (T.pts 1 - T.pts 0) 1 = 0 := by nlinarith [sq_nonneg ((T.pts 1 - T.pts 0) 0), sq_nonneg ((T.pts 1 - T.pts 0) 1)]
    apply hΔ; rw [hΔe, h0, h1]; ring
  · by_contra hcon
    push_neg at hcon
    have h0 : (T.pts 2 - T.pts 0) 0 = 0 := by nlinarith [sq_nonneg ((T.pts 2 - T.pts 0) 0), sq_nonneg ((T.pts 2 - T.pts 0) 1)]
    have h1 : (T.pts 2 - T.pts 0) 1 = 0 := by nlinarith [sq_nonneg ((T.pts 2 - T.pts 0) 0), sq_nonneg ((T.pts 2 - T.pts 0) 1)]
    apply hΔ; rw [hΔe, h0, h1]; ring

/-- **(d)** For a triangle with vertex `0` at `v` and a unit direction `d` whose clockwise wedge
is *not* inside the triangle: either the counter-clockwise near-`d` points avoid the triangle, or
the triangle has an edge from `v` along `d` and its third vertex strictly counter-clockwise of
`d`. -/
theorem corner_edge_dichotomy (T : Tri) (d : Plane) (hunit : d 0 ^ 2 + d 1 ^ 2 = 1)
    (hCW : ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      T.pts 0 + t • (d - s • perp d) ∈ interior T.carrier) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
        T.pts 0 + t • (d + s • perp d) ∉ T.carrier) ∨
    (∃ k₁ k₂ : Fin 3, k₁ ≠ 0 ∧ k₂ ≠ 0 ∧ k₁ ≠ k₂ ∧
        (∃ c : ℝ, 0 < c ∧ T.pts k₁ = T.pts 0 + c • d) ∧
        0 < cross d (T.pts k₂ - T.pts 0)) := by
  have hΔ := T.det_ne_zero
  obtain ⟨he₁, he₂⟩ := norm_sq_pos_of_det T
  set A := cross d (T.pts 2 - T.pts 0) / T.det with hA
  set B := cross (T.pts 1 - T.pts 0) d / T.det with hB
  set A' := cross (perp d) (T.pts 2 - T.pts 0) / T.det with hA'
  set B' := cross (T.pts 1 - T.pts 0) (perp d) / T.det with hB'
  have hd : d = A • (T.pts 1 - T.pts 0) + B • (T.pts 2 - T.pts 0) := decompose_edge_frame T d
  have hn : perp d = A' • (T.pts 1 - T.pts 0) + B' • (T.pts 2 - T.pts 0) :=
    decompose_edge_frame T (perp d)
  obtain ⟨hd0, hd1⟩ := coords_of_decomp T hd
  have hAΔ : A * T.det = cross d (T.pts 2 - T.pts 0) := by rw [hA]; field_simp
  have hBΔ : B * T.det = cross (T.pts 1 - T.pts 0) d := by rw [hB]; field_simp
  have hA'Δ : A' * T.det = cross (perp d) (T.pts 2 - T.pts 0) := by rw [hA']; field_simp
  have hB'Δ : B' * T.det = cross (T.pts 1 - T.pts 0) (perp d) := by rw [hB']; field_simp
  rcases lt_trichotomy A 0 with hAn | hA0 | hAp
  · exact Or.inl (wedge_exclusion T d (perp d) A B A' B' hd hn (Or.inl hAn))
  · rcases lt_trichotomy B 0 with hBn | hB0 | hBp
    · exact Or.inl (wedge_exclusion T d (perp d) A B A' B' hd hn (Or.inr hBn))
    · exfalso
      rw [hA0, hB0] at hd0 hd1
      simp only [zero_mul, add_zero] at hd0 hd1
      rw [hd0, hd1] at hunit; norm_num at hunit
    · by_cases hA'n : A' < 0
      · exact absurd (wedge_interior T d (perp d) A B A' B' hd hn (Or.inr ⟨hA0, hA'n⟩)
          (Or.inl hBp)) hCW
      · push_neg at hA'n
        rw [hA0] at hd0 hd1
        simp only [zero_mul, zero_add] at hd0 hd1
        have hcr : cross (perp d) (T.pts 2 - T.pts 0)
            = -(B * ((T.pts 2 - T.pts 0) 0 ^ 2 + (T.pts 2 - T.pts 0) 1 ^ 2)) := by
          simp only [cross, perp_zero, perp_one]
          rw [hd0, hd1]; ring
        have hΔneg : T.det < 0 := by
          have h1 : cross (perp d) (T.pts 2 - T.pts 0) < 0 := by
            rw [hcr]; nlinarith
          rw [← hA'Δ] at h1
          by_contra hge; push_neg at hge
          have := mul_nonneg hA'n hge; linarith
        refine Or.inr ⟨2, 1, by decide, by decide, by decide, ⟨1 / B, by positivity, ?_⟩, ?_⟩
        · have hdB : d = B • (T.pts 2 - T.pts 0) := by rw [hd, hA0, zero_smul, zero_add]
          have : (1 / B) • d = T.pts 2 - T.pts 0 := by
            rw [hdB, smul_smul, one_div_mul_cancel hBp.ne', one_smul]
          rw [this]; abel
        · rw [cross_anticomm, ← hBΔ]
          have := mul_neg_of_pos_of_neg hBp hΔneg; linarith
  · rcases lt_trichotomy B 0 with hBn | hB0 | hBp
    · exact Or.inl (wedge_exclusion T d (perp d) A B A' B' hd hn (Or.inr hBn))
    · by_cases hB'n : B' < 0
      · exact absurd (wedge_interior T d (perp d) A B A' B' hd hn (Or.inl hAp)
          (Or.inr ⟨hB0, hB'n⟩)) hCW
      · push_neg at hB'n
        rw [hB0] at hd0 hd1
        simp only [zero_mul, add_zero] at hd0 hd1
        have hcr : cross (T.pts 1 - T.pts 0) (perp d)
            = A * ((T.pts 1 - T.pts 0) 0 ^ 2 + (T.pts 1 - T.pts 0) 1 ^ 2) := by
          simp only [cross, perp_zero, perp_one]
          rw [hd0, hd1]; ring
        have hΔpos : 0 < T.det := by
          have h1 : 0 < cross (T.pts 1 - T.pts 0) (perp d) := by rw [hcr]; positivity
          rw [← hB'Δ] at h1
          by_contra hge; push_neg at hge
          have := mul_nonpos_of_nonneg_of_nonpos hB'n hge; linarith
        refine Or.inr ⟨1, 2, by decide, by decide, by decide, ⟨1 / A, by positivity, ?_⟩, ?_⟩
        · have hdA : d = A • (T.pts 1 - T.pts 0) := by rw [hd, hB0, zero_smul, add_zero]
          have : (1 / A) • d = T.pts 1 - T.pts 0 := by
            rw [hdA, smul_smul, one_div_mul_cancel hAp.ne', one_smul]
          rw [this]; abel
        · rw [← hAΔ]; positivity
    · exact absurd (wedge_interior T d (perp d) A B A' B' hd hn (Or.inl hAp) (Or.inl hBp)) hCW

/-! ## 9. Assembly: the clockwise wedge, the uniform `δ`, the theorem -/

/-- A uniform `δ` over a finite family of `δ`-monotone properties. -/
theorem exists_uniform_delta {ι : Type*} (F : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ i (δ δ' : ℝ), δ' ≤ δ → P i δ → P i δ')
    (h : ∀ i ∈ F, ∃ δ : ℝ, 0 < δ ∧ P i δ) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ F, P i δ := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a F _ ih =>
    obtain ⟨δ₁, hδ₁, hP₁⟩ := h a (Finset.mem_insert_self a F)
    obtain ⟨δ₂, hδ₂, hP₂⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hmono _ _ _ (min_le_left _ _) hP₁
    · exact hmono _ _ _ (min_le_right _ _) (hP₂ i hi)

/-- Relabelling the vertices does not move the carrier. -/
theorem relabel_carrier (T : Tri) (τ : Equiv.Perm (Fin 3)) : (T.relabel τ).carrier = T.carrier := by
  show convexHull ℝ (Set.range (T.pts ∘ τ)) = convexHull ℝ (Set.range T.pts)
  rw [τ.surjective.range_comp T.pts]

/-- **The clockwise wedge at `v` cannot lie inside an unplaced tile** when it misses the unfilled
region: it would be an open set inside the placed tiles' frontiers. -/
theorem not_cw_wedge_interior {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) {v d : Plane}
    (hunit : d 0 ^ 2 + d 1 ^ 2 = 1)
    (hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      v + t • (d - s • perp d) ∉ unfilled D S)
    {j : Fin N} (hj : j ∉ S) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      v + t • (d - s • perp d) ∈ interior (D.tile j).carrier := by
  rintro ⟨δ₁, hδ₁, hint⟩
  obtain ⟨δ₂, hδ₂, hbl⟩ := hblocked
  set δ := min δ₁ δ₂ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hδ1 : δ ≤ δ₁ := min_le_left _ _
  have hδ2 : δ ≤ δ₂ := min_le_right _ _
  -- the two coordinates of `p - v` in the frame `(d, perp d)`
  set f₁ : Plane → ℝ := fun p => d 0 * (p 0 - v 0) + d 1 * (p 1 - v 1) with hf₁
  set f₂ : Plane → ℝ := fun p => d 0 * (p 1 - v 1) - d 1 * (p 0 - v 0) with hf₂
  have h0 : Continuous fun q : Plane => q 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have h1 : Continuous fun q : Plane => q 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have hc₁ : Continuous f₁ := by rw [hf₁]; fun_prop
  have hc₂ : Continuous f₂ := by rw [hf₂]; fun_prop
  set W : Set Plane := {p | 0 < f₁ p} ∩ {p | f₁ p < δ} ∩ {p | -δ * f₁ p < f₂ p} ∩ {p | f₂ p < 0}
    with hW
  have hWopen : IsOpen W :=
    (((isOpen_lt continuous_const hc₁).inter (isOpen_lt hc₁ continuous_const)).inter
      (isOpen_lt (continuous_const.mul hc₁) hc₂)).inter (isOpen_lt hc₂ continuous_const)
  have hWne : W.Nonempty := by
    refine ⟨v + (δ / 2) • (d - (δ / 2) • perp d), ?_⟩
    have e1 : f₁ (v + (δ / 2) • (d - (δ / 2) • perp d)) = δ / 2 := by
      simp only [hf₁, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, perp_zero,
        perp_one]
      linear_combination (δ / 2) * hunit
    have e2 : f₂ (v + (δ / 2) • (d - (δ / 2) • perp d)) = -(δ / 2) ^ 2 := by
      simp only [hf₂, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, perp_zero,
        perp_one]
      linear_combination (-(δ / 2) ^ 2) * hunit
    simp only [hW, Set.mem_inter_iff, Set.mem_setOf_eq, e1, e2]
    refine ⟨⟨⟨by positivity, by linarith⟩, by nlinarith⟩, by nlinarith⟩
  refine not_isOpen_subset_frontiers D S hWopen hWne ?_
  intro p hp
  simp only [hW, Set.mem_inter_iff, Set.mem_setOf_eq] at hp
  obtain ⟨⟨⟨ht0, htδ⟩, hu1⟩, hu2⟩ := hp
  set t := f₁ p with ht
  set u := f₂ p with hu
  have hs0 : 0 < -u / t := div_pos (by linarith) ht0
  have hsδ : -u / t < δ := by rw [div_lt_iff₀ ht0]; linarith
  have htu : t * (-u / t) = -u := by field_simp
  have hpt : p = v + t • (d - (-u / t) • perp d) := by
    refine plane_ext ?_ ?_
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, perp_zero, perp_one]
      have e : t * (d 0 - (-u / t) * (-(d 1))) = t * d 0 - u * d 1 := by
        field_simp
      rw [e]
      simp only [ht, hu, hf₁, hf₂]
      linear_combination (-(p 0 - v 0)) * hunit
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, perp_zero, perp_one]
      have e : t * (d 1 - (-u / t) * d 0) = t * d 1 + u * d 0 := by
        field_simp; ring
      rw [e]
      simp only [ht, hu, hf₁, hf₂]
      linear_combination (-(p 1 - v 1)) * hunit
  have hpint : p ∈ interior (D.tile j).carrier := by
    rw [hpt]; exact hint t (-u / t) ht0 (by linarith) hs0 (by linarith)
  have hpU : p ∉ unfilled D S := by
    rw [hpt]; exact hbl t (-u / t) ht0 (by linarith) hs0 (by linarith)
  have hpt' : p ∈ D.target.carrier :=
    Erdos634.BaseSelection.tile_subset_target D j (interior_subset hpint)
  have hpl : p ∈ ⋃ i ∈ S, (D.tile i).carrier := by
    by_contra hn; exact hpU ⟨hpt', hn⟩
  exact mem_frontier_of_mem_interior_unplaced D S hj hpint hpl

/-- **PLACEMENT COMPLETENESS.**  At a lexicographically least point `v` of the closure of the
unfilled region, with `d` the unit direction of the clockwise boundary ray (counter-clockwise
side free, clockwise wedge blocked), some **unplaced** tile has a vertex at `v`, a second vertex
on the ray `v + ℝ₊·d`, and its third vertex strictly counter-clockwise of `d`. -/
theorem placement_completeness {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) (v d : Plane)
    (hunit : d 0 ^ 2 + d 1 ^ 2 = 1)
    (hlex : ∀ p ∈ closure (unfilled D S), LexLE v p)
    (hfree : ∀ ε : ℝ, 0 < ε → ∃ t s : ℝ, 0 < t ∧ t < ε ∧ 0 < s ∧ s < ε ∧
      v + t • (d + s • perp d) ∈ unfilled D S)
    (hblocked : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      v + t • (d - s • perp d) ∉ unfilled D S) :
    ∃ j, j ∉ S ∧ ∃ k₀ k₁ k₂ : Fin 3, k₀ ≠ k₁ ∧ k₀ ≠ k₂ ∧ k₁ ≠ k₂ ∧
      (D.tile j).pts k₀ = v ∧
      (∃ c : ℝ, 0 < c ∧ (D.tile j).pts k₁ = v + c • d) ∧
      0 < cross d ((D.tile j).pts k₂ - v) := by
  classical
  by_contra hcon
  -- every unplaced tile is avoided by the counter-clockwise near-`d` points
  have hexcl : ∀ j ∈ (Finset.univ.filter fun j => j ∉ S), ∃ δ : ℝ, 0 < δ ∧
      ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
        v + t • (d + s • perp d) ∉ (D.tile j).carrier := by
    intro j hj
    have hj : j ∉ S := by simpa using hj
    by_cases hvj : v ∈ (D.tile j).carrier
    · obtain ⟨k, hk⟩ := unplaced_corner_at_lexmin D S hlex hj hvj
      set T := (D.tile j).relabel (Equiv.addRight k) with hT
      have hT0 : T.pts 0 = v := by rw [hT, Tri.relabel_pts]; simpa using hk
      have hTc : T.carrier = (D.tile j).carrier := relabel_carrier _ _
      have hCW := not_cw_wedge_interior D S hunit hblocked hj
      rw [← hT0, ← hTc] at hCW
      rcases corner_edge_dichotomy T d hunit hCW with ⟨δ, hδ, hex⟩ |
        ⟨k₁, k₂, h1, h2, h12, ⟨c, hc, hk₁⟩, hk₂⟩
      · refine ⟨δ, hδ, fun t s ht htδ hs hsδ => ?_⟩
        have := hex t s ht htδ hs hsδ
        rwa [hT0, hTc] at this
      · exfalso
        apply hcon
        refine ⟨j, hj, (Equiv.addRight k) 0, (Equiv.addRight k) k₁, (Equiv.addRight k) k₂,
          (Equiv.addRight k).injective.ne (Ne.symm h1),
          (Equiv.addRight k).injective.ne (Ne.symm h2),
          (Equiv.addRight k).injective.ne h12, ?_, ⟨c, hc, ?_⟩, ?_⟩
        · exact hT0
        · rw [← hT0]; exact hk₁
        · rw [← hT0]; exact hk₂
    · obtain ⟨ρ, hρ, hball⟩ :=
        Metric.isOpen_iff.mp (D.tile j).isCompact.isClosed.isOpen_compl v hvj
      refine ⟨min 1 (ρ / 2), by positivity, fun t s ht htδ hs hsδ => ?_⟩
      have ht1 : t < ρ / 2 := lt_of_lt_of_le htδ (min_le_right _ _)
      have hs1 : s < 1 := lt_of_lt_of_le hsδ (min_le_left _ _)
      have hdist : dist (v + t • (d + s • perp d)) v < ρ := by
        have hsq : dist (v + t • (d + s • perp d)) v ^ 2 = t ^ 2 * (1 + s ^ 2) := by
          rw [dist_sq_coord]
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, perp_zero, perp_one]
          linear_combination (t ^ 2 * (1 + s ^ 2)) * hunit
        have hlt : dist (v + t • (d + s • perp d)) v ^ 2 < ρ ^ 2 := by
          rw [hsq]
          have h1 : t ^ 2 < (ρ / 2) ^ 2 := by nlinarith
          have h2 : s ^ 2 < 1 := by nlinarith
          have h3 : t ^ 2 * (1 + s ^ 2) < t ^ 2 * 2 :=
            mul_lt_mul_of_pos_left (by linarith) (by positivity)
          nlinarith
        nlinarith [dist_nonneg (x := v + t • (d + s • perp d)) (y := v)]
      exact hball (Metric.mem_ball.mpr hdist)
  obtain ⟨δ, hδ, hall⟩ := exists_uniform_delta (Finset.univ.filter fun j => j ∉ S)
    (fun j δ => ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      v + t • (d + s • perp d) ∉ (D.tile j).carrier)
    (fun j δ δ' hle h t s ht htδ hs hsδ => h t s ht (lt_of_lt_of_le htδ hle) hs
      (lt_of_lt_of_le hsδ hle))
    hexcl
  obtain ⟨t, s, ht, htδ, hs, hsδ, hq⟩ := hfree δ hδ
  obtain ⟨j, hj, hqj⟩ := exists_unplaced_of_mem_unfilled D S hq
  exact hall j (by simp [hj]) t s ht htδ hs hsδ hqj

end Erdos634.PlacementCompleteness

#print axioms Erdos634.PlacementCompleteness.placement_completeness
