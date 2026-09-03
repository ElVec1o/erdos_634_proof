import Erdos634.RouteOneThroughEdge

/-!
# The `[V,E]` dichotomy, and the straight-angle count at a junction

Split out of `RouteOneThroughEdge.lean` (Lean rule 2.3's file-length guideline) — the concluding
two sections: `rem:route1uniform`'s `[V,E]` dichotomy itself, built from `edge_length_mem_model` and
`overshoot_dichotomy`, and the general (non-route-1-specific) consequence that at most one tile can
carry a straight angle at an interior point once some tile there does not.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RouteOne

open Erdos634.Geometry

/-! ## The `[V,E]` dichotomy itself

`rem:route1uniform` reduces route 1 to one question: *what covers the segment `[V,E]` of length
exactly `a`?*  With the flank in hand the answer is forced.  The flank gives a horizontal rightward
edge of the serving tile from `V`; congruence forces its length to be one of the model's three
sides; and `a < b < c`.  So either that length is exactly `a` — `E` is the edge's far endpoint, a
junction, and the march advances — or the length exceeds `a` and `E` lies strictly inside the edge,
which is the tile-interior blocking whose failure defined the escape, so the branch dies.

Nothing here assumes a straight angle anywhere. -/

/-- **A tile's edge length is one of the model's three sides.** -/
theorem edge_length_mem_model {N : ℕ} (D : CongruentDissection N) (i : Fin N) (m : Fin 3) :
    dist ((D.tile i).pts m) ((D.tile i).pts (m + 1))
      ∈ ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
          dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) := by
  have hcong := (D.tiles_congruent i).sideMultiset_eq
  have hshift := _root_.Tri.sideMultiset_shift (D.tile i) m
  have hmem : dist ((D.tile i).pts m) ((D.tile i).pts (m + 1))
      ∈ ({dist ((D.tile i).pts m) ((D.tile i).pts (m+1)),
          dist ((D.tile i).pts (m+2)) ((D.tile i).pts m),
          dist ((D.tile i).pts (m+1)) ((D.tile i).pts (m+2))} : Multiset ℝ) := by
    simp
  rw [hshift, hcong] at hmem
  exact hmem

/-- **A horizontal rightward edge has length equal to its `x`-offset.** -/
theorem dist_eq_x_of_horizontal {V W : Plane} (hy : (W - V) 1 = 0) (hx : 0 < (W - V) 0) :
    dist V W = (W - V) 0 := by
  have hyc : W 1 - V 1 = 0 := by simpa only [PiLp.sub_apply] using hy
  have hxc : 0 < W 0 - V 0 := by simpa only [PiLp.sub_apply] using hx
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h1 : ‖(V - W) 1‖ ^ 2 = 0 := by
    simp only [PiLp.sub_apply, Real.norm_eq_abs]
    have : V 1 - W 1 = 0 := by linarith
    rw [this]; simp
  have h0 : ‖(V - W) 0‖ ^ 2 = ((W - V) 0) ^ 2 := by
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    ring
  rw [h0, h1, add_zero, Real.sqrt_sq (le_of_lt hx)]

/-- **The `[V,E]` dichotomy.**  For a tile of a congruent dissection whose model has sides
`f`, `f²-1`, `f²` (the base-`β` family at `e = 1`, in the scaling of `rem:route1uniform`), a
horizontal rightward edge from `V` either has length exactly `a = f` — so its far endpoint is `E`
and `E` is a junction — or its length exceeds `f`, so the point at distance `f` lies strictly inside
it and the escape is blocked. -/
theorem VE_dichotomy {N : ℕ} (D : CongruentDissection N) (i : Fin N) (V W : Plane) (m : Fin 3)
    (hV : (D.tile i).pts m = V) (hW : (D.tile i).pts (m + 1) = W)
    (hy : (W - V) 1 = 0) (hx : 0 < (W - V) 0)
    (f : ℝ) (hf : 2 ≤ f)
    (hmodel : ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
                dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) = {f, f ^ 2 - 1, f ^ 2}) :
    (W - V) 0 = f ∨ f < (W - V) 0 := by
  have hmem := edge_length_mem_model D i m
  rw [hmodel, hV, hW] at hmem
  rw [dist_eq_x_of_horizontal hy hx] at hmem
  have hcases : (W - V) 0 = f ∨ (W - V) 0 = f ^ 2 - 1 ∨ (W - V) 0 = f ^ 2 := by
    simpa using hmem
  exact overshoot_dichotomy f ((W - V) 0) hf hcases

/-- **The other neighbour's edge length is likewise one of the model's sides.** -/
theorem edge_length_mem_model' {N : ℕ} (D : CongruentDissection N) (i : Fin N) (m : Fin 3) :
    dist ((D.tile i).pts m) ((D.tile i).pts (m + 2))
      ∈ ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
          dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) := by
  have hcong := (D.tiles_congruent i).sideMultiset_eq
  have hshift := _root_.Tri.sideMultiset_shift (D.tile i) m
  have hmem : dist ((D.tile i).pts (m + 2)) ((D.tile i).pts m)
      ∈ ({dist ((D.tile i).pts m) ((D.tile i).pts (m+1)),
          dist ((D.tile i).pts (m+2)) ((D.tile i).pts m),
          dist ((D.tile i).pts (m+1)) ((D.tile i).pts (m+2))} : Multiset ℝ) := by
    simp
  rw [hshift, hcong] at hmem
  rw [dist_comm ((D.tile i).pts m) ((D.tile i).pts (m + 2))]
  exact hmem

/-- **The `[V,E]` dichotomy, for whichever neighbour the flank returns.**  This is the form that
composes directly with `route_one_flank_of_vertices` / `flank_propagates`, whose conclusion is a
disjunction over the two neighbours of `V`. -/
theorem VE_dichotomy_of_flank {N : ℕ} (D : CongruentDissection N) (i : Fin N) (V W : Plane)
    (m : Fin 3) (hV : (D.tile i).pts m = V)
    (hW : (D.tile i).pts (m + 1) = W ∨ (D.tile i).pts (m + 2) = W)
    (hy : (W - V) 1 = 0) (hx : 0 < (W - V) 0)
    (f : ℝ) (hf : 2 ≤ f)
    (hmodel : ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
                dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) = {f, f ^ 2 - 1, f ^ 2}) :
    (W - V) 0 = f ∨ f < (W - V) 0 := by
  have hd : dist V W = (W - V) 0 := dist_eq_x_of_horizontal hy hx
  rcases hW with hW1 | hW2
  · have hmem := edge_length_mem_model D i m
    rw [hmodel, hV, hW1, hd] at hmem
    exact overshoot_dichotomy f ((W - V) 0) hf (by simpa using hmem)
  · have hmem := edge_length_mem_model' D i m
    rw [hmodel, hV, hW2, hd] at hmem
    exact overshoot_dichotomy f ((W - V) 0) hf (by simpa using hmem)

/-! ## A general consequence: the straight-angle count at a junction

`two_through_excludes_mem` is not route-1-specific.  Read as a bound it says: at an interior point
where some tile sits *without* a straight angle, at most one tile can have one.  The figure
arguments in the corpus assume that bound (`route_one_flank_composed`'s `hcard`, the `s = 1` of
`alpha_wall_figure`); here it is a theorem, proved geometrically from the angle sum, with no appeal
to the irrationality of `α` and no vertex-figure classification. -/

/-- **At most one straight angle at a junction.**  If some tile contains the interior point `p` and
does *not* have a straight angle there, then at most one tile has a straight angle at `p`: two would
already exhaust the `2π` and leave no room for that tile. -/
theorem pi_count_le_one {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ interior D.target.carrier) (k : Fin N) (hk : p ∈ (D.tile k).carrier)
    (hknot : (D.tile k).localAngle p ≠ Real.pi) :
    ({i | (D.tile i).localAngle p = Real.pi} : Finset (Fin N)).card ≤ 1 := by
  classical
  by_contra hc
  push_neg at hc
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hik : i ≠ k := fun h => hknot (h ▸ hi)
  have hjk : j ≠ k := fun h => hknot (h ▸ hj)
  exact two_through_excludes_mem D hp i j k hij hik hjk hi hj hk

/-- **The `π`-count is exactly one**, given a tile that carries the straight angle and a tile that
does not.  This is `route_one_flank_composed`'s `hcard` — so of the pair `hcard`/`hb` that made up
`conj:advance`'s case (a) in the old chain, only `hb` was ever an independent assumption. -/
theorem pi_count_eq_one {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ interior D.target.carrier) (b k : Fin N)
    (hb : (D.tile b).localAngle p = Real.pi)
    (hk : p ∈ (D.tile k).carrier) (hknot : (D.tile k).localAngle p ≠ Real.pi) :
    ({i | (D.tile i).localAngle p = Real.pi} : Finset (Fin N)).card = 1 := by
  classical
  have hle := pi_count_le_one D hp k hk hknot
  have hpos : 1 ≤ ({i | (D.tile i).localAngle p = Real.pi} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨b, by simp [hb]⟩
  omega


end Erdos634.RouteOne
