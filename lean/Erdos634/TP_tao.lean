import Erdos634.Dissection
import Erdos634.TileAdjacency
import Erdos634.LineParam
import Erdos634.CollarAssembleM4

/-!
# Darts of a general dissection, and CONSTANCY of the tile pair along a dart

Erdős #634, room `tileplace`, mode TAO.  Target: for a **general** `Dissection N`, define the
arrangement refinement — the vertex set `V`, the darts (maximal sub-segments of a tile side whose
relative interior misses `V`) — and prove **CONSTANCY**: the unordered pair of tiles meeting along a
dart is the same at every point of the dart's relative interior.  `TP_gonthier.lean` verifies this
refinement by `decide` on the certified `N = 44` instance (162 darts, 81 edge orbits); this file
proves the general statements it is a special case of.

## The reformulation that made it work

Mathlib has nothing about "maximal subintervals of a segment avoiding a finite set", and doing it in
the plane would need a decidable order on `Plane`.  The trick the room brief guessed is the whole
trick: **parametrise**.  A tile side is `edgeMap D i k = AffineMap.lineMap (pts k) (pts (k+1))`,
which is injective; pull `D.vertexSet` (already in `Dissection.lean`, already known finite) back
along it to a finite `Finset ℝ`, `Finset.sort` it, and

> a maximal vertex-free sub-segment **is** a consecutive pair of the sorted list.

Consequences, all realised below: **no `DecidableEq` on `Plane` is used anywhere**; the only
decidability is `Classical` on `ℝ` (`Finset.sort`, `Set.Finite.toFinset`, `Finset.filter`).  And
maximality turns out to be *unnecessary for constancy* — constancy holds for every vertex-free
sub-segment, maximal or not — which is why `Dart` below carries vertex-freeness and not maximality,
and why the edge involution comes out with no extra work.

## What is proved (Rule 0 labels; all VERIFIED = Lean statement is the statement)

Geometry (all VERIFIED, axiom-clean, no `sorry`):

* `edge_vector_parallel` — two tiles meeting at a non-vertex edge point have collinear sides.
  (`Dissection.leftDir_antiparallel` with the `Tri.leftDir` sign convention stripped.)
* `partner_side_param` — the partner tile's side is the affine reparametrisation `r ↦ p + r·δ` of
  this one, and it spans the whole closed dart.  This is the geometric heart.
* `onEdge_propagate` — `OnEdge D · j` propagates from one interior parameter of a vertex-free
  sub-segment to every other.
* **`onEdge_set_constant`, `dartTiles_constant`, `Dart.tiles_constant` — CONSTANCY.**  The *set* of
  tiles meeting the side is constant along the dart.  Note: **no interiority hypothesis** — this
  holds for boundary darts too.
* `dartTiles_card_two`, `dartTiles_card_two_of_interior` — at a dart point interior to the target
  the set has exactly two members, i.e. it is the unordered *pair*.
* `otherTile_constant` — `TileAdjacency.otherTile` is constant along a dart.

Combinatorics of the refinement (all VERIFIED):

* `vertexParams_finite`, `edgeSplit` — the sorted split list of a side.
* `edgeSplit_gap_vertexFree` — consecutive split points bound a vertex-free open interval.
* `edgeSplit_covers`, `edgeSplit_covers_strict` — the closed darts cover `[0,1]`, and every
  non-vertex parameter is in the *open* part of one.  Together with the previous item this is
  maximality.
* `two_le_edgeSplit_length`, `exists_dart`, `sideDart`, `exists_dart_containing` — every side of
  every tile of every dissection carries at least one dart, and every non-vertex point of it lies in
  the relative interior of one.
* `vertexFinset_card_le`, `edgeSplit_length_le` — at most `3N` tiling vertices, hence at most `3N`
  split points per side, hence at most `3N − 1` darts per side and `≤ 3N(3N−1)` in total.  This
  bound is quadratic and loose: the true count is `3N + #(strict vertex-in-side incidences)`, which
  is `132 + 13 = 145` on the `N = 44` instance against a bound of `17292`.

  **A LINEAR bound `≤ 9N` is reachable and its local ingredient already exists — do not rebuild
  it.**  `PinPlumbing.at_most_two_through` (with `PinPlumbing.pin_angle_sum_interior`) proves that
  no three distinct tiles have local angle `π` at a common interior point; a tile with `v` in the
  relative interior of one of its sides has exactly that local angle (`Tri.localAngle_frontier`),
  and unlike `Dissection.two_tiles_at_edge_point` the angle-sum route does **not** exclude tiling
  vertices.  So each tiling vertex lies strictly inside at most two tile sides, giving
  `Σ (splitpoints) ≤ 6N + 2·3N` and `#darts ≤ 9N`.  What is missing is only the `Finset` double
  count over incidences (`Finset.card_eq_sum_card_fiberwise`), costed in the report.

Beyond the target (VERIFIED):

* `exists_partner_dart`, `exists_partner_dart_of_interior` — **the edge involution `α`**: at an
  interior dart, a *different* tile carries a dart with exactly the same relative interior.  This is
  the well-definedness, on a general dissection, of what `TP_gonthier.alphaT` verifies by `decide`
  at `N = 44`.

## Satisfiability

`witness_delta4` exhibits, for the corpus's concrete `delta4Dissection : Dissection 176`, a dart on
every side of every tile with nonempty relative interior on which the tile set is constant.  Nothing
here is vacuous.  `ball_of_mem_interior` shows the ball hypothesis of the pair statements is implied
by interiority, so the only genuinely extra hypothesis in `dartTiles_card_two_of_interior` and
`exists_partner_dart_of_interior` is that the dart meets the target's interior — satisfied by all
`81` interior edge orbits of the `N = 44` instance, not proved to be satisfiable for a general
dissection here.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace Erdos634.TPTao

open Erdos634.Geometry Set

variable {N : ℕ}

/-- The affine parametrisation of tile `i`'s side `k` by `[0,1]`. -/
noncomputable def edgeMap (D : Dissection N) (i : Fin N) (k : Fin 3) : ℝ → Plane :=
  AffineMap.lineMap ((D.tile i).pts k) ((D.tile i).pts (k + 1))

theorem edgeMap_apply (D : Dissection N) (i : Fin N) (k : Fin 3) (t : ℝ) :
    edgeMap D i k t
      = t • ((D.tile i).pts (k + 1) - (D.tile i).pts k) + (D.tile i).pts k := by
  simp [edgeMap, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]

@[simp] theorem edgeMap_zero (D : Dissection N) (i : Fin N) (k : Fin 3) :
    edgeMap D i k 0 = (D.tile i).pts k := by
  simp [edgeMap]

@[simp] theorem edgeMap_one (D : Dissection N) (i : Fin N) (k : Fin 3) :
    edgeMap D i k 1 = (D.tile i).pts (k + 1) := by
  simp [edgeMap]

theorem pts_ne_succ (T : Tri) (k : Fin 3) : T.pts k ≠ T.pts (k + 1) := by
  have hsucc : ∀ j : Fin 3, j ≠ j + 1 := by decide
  exact fun h => hsucc k (T.indep.injective h)

theorem edgeMap_injective (D : Dissection N) (i : Fin N) (k : Fin 3) :
    Function.Injective (edgeMap D i k) :=
  LineParam.lineMap_injective_of_ne (pts_ne_succ (D.tile i) k)

theorem edgeMap_mem_edge (D : Dissection N) (i : Fin N) (k : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) : edgeMap D i k t ∈ (D.tile i).edge k := by
  rw [Tri.edge, segment_eq_image_lineMap]
  exact ⟨t, ht, rfl⟩

theorem pts_mem_vertexSet (D : Dissection N) (i : Fin N) (k : Fin 3) :
    (D.tile i).pts k ∈ D.vertexSet :=
  Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k, rfl⟩⟩

/-- A non-vertex point of a side of tile `i` is `OnEdge` for tile `i`. -/
theorem onEdge_self (D : Dissection N) (i : Fin N) (k : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hV : edgeMap D i k t ∉ D.vertexSet) :
    OnEdge D (edgeMap D i k t) i := by
  obtain ⟨hz, hp⟩ :=
    (D.tile i).onEdge_data (edgeMap_mem_edge D i k ht) (D.notMem_vertexSet hV i)
  exact ⟨k + 2, hz, hp⟩


/-! ## The collinearity step -/

/-- **Two tiles meeting at a non-vertex edge point have collinear sides.**  `leftDir_antiparallel`
says the two left-hand directions are negative multiples of each other; stripping the sign
convention of `Tri.leftDir` leaves a nonzero scalar relating the two edge vectors. -/
theorem edge_vector_parallel (D : Dissection N) {i j : Fin N} (hji : j ≠ i) {k m : Fin 3}
    {x : Plane}
    (hz₁ : (D.tile i).basis.coord (k + 2) x = 0)
    (hp₁ : ∀ l, l ≠ k + 2 → 0 < (D.tile i).basis.coord l x)
    (hz₂ : (D.tile j).basis.coord m x = 0)
    (hp₂ : ∀ l, l ≠ m → 0 < (D.tile j).basis.coord l x) :
    ∃ δ : ℝ, δ ≠ 0 ∧
      (D.tile j).pts (m + 1 + 1) - (D.tile j).pts (m + 1)
        = δ • ((D.tile i).pts (k + 1) - (D.tile i).pts k) := by
  obtain ⟨c, hcneg, hc⟩ := D.leftDir_antiparallel hji hz₂ hp₂ hz₁ hp₁
  have hkk : (k + 2 + 1 : Fin 3) = k := by fin_cases k <;> rfl
  rw [hkk] at hc
  have hcne : c ≠ 0 := ne_of_lt hcneg
  have hncne : -c ≠ 0 := by simpa using hcne
  -- `hc : leftDir i k = c • leftDir j (m+1)`
  have key : ∀ γ : ℝ, γ ≠ 0 →
      (D.tile i).pts (k + 1) - (D.tile i).pts k
        = γ • ((D.tile j).pts (m + 1 + 1) - (D.tile j).pts (m + 1)) →
      ∃ δ : ℝ, δ ≠ 0 ∧
        (D.tile j).pts (m + 1 + 1) - (D.tile j).pts (m + 1)
          = δ • ((D.tile i).pts (k + 1) - (D.tile i).pts k) := by
    intro γ hγ h
    refine ⟨γ⁻¹, inv_ne_zero hγ, ?_⟩
    rw [h, smul_smul, inv_mul_cancel₀ hγ, one_smul]
  rcases (D.tile i).leftDir_eq_or k with h1 | h1 <;>
    rcases (D.tile j).leftDir_eq_or (m + 1) with h2 | h2 <;> rw [h1, h2] at hc
  · exact key c hcne (by linear_combination (norm := module) hc)
  · exact key (-c) hncne (by linear_combination (norm := module) hc)
  · exact key (-c) hncne (by linear_combination (norm := module) (-1 : ℝ) • hc)
  · exact key c hcne (by linear_combination (norm := module) (-1 : ℝ) • hc)

/-! ## The propagation step: `OnEdge` is constant along a vertex-free sub-segment -/

/-- **The partner side, in the dart's own parameter.**  If a tile `j ≠ i` meets tile `i`'s side `k`
at an interior parameter `s` of a vertex-free sub-interval `(lo,hi)`, then one of `j`'s sides is
carried by the SAME line, its parametrisation is the affine reparametrisation `r ↦ p + r·δ` of tile
`i`'s, and the closed interval `[lo,hi]` sits inside the image of `[0,1]`.

This is the whole geometric content: `edge_vector_parallel` gives collinearity, the endpoints of
`j`'s side are tiling vertices so their parameters miss the open dart, and `s` lies between them. -/
theorem partner_side_param (D : Dissection N) {i j : Fin N} (hji : j ≠ i) {k : Fin 3}
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hvf : ∀ t ∈ Ioo lo hi, edgeMap D i k t ∉ D.vertexSet)
    {s : ℝ} (hs : s ∈ Ioo lo hi) (hj : OnEdge D (edgeMap D i k s) j) :
    ∃ (m : Fin 3) (p δ : ℝ), δ ≠ 0 ∧
      (∀ r : ℝ, edgeMap D j (m + 1) r = edgeMap D i k (p + r * δ)) ∧
      min p (p + δ) ≤ lo ∧ hi ≤ max p (p + δ) := by
  classical
  have hsIcc : s ∈ Icc (0:ℝ) 1 := ⟨le_trans hlo hs.1.le, le_trans hs.2.le hhi⟩
  have hxV := hvf s hs
  have hnv := D.notMem_vertexSet hxV
  obtain ⟨hz₁, hp₁⟩ :=
    (D.tile i).onEdge_data (edgeMap_mem_edge D i k hsIcc) (hnv i)
  obtain ⟨m, hz₂, hp₂⟩ := hj
  obtain ⟨δ, hδ, hdJ⟩ := edge_vector_parallel D hji hz₁ hp₁ hz₂ hp₂
  have hxj : edgeMap D i k s ∈ (D.tile j).edge (m + 1) :=
    (D.tile j).mem_edge_of_coord_zero hz₂ hp₂
  rw [Tri.edge, segment_eq_image_lineMap] at hxj
  obtain ⟨θ, hθ, hθx⟩ := hxj
  set p : ℝ := s - θ * δ with hpdef
  have hA : (D.tile j).pts (m + 1) = edgeMap D i k p := by
    have h := hθx
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at h
    rw [hdJ] at h
    rw [edgeMap_apply] at h ⊢
    rw [hpdef]
    linear_combination (norm := module) h
  -- the affine reparametrisation
  have hrep : ∀ r : ℝ, edgeMap D j (m + 1) r = edgeMap D i k (p + r * δ) := by
    intro r
    have h1 : edgeMap D j (m + 1) r
        = r • ((D.tile j).pts (m + 1 + 1) - (D.tile j).pts (m + 1)) + (D.tile j).pts (m + 1) :=
      edgeMap_apply D j (m + 1) r
    rw [h1, hdJ, hA, edgeMap_apply, edgeMap_apply]
    module
  have hB : (D.tile j).pts (m + 1 + 1) = edgeMap D i k (p + δ) := by
    have := hrep 1
    rw [show (1:ℝ) * δ = δ by ring] at this
    rw [← this, edgeMap_apply]
    simp
  refine ⟨m, p, δ, hδ, hrep, ?_, ?_⟩ <;>
    [skip; skip]
  all_goals {
    have hpnot : p ∉ Ioo lo hi := fun hmem =>
      hvf p hmem (hA ▸ pts_mem_vertexSet D j (m + 1))
    have hqnot : p + δ ∉ Ioo lo hi := fun hmem =>
      hvf (p + δ) hmem (hB ▸ pts_mem_vertexSet D j (m + 1 + 1))
    have hs' : s = p + θ * δ := by rw [hpdef]; ring
    have hsbetween : min p (p + δ) ≤ s ∧ s ≤ max p (p + δ) := by
      rcases lt_or_gt_of_ne hδ with hneg | hpos
      · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        constructor <;> nlinarith [hθ.1, hθ.2]
      · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        constructor <;> nlinarith [hθ.1, hθ.2]
    first
    | (by_contra hcon
       rw [not_le] at hcon
       have hmem : min p (p + δ) ∈ Ioo lo hi := ⟨hcon, lt_of_le_of_lt hsbetween.1 hs.2⟩
       rcases min_choice p (p + δ) with h | h
       · exact hpnot (h ▸ hmem)
       · exact hqnot (h ▸ hmem))
    | (by_contra hcon
       rw [not_le] at hcon
       have hmem : max p (p + δ) ∈ Ioo lo hi := ⟨lt_of_lt_of_le hs.1 hsbetween.2, hcon⟩
       rcases max_choice p (p + δ) with h | h
       · exact hpnot (h ▸ hmem)
       · exact hqnot (h ▸ hmem)) }

/-- **Propagation.**  Let `[lo,hi] ⊆ [0,1]` be a sub-interval of the parameter interval of tile
`i`'s side `k` whose *open* part carries no tiling vertex.  If some other tile `j` meets the side at
one interior parameter `s`, it meets it at **every** interior parameter `t`.

The proof is the sketch of the room brief, with no new geometry: `partner_side_param` puts tile
`j`'s side on the same line and shows it spans the whole closed dart; a non-vertex point of a side
is `OnEdge` by `Tri.onEdge_data`. -/
theorem onEdge_propagate (D : Dissection N) {i j : Fin N} (hji : j ≠ i) {k : Fin 3}
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hvf : ∀ t ∈ Ioo lo hi, edgeMap D i k t ∉ D.vertexSet)
    {s : ℝ} (hs : s ∈ Ioo lo hi) (hj : OnEdge D (edgeMap D i k s) j)
    {t : ℝ} (ht : t ∈ Ioo lo hi) :
    OnEdge D (edgeMap D i k t) j := by
  obtain ⟨m, p, δ, hδ, hrep, hminlo, hhimax⟩ :=
    partner_side_param D hji hlo hhi hvf hs hj
  have hA : (D.tile j).pts (m + 1) = edgeMap D i k p := by
    have := hrep 0
    rw [show (0:ℝ) * δ = 0 by ring, add_zero] at this
    rw [← this, edgeMap_apply]; simp
  have hB : (D.tile j).pts (m + 1 + 1) = edgeMap D i k (p + δ) := by
    have := hrep 1
    rw [show (1:ℝ) * δ = δ by ring] at this
    rw [← this, edgeMap_apply]; simp
  have htmem : t ∈ Icc (min p (p + δ)) (max p (p + δ)) :=
    ⟨le_trans hminlo ht.1.le, le_trans ht.2.le hhimax⟩
  have hseg := LineParam.mem_segment_lineMap_of_mem_Icc
    ((D.tile i).pts k) ((D.tile i).pts (k + 1)) (min_le_max) htmem
  have hedge : edgeMap D i k t ∈ (D.tile j).edge (m + 1) := by
    rw [Tri.edge, hA, hB]
    rcases le_total p (p + δ) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hseg
      exact hseg
    · rw [min_eq_right hle, max_eq_left hle] at hseg
      rw [segment_symm]
      exact hseg
  obtain ⟨hz, hp⟩ :=
    (D.tile j).onEdge_data hedge (D.notMem_vertexSet (hvf t ht) j)
  exact ⟨m + 1 + 2, hz, hp⟩

/-! ## CONSTANCY -/

open scoped Classical in
/-- The set of tiles meeting tile `i`'s side `k` at parameter `t`, as a `Finset`. -/
noncomputable def dartTiles (D : Dissection N) (i : Fin N) (k : Fin 3) (t : ℝ) :
    Finset (Fin N) :=
  Finset.univ.filter (fun j => OnEdge D (edgeMap D i k t) j)

/-- **CONSTANCY, set form.**  Along a vertex-free open sub-segment of a tile side, the *set* of
tiles meeting the side is the same at every interior point.  No hypothesis on the target's interior
is needed: this holds for boundary sub-segments too. -/
theorem onEdge_set_constant (D : Dissection N) {i : Fin N} {k : Fin 3} {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hvf : ∀ t ∈ Ioo lo hi, edgeMap D i k t ∉ D.vertexSet)
    {s t : ℝ} (hs : s ∈ Ioo lo hi) (ht : t ∈ Ioo lo hi) :
    {j | OnEdge D (edgeMap D i k s) j} = {j | OnEdge D (edgeMap D i k t) j} := by
  have main : ∀ a b : ℝ, a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      ∀ j, OnEdge D (edgeMap D i k a) j → OnEdge D (edgeMap D i k b) j := by
    intro a b ha hb j hja
    by_cases hji : j = i
    · subst hji
      exact onEdge_self D j k ⟨le_trans hlo hb.1.le, le_trans hb.2.le hhi⟩ (hvf b hb)
    · exact onEdge_propagate D hji hlo hhi hvf ha hja hb
  ext j
  exact ⟨main s t hs ht j, main t s ht hs j⟩

/-- **CONSTANCY, `Finset` form.** -/
theorem dartTiles_constant (D : Dissection N) {i : Fin N} {k : Fin 3} {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hvf : ∀ t ∈ Ioo lo hi, edgeMap D i k t ∉ D.vertexSet)
    {s t : ℝ} (hs : s ∈ Ioo lo hi) (ht : t ∈ Ioo lo hi) :
    dartTiles D i k s = dartTiles D i k t := by
  classical
  have h := onEdge_set_constant D hlo hhi hvf hs ht
  ext j
  simp only [dartTiles, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj; exact (Set.ext_iff.mp h j).mp hj
  · intro hj; exact (Set.ext_iff.mp h j).mpr hj

open scoped Classical in
/-- **The tile set at an interior dart point has exactly two members** — the unordered pair. -/
theorem dartTiles_card_two (D : Dissection N) (hN : 0 < N) {i : Fin N} {k : Fin 3} {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hvf : ∀ t ∈ Ioo lo hi, edgeMap D i k t ∉ D.vertexSet)
    {s : ℝ} (hs : s ∈ Ioo lo hi) {R : ℝ} (hR : 0 < R)
    (hRt : Metric.ball (edgeMap D i k s) R ⊆ D.target.carrier) :
    (dartTiles D i k s).card = 2 := by
  have hself : OnEdge D (edgeMap D i k s) i :=
    onEdge_self D i k ⟨le_trans hlo hs.1.le, le_trans hs.2.le hhi⟩ (hvf s hs)
  exact (D.two_tiles_at_edge_point hN (D.notMem_vertexSet (hvf s hs)) hR hRt
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hself⟩⟩).1

/-- **CONSTANCY for the adjacency map.**  The "other tile" produced by
`TileAdjacency.otherTile` is the same at every interior point of a vertex-free sub-segment. -/
theorem otherTile_constant (D : Dissection N) (hN : 0 < N) {i : Fin N} {k : Fin 3} {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hvf : ∀ t ∈ Ioo lo hi, edgeMap D i k t ∉ D.vertexSet)
    {s t : ℝ} (hs : s ∈ Ioo lo hi) (ht : t ∈ Ioo lo hi)
    {Rs Rt : ℝ} (hRs : 0 < Rs) (hRt : 0 < Rt)
    (hRts : Metric.ball (edgeMap D i k s) Rs ⊆ D.target.carrier)
    (hRtt : Metric.ball (edgeMap D i k t) Rt ⊆ D.target.carrier)
    (his : OnEdge D (edgeMap D i k s) i) (hit : OnEdge D (edgeMap D i k t) i) :
    TileAdjacency.otherTile D hN (D.notMem_vertexSet (hvf s hs)) hRs hRts i his
      = TileAdjacency.otherTile D hN (D.notMem_vertexSet (hvf t ht)) hRt hRtt i hit := by
  have hjne :=
    TileAdjacency.otherTile_ne D hN (D.notMem_vertexSet (hvf s hs)) hRs hRts i his
  have hjE :=
    TileAdjacency.otherTile_onEdge D hN (D.notMem_vertexSet (hvf s hs)) hRs hRts i his
  have hset := onEdge_set_constant D hlo hhi hvf hs ht
  have hjEt : OnEdge D (edgeMap D i k t)
      (TileAdjacency.otherTile D hN (D.notMem_vertexSet (hvf s hs)) hRs hRts i his) :=
    (Set.ext_iff.mp hset _).mp hjE
  exact (TileAdjacency.exists_unique_other_tile D hN (D.notMem_vertexSet (hvf t ht))
    hRt hRtt i hit).choose_spec.2 _ ⟨hjne, hjEt⟩

/-! ## Darts: maximal vertex-free sub-segments as consecutive pairs in a sorted list

This is the combinatorial half.  Mathlib has no "maximal subinterval of a segment avoiding a finite
set", and building one directly in the plane would need a decidable order on `Plane`.  The
parametrisation removes the problem entirely: pull the finite vertex set back along `edgeMap` to a
finite subset of `ℝ`, sort it, and a *maximal vertex-free sub-segment is exactly a consecutive pair
of the sorted list*.  All decidability used below is `Classical` on `ℝ`; **no decidable structure on
`Plane` is required anywhere.** -/

/-- The parameters in `[0,1]` at which a tiling vertex sits on tile `i`'s side `k`. -/
def vertexParams (D : Dissection N) (i : Fin N) (k : Fin 3) : Set ℝ :=
  {t | t ∈ Icc (0:ℝ) 1 ∧ edgeMap D i k t ∈ D.vertexSet}

/-- **Finiteness — the only place the plane's finite vertex set is used.**  `edgeMap` is injective
(the two endpoints of a side are distinct), so the pullback of a finite set is finite. -/
theorem vertexParams_finite (D : Dissection N) (i : Fin N) (k : Fin 3) :
    (vertexParams D i k).Finite := by
  have hpre : (edgeMap D i k ⁻¹' D.vertexSet).Finite :=
    Set.Finite.preimage (Set.injOn_of_injective (edgeMap_injective D i k)) D.vertexSet_finite
  have hsub : vertexParams D i k ⊆ edgeMap D i k ⁻¹' D.vertexSet := fun t ht => ht.2
  exact hpre.subset hsub

noncomputable def vertexParamFinset (D : Dissection N) (i : Fin N) (k : Fin 3) : Finset ℝ :=
  (vertexParams_finite D i k).toFinset

/-- **The split points of a side, in increasing order.** -/
noncomputable def edgeSplit (D : Dissection N) (i : Fin N) (k : Fin 3) : List ℝ :=
  (vertexParamFinset D i k).sort

theorem mem_edgeSplit (D : Dissection N) (i : Fin N) (k : Fin 3) {t : ℝ} :
    t ∈ edgeSplit D i k ↔ t ∈ Icc (0:ℝ) 1 ∧ edgeMap D i k t ∈ D.vertexSet := by
  simp only [edgeSplit, Finset.mem_sort, vertexParamFinset, Set.Finite.mem_toFinset]
  rfl

theorem edgeSplit_sortedLT (D : Dissection N) (i : Fin N) (k : Fin 3) :
    StrictMono (edgeSplit D i k).get :=
  Finset.sortedLT_sort _

theorem zero_mem_edgeSplit (D : Dissection N) (i : Fin N) (k : Fin 3) :
    (0:ℝ) ∈ edgeSplit D i k :=
  (mem_edgeSplit D i k).mpr ⟨⟨le_refl _, zero_le_one⟩, by
    rw [edgeMap_zero]; exact pts_mem_vertexSet D i k⟩

theorem one_mem_edgeSplit (D : Dissection N) (i : Fin N) (k : Fin 3) :
    (1:ℝ) ∈ edgeSplit D i k :=
  (mem_edgeSplit D i k).mpr ⟨⟨zero_le_one, le_refl _⟩, by
    rw [edgeMap_one]; exact pts_mem_vertexSet D i (k + 1)⟩

theorem edgeSplit_mem_Icc (D : Dissection N) (i : Fin N) (k : Fin 3) {t : ℝ}
    (ht : t ∈ edgeSplit D i k) : t ∈ Icc (0:ℝ) 1 := ((mem_edgeSplit D i k).mp ht).1

/-- **Every side carries at least one dart**: the sorted split list has length at least two,
because it contains both `0` and `1`. -/
theorem two_le_edgeSplit_length (D : Dissection N) (i : Fin N) (k : Fin 3) :
    2 ≤ (edgeSplit D i k).length := by
  classical
  have h0 := zero_mem_edgeSplit D i k
  have h1 := one_mem_edgeSplit D i k
  have hnodup : (edgeSplit D i k).Nodup := Finset.sort_nodup _ _
  have hsub : ({0, 1} : Finset ℝ) ⊆ (edgeSplit D i k).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr h0
    · exact List.mem_toFinset.mpr h1
  have hcard : ({0, 1} : Finset ℝ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_singleton]
  have := Finset.card_le_card hsub
  rw [hcard, List.toFinset_card_of_nodup hnodup] at this
  exact this

/-- **Consecutive split points bound a vertex-free open interval** — this is exactly maximality,
in the form the constancy theorem consumes. -/
theorem edgeSplit_gap_vertexFree (D : Dissection N) (i : Fin N) (k : Fin 3) {n : ℕ}
    (h1 : n < (edgeSplit D i k).length) (h2 : n + 1 < (edgeSplit D i k).length) :
    ∀ t ∈ Ioo ((edgeSplit D i k).get ⟨n, h1⟩) ((edgeSplit D i k).get ⟨n + 1, h2⟩),
      edgeMap D i k t ∉ D.vertexSet := by
  intro t ht hV
  have hnI := edgeSplit_mem_Icc D i k (List.get_mem _ ⟨n, h1⟩)
  have hn1I := edgeSplit_mem_Icc D i k (List.get_mem _ ⟨n + 1, h2⟩)
  have htI : t ∈ Icc (0:ℝ) 1 := ⟨le_trans hnI.1 ht.1.le, le_trans ht.2.le hn1I.2⟩
  have hmem : t ∈ edgeSplit D i k := (mem_edgeSplit D i k).mpr ⟨htI, hV⟩
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp hmem
  have hmono := edgeSplit_sortedLT D i k
  have hlt1 : (⟨n, h1⟩ : Fin _) < r := by
    have : (edgeSplit D i k).get ⟨n, h1⟩ < (edgeSplit D i k).get r := by rw [hr]; exact ht.1
    exact hmono.lt_iff_lt.mp this
  have hlt2 : r < (⟨n + 1, h2⟩ : Fin _) := by
    have : (edgeSplit D i k).get r < (edgeSplit D i k).get ⟨n + 1, h2⟩ := by rw [hr]; exact ht.2
    exact hmono.lt_iff_lt.mp this
  have e1 : n < r.val := hlt1
  have e2 : r.val < n + 1 := hlt2
  omega

/-- **A dart of a dissection**: a tile, one of its sides, and a nondegenerate parameter interval
inside `[0,1]` whose *open* part carries no tiling vertex. -/
structure Dart (D : Dissection N) where
  tile : Fin N
  side : Fin 3
  lo : ℝ
  hi : ℝ
  lo_lt_hi : lo < hi
  lo_nonneg : 0 ≤ lo
  hi_le_one : hi ≤ 1
  vertexFree : ∀ t ∈ Ioo lo hi, edgeMap D tile side t ∉ D.vertexSet

/-- The relative interior of a dart, as a subset of the plane. -/
def Dart.relInt {D : Dissection N} (d : Dart D) : Set Plane :=
  edgeMap D d.tile d.side '' Ioo d.lo d.hi

/-- **The relative interior of a dart is nonempty** — the darts of this development are not
degenerate, so nothing below is vacuous. -/
theorem Dart.relInt_nonempty {D : Dissection N} (d : Dart D) : d.relInt.Nonempty := by
  obtain ⟨t, ht⟩ := Set.nonempty_Ioo.mpr d.lo_lt_hi
  exact ⟨edgeMap D d.tile d.side t, ⟨t, ht, rfl⟩⟩

/-- **CONSTANCY, final form.**  The unordered set of tiles meeting a dart is the same at every
point of the dart's relative interior. -/
theorem Dart.tiles_constant {D : Dissection N} (d : Dart D) {s t : ℝ}
    (hs : s ∈ Ioo d.lo d.hi) (ht : t ∈ Ioo d.lo d.hi) :
    dartTiles D d.tile d.side s = dartTiles D d.tile d.side t :=
  dartTiles_constant D d.lo_nonneg d.hi_le_one d.vertexFree hs ht

/-- **Non-vacuity, uniform:** every side of every tile of every dissection carries a dart. -/
theorem exists_dart (D : Dissection N) (i : Fin N) (k : Fin 3) :
    ∃ d : Dart D, d.tile = i ∧ d.side = k := by
  have hlen := two_le_edgeSplit_length D i k
  have h1 : 0 < (edgeSplit D i k).length := by omega
  have h2 : 0 + 1 < (edgeSplit D i k).length := by omega
  refine ⟨{ tile := i, side := k
            lo := (edgeSplit D i k).get ⟨0, h1⟩
            hi := (edgeSplit D i k).get ⟨0 + 1, h2⟩
            lo_lt_hi := edgeSplit_sortedLT D i k (by exact Fin.mk_lt_mk.mpr (by omega))
            lo_nonneg := (edgeSplit_mem_Icc D i k (List.get_mem _ ⟨0, h1⟩)).1
            hi_le_one := (edgeSplit_mem_Icc D i k (List.get_mem _ ⟨0 + 1, h2⟩)).2
            vertexFree := edgeSplit_gap_vertexFree D i k h1 h2 }, rfl, rfl⟩

/-! ### The darts of a side exhaust it -/

theorem edgeSplit_get_zero (D : Dissection N) (i : Fin N) (k : Fin 3)
    (h : 0 < (edgeSplit D i k).length) : (edgeSplit D i k).get ⟨0, h⟩ = 0 := by
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp (zero_mem_edgeSplit D i k)
  have hle : (edgeSplit D i k).get ⟨0, h⟩ ≤ (edgeSplit D i k).get r :=
    (edgeSplit_sortedLT D i k).monotone (Fin.le_def.mpr (Nat.zero_le _))
  rw [hr] at hle
  exact le_antisymm hle (edgeSplit_mem_Icc D i k (List.get_mem _ _)).1

theorem edgeSplit_get_last (D : Dissection N) (i : Fin N) (k : Fin 3)
    (h : (edgeSplit D i k).length - 1 < (edgeSplit D i k).length) :
    (edgeSplit D i k).get ⟨(edgeSplit D i k).length - 1, h⟩ = 1 := by
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp (one_mem_edgeSplit D i k)
  have hle : (edgeSplit D i k).get r ≤ (edgeSplit D i k).get ⟨_, h⟩ :=
    (edgeSplit_sortedLT D i k).monotone
      (Fin.le_def.mpr (show (r : ℕ) ≤ (edgeSplit D i k).length - 1 by have := r.isLt; omega))
  rw [hr] at hle
  exact le_antisymm (edgeSplit_mem_Icc D i k (List.get_mem _ _)).2 hle

/-- **The darts of a side exhaust it.**  Every parameter of `[0,1]` lies in one of the closed
consecutive intervals of the sorted split list.  With `edgeSplit_gap_vertexFree` this says the
consecutive pairs really are the *maximal* vertex-free sub-segments: they are vertex-free, and
together they cover the whole side. -/
theorem edgeSplit_covers (D : Dissection N) (i : Fin N) (k : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ n : ℕ, ∃ (h1 : n < (edgeSplit D i k).length) (h2 : n + 1 < (edgeSplit D i k).length),
      t ∈ Icc ((edgeSplit D i k).get ⟨n, h1⟩) ((edgeSplit D i k).get ⟨n + 1, h2⟩) := by
  classical
  have hlen : 2 ≤ (edgeSplit D i k).length := two_le_edgeSplit_length D i k
  have h0 : 0 < (edgeSplit D i k).length := by omega
  have hlastlt : (edgeSplit D i k).length - 1 < (edgeSplit D i k).length := by omega
  have hz := edgeSplit_get_zero D i k h0
  have hlast := edgeSplit_get_last D i k hlastlt
  have hmono := edgeSplit_sortedLT D i k
  set S : Finset (Fin (edgeSplit D i k).length) :=
    Finset.univ.filter (fun r => (edgeSplit D i k).get r ≤ t) with hSdef
  have hSne : S.Nonempty :=
    ⟨⟨0, h0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hz]; exact ht.1⟩⟩
  set n := S.max' hSne with hn
  have hnle : (edgeSplit D i k).get n ≤ t := (Finset.mem_filter.mp (S.max'_mem hSne)).2
  by_cases hcase : n.val + 1 < (edgeSplit D i k).length
  · refine ⟨n.val, n.isLt, hcase, ?_, ?_⟩
    · simpa using hnle
    · by_contra hcon
      rw [not_le] at hcon
      have hmem : (⟨n.val + 1, hcase⟩ : Fin _) ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon.le⟩
      have hle := S.le_max' _ hmem
      rw [← hn] at hle
      simp only [Fin.le_def] at hle
      omega
  · have hnv : n.val = (edgeSplit D i k).length - 1 := by have := n.isLt; omega
    have hgetn : (edgeSplit D i k).get n = 1 := by
      have hfin : n = (⟨(edgeSplit D i k).length - 1, hlastlt⟩ : Fin _) := Fin.ext hnv
      rw [hfin]; exact hlast
    have ht1 : t = 1 := le_antisymm ht.2 (by rw [← hgetn]; exact hnle)
    have hidx : (edgeSplit D i k).length - 2 + 1 = (edgeSplit D i k).length - 1 := by omega
    refine ⟨(edgeSplit D i k).length - 2, by omega, by omega, ?_, ?_⟩
    · have hmm := hmono.monotone
        (Fin.le_def.mpr (show (edgeSplit D i k).length - 2 ≤ (edgeSplit D i k).length - 1 by omega)
          : (⟨(edgeSplit D i k).length - 2, by omega⟩ : Fin _) ≤ ⟨_, hlastlt⟩)
      rw [hlast] at hmm
      linarith
    · have hfin : (⟨(edgeSplit D i k).length - 2 + 1, by omega⟩ : Fin _)
          = (⟨(edgeSplit D i k).length - 1, hlastlt⟩ : Fin _) := Fin.ext hidx
      rw [hfin, hlast]
      exact ht.2

/-- **Strict coverage.**  A *non-vertex* parameter of a side lies in the OPEN interval of one of the
consecutive pairs — i.e. in the relative interior of a dart. -/
theorem edgeSplit_covers_strict (D : Dissection N) (i : Fin N) (k : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hV : edgeMap D i k t ∉ D.vertexSet) :
    ∃ n : ℕ, ∃ (h1 : n < (edgeSplit D i k).length) (h2 : n + 1 < (edgeSplit D i k).length),
      t ∈ Ioo ((edgeSplit D i k).get ⟨n, h1⟩) ((edgeSplit D i k).get ⟨n + 1, h2⟩) := by
  obtain ⟨n, h1, h2, hmem⟩ := edgeSplit_covers D i k ht
  have hne : ∀ (r : Fin (edgeSplit D i k).length), t ≠ (edgeSplit D i k).get r := by
    intro r hr
    exact hV (hr ▸ ((mem_edgeSplit D i k).mp (List.get_mem _ r)).2)
  exact ⟨n, h1, h2, lt_of_le_of_ne hmem.1 (Ne.symm (hne _)), lt_of_le_of_ne hmem.2 (hne _)⟩

/-- The `n`-th dart of tile `i`'s side `k`. -/
noncomputable def sideDart (D : Dissection N) (i : Fin N) (k : Fin 3) (n : ℕ)
    (h2 : n + 1 < (edgeSplit D i k).length) : Dart D where
  tile := i
  side := k
  lo := (edgeSplit D i k).get ⟨n, by omega⟩
  hi := (edgeSplit D i k).get ⟨n + 1, h2⟩
  lo_lt_hi := edgeSplit_sortedLT D i k (Fin.mk_lt_mk.mpr (by omega))
  lo_nonneg := (edgeSplit_mem_Icc D i k (List.get_mem _ ⟨n, by omega⟩)).1
  hi_le_one := (edgeSplit_mem_Icc D i k (List.get_mem _ ⟨n + 1, h2⟩)).2
  vertexFree := edgeSplit_gap_vertexFree D i k (by omega) h2

/-- **Every non-vertex point of every tile side lies in the relative interior of a dart**, and the
tile set is constant there.  This is the target statement of the mode, assembled. -/
theorem exists_dart_containing (D : Dissection N) (i : Fin N) (k : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hV : edgeMap D i k t ∉ D.vertexSet) :
    ∃ d : Dart D, d.tile = i ∧ d.side = k ∧ edgeMap D i k t ∈ d.relInt := by
  obtain ⟨n, h1, h2, hmem⟩ := edgeSplit_covers_strict D i k ht hV
  exact ⟨sideDart D i k n h2, rfl, rfl, ⟨t, hmem, rfl⟩⟩

/-! ### Quantitative bookkeeping: how the construction scales in `N` -/

/-- The tiling vertices as a `Finset`. -/
noncomputable def vertexFinset (D : Dissection N) : Finset Plane := D.vertexSet_finite.toFinset

/-- **At most `3N` tiling vertices.** -/
theorem vertexFinset_card_le (D : Dissection N) : (vertexFinset D).card ≤ 3 * N := by
  classical
  have himg : vertexFinset D
      ⊆ Finset.image (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2) Finset.univ := by
    intro x hx
    rw [vertexFinset, Set.Finite.mem_toFinset] at hx
    simp only [Dissection.vertexSet, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨i, k, hik⟩ := hx
    exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, hik.symm⟩
  refine le_trans (Finset.card_le_card himg) (le_trans Finset.card_image_le ?_)
  simp [Fintype.card_prod, Nat.mul_comm]

/-- **At most `3N` split points on a side, hence at most `3N − 1` darts per side and at most
`9N² − 3N` darts in total.**  This is the honest bound the parameter construction gives; the true
count is much smaller (`3N` plus the number of strict vertex-in-edge incidences: `145` rather than
`17292` on the certified `N = 44` instance), but a linear bound is *not* available from this
argument — see the report. -/
theorem edgeSplit_length_le (D : Dissection N) (i : Fin N) (k : Fin 3) :
    (edgeSplit D i k).length ≤ 3 * N := by
  classical
  rw [edgeSplit, Finset.length_sort]
  have hsub : (vertexParamFinset D i k).image (edgeMap D i k) ⊆ vertexFinset D := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    rw [vertexParamFinset, Set.Finite.mem_toFinset] at ht
    rw [vertexFinset, Set.Finite.mem_toFinset]
    exact ht.2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (edgeMap_injective D i k)] at hcard
  exact hcard.trans (vertexFinset_card_le D)

/-! ## Satisfiability witnesses

Rule: every theorem needs an exhibited witness for its hypotheses.  The hypotheses used above are
(i) a `Dissection N`, (ii) a dart, (iii) for the pair statements, a point of the target's interior.
-/

/-- The ball hypothesis of `Dissection.two_tiles_at_edge_point` is implied by interiority, so it is
never an extra assumption. -/
theorem ball_of_mem_interior (D : Dissection N) {x : Plane}
    (hx : x ∈ interior D.target.carrier) : ∃ R > 0, Metric.ball x R ⊆ D.target.carrier := by
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  exact ⟨R, hR, hsub.trans interior_subset⟩

/-- **The pair statement with the radius eliminated.**  Its only remaining hypothesis is that the
point is interior to the target. -/
theorem dartTiles_card_two_of_interior (D : Dissection N) (hN : 0 < N) (d : Dart D) {s : ℝ}
    (hs : s ∈ Ioo d.lo d.hi)
    (hint : edgeMap D d.tile d.side s ∈ interior D.target.carrier) :
    (dartTiles D d.tile d.side s).card = 2 := by
  obtain ⟨R, hR, hRt⟩ := ball_of_mem_interior D hint
  exact dartTiles_card_two D hN d.lo_nonneg d.hi_le_one d.vertexFree hs hR hRt

/-- **Concrete witness.**  `delta4Dissection : Dissection 176` (`CollarAssembleM4.lean`) is a real
dissection of the corpus.  Every side of every one of its 176 tiles carries a dart whose relative
interior is nonempty, and the tile set is constant on it.  Nothing above is vacuous. -/
theorem witness_delta4 (i : Fin 176) (k : Fin 3) :
    ∃ d : Dart delta4Dissection, d.tile = i ∧ d.side = k ∧ d.relInt.Nonempty ∧
      ∀ s ∈ Ioo d.lo d.hi, ∀ t ∈ Ioo d.lo d.hi,
        dartTiles delta4Dissection d.tile d.side s
          = dartTiles delta4Dissection d.tile d.side t := by
  obtain ⟨d, h1, h2⟩ := exists_dart delta4Dissection i k
  exact ⟨d, h1, h2, d.relInt_nonempty, fun s hs t ht => d.tiles_constant hs ht⟩

/-! ## The edge involution

Constancy says the tile *set* is constant along a dart.  The next object a general arrangement needs
is the involution `α` that swaps a dart for the partner tile's dart on the same segment.  Because
`Dart` asks only for vertex-freeness of the open part (not for maximality), the partner dart is
obtained from `partner_side_param`'s reparametrisation with no further geometry. -/

theorem relInt_eq_of_reparam (D : Dissection N) (i : Fin N) (k : Fin 3) (j : Fin N) (m : Fin 3)
    {p δ : ℝ} (hδ : δ ≠ 0)
    (hrep : ∀ r : ℝ, edgeMap D j m r = edgeMap D i k (p + r * δ))
    {lo hi lo' hi' : ℝ}
    (hkey : ∀ r : ℝ, r ∈ Ioo lo' hi' ↔ p + r * δ ∈ Ioo lo hi) :
    edgeMap D j m '' Ioo lo' hi' = edgeMap D i k '' Ioo lo hi := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨p + r * δ, (hkey r).mp hr, (hrep r).symm⟩
  · rintro ⟨t, ht, rfl⟩
    have hcancel : p + (t - p) / δ * δ = t := by
      rw [div_mul_cancel₀ _ hδ]; ring
    exact ⟨(t - p) / δ, (hkey _).mpr (by rw [hcancel]; exact ht), by rw [hrep, hcancel]⟩

/-- **The edge involution, point-set form.**  For a dart `d` and any tile `j ≠ d.tile` meeting it,
there is a dart of `j` with exactly the same relative interior.  Together with `Dart.tiles_constant`
this is the well-definedness of the arrangement's edge map on a *general* dissection — the fact
`TP_gonthier` verifies by `decide` on the certified `N = 44` instance. -/
theorem exists_partner_dart (D : Dissection N) (d : Dart D) {j : Fin N} (hji : j ≠ d.tile)
    {s : ℝ} (hs : s ∈ Ioo d.lo d.hi) (hj : OnEdge D (edgeMap D d.tile d.side s) j) :
    ∃ d' : Dart D, d'.tile = j ∧ d'.relInt = d.relInt := by
  obtain ⟨m, p, δ, hδ, hrep, hminlo, hhimax⟩ :=
    partner_side_param D hji d.lo_nonneg d.hi_le_one d.vertexFree hs hj
  set a : ℝ := (d.lo - p) / δ with hadef
  set b : ℝ := (d.hi - p) / δ with hbdef
  have hpa : p + a * δ = d.lo := by rw [hadef, div_mul_cancel₀ _ hδ]; ring
  have hpb : p + b * δ = d.hi := by rw [hbdef, div_mul_cancel₀ _ hδ]; ring
  have hlohi := d.lo_lt_hi
  have hlo0 := d.lo_nonneg
  have hhi1 := d.hi_le_one
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · -- `δ < 0`: the reparametrisation reverses the sense, so the partner dart is `[b, a]`
    rw [min_eq_right (by linarith)] at hminlo
    rw [max_eq_left (by linarith)] at hhimax
    have hba : b < a := by nlinarith
    have hb0 : 0 ≤ b := by nlinarith
    have ha1 : a ≤ 1 := by nlinarith
    have hkey : ∀ r : ℝ, r ∈ Ioo b a ↔ p + r * δ ∈ Ioo d.lo d.hi := by
      intro r
      simp only [Set.mem_Ioo, ← hpa, ← hpb]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
    refine ⟨{ tile := j, side := m + 1, lo := b, hi := a
              lo_lt_hi := hba
              lo_nonneg := hb0
              hi_le_one := ha1
              vertexFree := fun r hr => by
                rw [hrep r]; exact d.vertexFree _ ((hkey r).mp hr) }, rfl, ?_⟩
    exact relInt_eq_of_reparam D d.tile d.side j (m + 1) hδ hrep hkey
  · -- `δ > 0`: the sense is preserved, and the partner dart is `[a, b]`
    rw [min_eq_left (by linarith)] at hminlo
    rw [max_eq_right (by linarith)] at hhimax
    have hab : a < b := by nlinarith
    have ha0 : 0 ≤ a := by nlinarith
    have hb1 : b ≤ 1 := by nlinarith
    have hkey : ∀ r : ℝ, r ∈ Ioo a b ↔ p + r * δ ∈ Ioo d.lo d.hi := by
      intro r
      simp only [Set.mem_Ioo, ← hpa, ← hpb]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
    refine ⟨{ tile := j, side := m + 1, lo := a, hi := b
              lo_lt_hi := hab
              lo_nonneg := ha0
              hi_le_one := hb1
              vertexFree := fun r hr => by
                rw [hrep r]; exact d.vertexFree _ ((hkey r).mp hr) }, rfl, ?_⟩
    exact relInt_eq_of_reparam D d.tile d.side j (m + 1) hδ hrep hkey


/-- **The involution, unconditionally at interior darts.**  If any point of a dart's relative
interior is interior to the target, then a *different* tile carries a dart with exactly the same
relative interior.  This is the edge involution `α` of the arrangement, on a general dissection. -/
theorem exists_partner_dart_of_interior (D : Dissection N) (hN : 0 < N) (d : Dart D) {s : ℝ}
    (hs : s ∈ Ioo d.lo d.hi)
    (hint : edgeMap D d.tile d.side s ∈ interior D.target.carrier) :
    ∃ d' : Dart D, d'.tile ≠ d.tile ∧ d'.relInt = d.relInt := by
  obtain ⟨R, hR, hRt⟩ := ball_of_mem_interior D hint
  have hself : OnEdge D (edgeMap D d.tile d.side s) d.tile :=
    onEdge_self D d.tile d.side
      ⟨le_trans d.lo_nonneg hs.1.le, le_trans hs.2.le d.hi_le_one⟩ (d.vertexFree s hs)
  obtain ⟨j, hjne, hj⟩ := D.second_tile_at_edge_point hN
    (D.notMem_vertexSet (d.vertexFree s hs)) hR hRt hself
  obtain ⟨d', h1, h2⟩ := exists_partner_dart D d hjne hs hj
  exact ⟨d', h1 ▸ hjne, h2⟩

end Erdos634.TPTao
#print axioms Erdos634.TPTao.onEdge_propagate
#print axioms Erdos634.TPTao.onEdge_set_constant
#print axioms Erdos634.TPTao.dartTiles_constant
#print axioms Erdos634.TPTao.dartTiles_card_two
#print axioms Erdos634.TPTao.otherTile_constant
#print axioms Erdos634.TPTao.Dart.tiles_constant
#print axioms Erdos634.TPTao.exists_dart
#print axioms Erdos634.TPTao.edgeSplit_covers
#print axioms Erdos634.TPTao.exists_dart_containing
#print axioms Erdos634.TPTao.edgeSplit_length_le
#print axioms Erdos634.TPTao.exists_partner_dart
#print axioms Erdos634.TPTao.exists_partner_dart_of_interior
#print axioms Erdos634.TPTao.witness_delta4
