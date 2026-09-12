import Erdos634.MarchInduction

/-!
# The mixed junctions of the layer-1 march at `e = 1`: figures and placements, in coordinates

Written 2026-09-12, sequential step 3 after `MarchInduction.lean`.  That file proved the `a|a`
junction step (`junction_step`) and the run induction (`run_rigid`).  This file applies the same
method — boundary π-figure at the junction (`TileAt.congruentDissection_boundary_figure_cases`),
the third tile's edges lie in the uncovered wedge (an ε-push into
`MarchOverlap.wedge_disjoint_combo`), Gram-form extremality (`gram_extremal`) — to the six mixed
junction types `a|b`, `b|a`, `a|c`, `c|a`, `b|c`, `c|b`.

## What is proved (all vertex-set statements about a `CongruentDissection` of `baseBetaTarget 1 f`)

* `b_letter_tile`, `c_letter_tile`: a tile laying the `b`- (`c`-) letter on the base has the vertex
  set of `bSlotTile`/`bSlotTile'` (`cSlotTile`/`cSlotTile'`) — two reflections, from distances.
* The figure lemmas at an interior base point: two `γ`-corners are impossible (`no_two_gamma`);
  `γ + β` and `γ + α` force exactly one further tile, of the third angle; `β + β` and `α + α` force
  the figure `{3α, 2β}`; `α + β` leaves `{γ}` or `{3α, 2β}` (`alpha_beta_cases`).
* `edge_in_wedge_gen`, `third_tile_placements`: the general form of `MarchInduction.edge_in_wedge`
  and `wedge_extremal_coords` — for arbitrary left/right neighbour tiles given by their vertex
  sets, a third tile with a corner at the junction has **exactly two placements**: its edges are
  the wedge's rays scaled to the tile's side lengths, or the reflection in the bisector.
* The junction theorems, each with the exact candidate list (§7):
  - `junction_a_b`: `bSlotTile` is **killed** (two `γ`); `bSlotTile'` forced; the `β`-tile at the
    junction is `bCapSet` (horizontal `b`-edge at the `b`-tile's apex height) or `bOverSet`.
  - `junction_b'_a`: after `bSlotTile'`, `GB` is **killed**, `BG` forced; the `α`-tile at the
    junction is the flush or offset filler of the virtual junction.
  - `junction_a_c`: both reflections survive; after `cSlotTile` the `α`-tile is flush/offset
    filler; after `cSlotTile'` the `β`-tile is `bCapSet`/`bOverSet`.
  - `junction_c_a_*`: **neither orientation of the next `a` is killed by the figure**; the four
    (reflection × orientation) cases give: `cSlotTile + GB`: `β`-tile in `bCapMSet`/`bOverMSet`;
    `cSlotTile' + GB`: `α`-tile in the mirrored fillers; `cSlotTile + BG`: a `γ`-tile
    (`cCapSet`/`cSplitSet`) or the fan `{3α, 2β}`; `cSlotTile' + BG`: the fan `{3α, 2β}`.
  - pins `b|c`, `c|b` (`junction_b'_c`, `junction_c_b`, `junction_c'_b`): all four reflection
    pairs classified, with the two placements wherever the figure is `{α, β, γ}`.
  - `junction_a_b_corner`: **one small new kill** — at the corner slot (`x₀ = f`, word `a b …`)
    the overshoot placement's vertex `(3f/2, (c/b)h)` is the offset filler's corner overshoot,
    outside the target (`MarchInduction.offset_at_corner_junction_outside`); only the cap survives.
* `first_run`, `run_last_tile`, `word_b_first`, `word_c_first` (§9): the composite along a base
  word — `a^p b a^q c …` is decided (up to the binary choices above) through the `c`-slot's
  left junction; `a^p c a …` through the `c`-slot's left junction and *into* the `c|a` junction,
  where the orientation of the next `a` is **not** decided.  That is exactly where the method stops.
* §10 non-vacuity: `ab_config_f4`, `ca_config_f4` (`f = 4`, `N = 47`, prime): the slot tiles,
  caps and overshoots in numbers, every vertex inside the target; `word_b_first_hyps_f4`.

## Novelty ledger (`code/novelty_check.sh`, 2026-09-12)

`no_two_gamma` **reproduces** `OrientBridge.no_two_gamma_at_boundary_junction` (2026-08-29,
`RESEARCH_LOG.md:10105`, via `pin_angle_sum`); here it is re-derived from the trichotomy because
the same trichotomy supplies the rest.  "exactly two placements" (`RESEARCH_LOG.md:6775`) is the
corridor chart at `e ≥ 2`, a different configuration.  "overshoot placement", "flat cap",
"corner slot", `bCap*`, `cCap*`: no corpus match.

## What is NOT proved (the residue, exactly)

No mixed junction is *killed* beyond the `γγ` cases and the corner slot.  Every surviving
placement is admitted by the local method; the kills the engine uses there are **region-level** —
the second-offset stub `c − b = 1` (K1), the run `b − a` at the `c`-slot (K2), the pockets (P1a) —
none of which has a dissection-level statement in the corpus (`Frontier.lean`'s (P2) is a model of
the search's frontier, not a theorem about dissections; the "exact partition of a straight run
between convex corners" lemma does not exist and is not assumed here).  In particular the
orientation of the `a` after a `c`-slot is undecided (`junction_c_a`: `GB` survives with a
`β`-tile, `BG` with a `γ`-cap or the fan), so the run induction cannot restart there and the far
corner is not reached.  The `e = 1` family does **not** fall.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.MarchSlots

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchCoords Erdos634.BaseBetaTargetCoord
  Erdos634.MarchKills Erdos634.MarchKillsFan Erdos634.MarchInduction

/-! ## 1. Finset helpers -/

theorem exists_unique_of_card_one {N : ℕ} {P : Fin N → Prop} [DecidablePred P]
    (h : ({m | P m} : Finset (Fin N)).card = 1) : ∃ l, P l ∧ ∀ l', P l' → l' = l := by
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp h
  have hlmem : l ∈ ({m | P m} : Finset (Fin N)) := by rw [hl]; exact Finset.mem_singleton_self l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlmem
  refine ⟨l, hlmem, fun l' hl' => ?_⟩
  have : l' ∈ ({m | P m} : Finset (Fin N)) := by simp [hl']
  rw [hl] at this; exact Finset.mem_singleton.mp this

theorem two_le_card_of_ne {N : ℕ} {P : Fin N → Prop} [DecidablePred P] {i j : Fin N}
    (hij : i ≠ j) (hi : P i) (hj : P j) : 2 ≤ ({m | P m} : Finset (Fin N)).card := by
  have hsub : ({i, j} : Finset (Fin N)) ⊆ ({m | P m} : Finset (Fin N)) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hm with rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hij] at this

/-! ## 2. The figure at an interior base point -/

/-- The bundle of angle hypotheses used throughout, packaged. -/
structure AngleData (α β γ : ℝ) : Prop where
  hα : 0 < α
  hαβ : α < β
  hγdef : γ = 2 * α + β
  hrel : 3 * α + 2 * β = Real.pi
  hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi

theorem angleData_f3 : ∃ α β γ, AngleData α β γ := by
  obtain ⟨α, β, γ, h1, h2, h3, h4, h5⟩ := angle_bundle_nonvacuous_f3
  exact ⟨α, β, γ, ⟨h4, h5, h1, h2, h3⟩⟩

/-- **The boundary figure at an interior base point `(x₀, 0)`**, `0 < x₀ < L`. -/
theorem base_figure {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f) :
    (({i | (D.tile i).localAngle (mkPt x₀ 0) = Real.pi} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 3 ∧
      ({i | (D.tile i).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0) ∨
    (({i | (D.tile i).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 1) := by
  classical
  have hf1 : 1 < f := by linarith
  obtain ⟨hαβ', hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ :=
    distinct_of_order hA.hα hA.hαβ hA.hγdef hA.hrel
  have hv : mkPt x₀ 0 ∈ frontier D.target.carrier := by
    rw [htgt]; exact base_point_mem_frontier hf1 hx0.le hxL.le
  have hnv : mkPt x₀ 0 ∉ Set.range D.target.pts := by
    rw [htgt]; exact base_point_not_vertex hf1 hx0 hxL
  exact Erdos634.Geometry.Dissection.congruentDissection_boundary_figure_cases D α β γ hαβ' hαγ
    hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 hA.hγdef hA.hrel hA.hirr hM.hα' hM.hβ' hM.hγ' hv hnv

/-- **Two `γ`-corners at an interior base point are impossible.** -/
theorem no_two_gamma {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle (mkPt x₀ 0) = γ) (hj : (D.tile j).localAngle (mkPt x₀ 0) = γ) :
    False := by
  classical
  have h2 := two_le_card_of_ne (P := fun m => (D.tile m).localAngle (mkPt x₀ 0) = γ) hij hi hj
  rcases base_figure D hf htgt hM hA hx0 hxL with ⟨_, _, _, hG⟩ | ⟨_, _, hG⟩ | ⟨_, _, hG⟩ <;>
    simp only at h2 hG <;> omega

/-- **`γ + β` at an interior base point: exactly one further tile, presenting `α`.** -/
theorem third_of_gamma_beta {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : (D.tile i).localAngle (mkPt x₀ 0) = γ) (hj : (D.tile j).localAngle (mkPt x₀ 0) = β) :
    ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = α ∧
      ∀ l', (D.tile l').localAngle (mkPt x₀ 0) = α → l' = l := by
  classical
  obtain ⟨hαβ', hαγ, -, -, hβγ, -, -, -, -, -⟩ := distinct_of_order hA.hα hA.hαβ hA.hγdef hA.hrel
  have hγpos : 0 < ({m | (D.tile m).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  rcases base_figure D hf htgt hM hA hx0 hxL with ⟨_, _, _, hG⟩ | ⟨_, _, hG⟩ | ⟨hAc, _, _⟩
  · omega
  · omega
  · obtain ⟨l, hl, huniq⟩ := exists_unique_of_card_one hAc
    refine ⟨l, ?_, ?_, hl, huniq⟩
    · rintro rfl; rw [hl] at hi; exact hαγ hi
    · rintro rfl; rw [hl] at hj; exact hαβ' hj

/-- **`γ + α` at an interior base point: exactly one further tile, presenting `β`.** -/
theorem third_of_gamma_alpha {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : (D.tile i).localAngle (mkPt x₀ 0) = γ) (hj : (D.tile j).localAngle (mkPt x₀ 0) = α) :
    ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = β ∧
      ∀ l', (D.tile l').localAngle (mkPt x₀ 0) = β → l' = l := by
  classical
  obtain ⟨hαβ', hαγ, -, -, hβγ, -, -, -, -, -⟩ := distinct_of_order hA.hα hA.hαβ hA.hγdef hA.hrel
  have hγpos : 0 < ({m | (D.tile m).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  rcases base_figure D hf htgt hM hA hx0 hxL with ⟨_, _, _, hG⟩ | ⟨_, _, hG⟩ | ⟨_, hBc, _⟩
  · omega
  · omega
  · obtain ⟨l, hl, huniq⟩ := exists_unique_of_card_one hBc
    refine ⟨l, ?_, ?_, hl, huniq⟩
    · rintro rfl; rw [hl] at hi; exact hβγ hi
    · rintro rfl; rw [hl] at hj; exact hαβ' hj.symm

/-- **`β + β` at an interior base point: the figure is `{3α, 2β}`** — three `α`-tiles, no third
`β`-tile, no `γ`-tile. -/
theorem beta_beta_fan {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle (mkPt x₀ 0) = β) (hj : (D.tile j).localAngle (mkPt x₀ 0) = β) :
    ({m | (D.tile m).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 3 ∧
    ({m | (D.tile m).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 2 ∧
    ({m | (D.tile m).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0 := by
  classical
  have h2 := two_le_card_of_ne (P := fun m => (D.tile m).localAngle (mkPt x₀ 0) = β) hij hi hj
  rcases base_figure D hf htgt hM hA hx0 hxL with ⟨_, _, hB, _⟩ | h | ⟨_, hB, _⟩
  · simp only at h2 hB; omega
  · exact h
  · simp only at h2 hB; omega

/-- **`α + α` at an interior base point: the figure is `{3α, 2β}`.** -/
theorem alpha_alpha_fan {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle (mkPt x₀ 0) = α) (hj : (D.tile j).localAngle (mkPt x₀ 0) = α) :
    ({m | (D.tile m).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 3 ∧
    ({m | (D.tile m).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 2 ∧
    ({m | (D.tile m).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0 := by
  classical
  have h2 := two_le_card_of_ne (P := fun m => (D.tile m).localAngle (mkPt x₀ 0) = α) hij hi hj
  rcases base_figure D hf htgt hM hA hx0 hxL with ⟨_, hAc, _, _⟩ | h | ⟨hAc, _, _⟩
  · simp only at h2 hAc; omega
  · exact h
  · simp only at h2 hAc; omega

/-- **`α + β` at an interior base point: either exactly one further tile, presenting `γ`, or the
fan figure `{3α, 2β}`.** -/
theorem alpha_beta_cases {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : (D.tile i).localAngle (mkPt x₀ 0) = α) (hj : (D.tile j).localAngle (mkPt x₀ 0) = β) :
    (∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = γ ∧
      ∀ l', (D.tile l').localAngle (mkPt x₀ 0) = γ → l' = l) ∨
    (({m | (D.tile m).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 3 ∧
     ({m | (D.tile m).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 2 ∧
     ({m | (D.tile m).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0) := by
  classical
  obtain ⟨hαβ', hαγ, -, -, hβγ, -, -, -, -, -⟩ := distinct_of_order hA.hα hA.hαβ hA.hγdef hA.hrel
  have hαpos : 0 < ({m | (D.tile m).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  rcases base_figure D hf htgt hM hA hx0 hxL with ⟨_, hAc, _, _⟩ | h | ⟨_, _, hGc⟩
  · omega
  · exact Or.inr h
  · obtain ⟨l, hl, huniq⟩ := exists_unique_of_card_one hGc
    refine Or.inl ⟨l, ?_, ?_, hl, huniq⟩
    · rintro rfl; rw [hl] at hi; exact hαγ hi.symm
    · rintro rfl; rw [hl] at hj; exact hβγ hj.symm

/-! ## 3. Corner data for `β` and `γ` (the analogues of `alpha_corner_data`) -/

/-- The sides at the third vertex of a `b`-edge: `{a, c}` in one of the two orders. -/
theorem sides_of_b_edge {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) (j : Fin N) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n)
    (hmn : m ≠ n) (hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = f ^ 2 - 1) :
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f ^ 2) ∨
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_dists D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = f ^ 2 := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = f := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = f ^ 2 - 1 := by rw [dist_comm]; exact m20
  have hinj := σ.injective
  have hkm' : σ k ≠ σ m := fun h => hkm (hinj h)
  have hkn' : σ k ≠ σ n := fun h => hkn (hinj h)
  have hmn' : σ m ≠ σ n := fun h => hmn (hinj h)
  rw [hσ] at hd; rw [hσ, hσ]
  generalize σ k = sk at hd hkm' hkn' ⊢
  generalize σ m = sm at hd hkm' hmn' ⊢
  generalize σ n = sn at hkn' hmn' ⊢
  have hff : f ^ 2 ≠ f ^ 2 - 1 := by linarith
  have hff' : f ≠ f ^ 2 - 1 := by nlinarith
  fin_cases sk <;> fin_cases sm <;> fin_cases sn <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, m01, m12, m20, m10, m21, m02,
      dist_self] at hd hkm' hkn' hmn' ⊢ <;>
    first
    | exact absurd rfl hkm'
    | exact absurd rfl hkn'
    | exact absurd rfl hmn'
    | exact absurd hd hff
    | exact absurd hd hff'
    | simp

/-- The sides at the third vertex of a `c`-edge: `{a, b}` in one of the two orders. -/
theorem sides_of_c_edge {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) (j : Fin N) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n)
    (hmn : m ≠ n) (hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = f ^ 2) :
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f ^ 2 - 1) ∨
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ^ 2 - 1 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_dists D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = f ^ 2 := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = f := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = f ^ 2 - 1 := by rw [dist_comm]; exact m20
  have hinj := σ.injective
  have hkm' : σ k ≠ σ m := fun h => hkm (hinj h)
  have hkn' : σ k ≠ σ n := fun h => hkn (hinj h)
  have hmn' : σ m ≠ σ n := fun h => hmn (hinj h)
  rw [hσ] at hd; rw [hσ, hσ]
  generalize σ k = sk at hd hkm' hkn' ⊢
  generalize σ m = sm at hd hkm' hmn' ⊢
  generalize σ n = sn at hkn' hmn' ⊢
  have hff : f ^ 2 - 1 ≠ f ^ 2 := by linarith
  have hff' : f ≠ f ^ 2 := by nlinarith
  fin_cases sk <;> fin_cases sm <;> fin_cases sn <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, m01, m12, m20, m10, m21, m02,
      dist_self] at hd hkm' hkn' hmn' ⊢ <;>
    first
    | exact absurd rfl hkm'
    | exact absurd rfl hkn'
    | exact absurd rfl hmn'
    | exact absurd hd hff
    | exact absurd hd hff'
    | simp

theorem fin3_succ_ne (k : Fin 3) : k + 1 ≠ k + 2 ∧ k + 1 ≠ k ∧ k + 2 ≠ k := by
  revert k; decide

/-- **A tile presenting `β` at `v` has a vertex there, opposite side `b`, adjacent sides `{a, c}`.** -/
theorem beta_corner_data {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) (hA : AngleData α β γ) {l : Fin N} {v : Plane}
    (hl : (D.tile l).localAngle v = β) :
    ∃ k : Fin 3, (D.tile l).pts k = v ∧
      dist ((D.tile l).pts (k + 1)) ((D.tile l).pts (k + 2)) = f ^ 2 - 1 ∧
      ((dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = f ∧
        dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = f ^ 2) ∨
       (dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = f ^ 2 ∧
        dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = f)) := by
  have hπ := Real.pi_pos
  have hα := hA.hα; have hαβ := hA.hαβ; have hγdef := hA.hγdef; have hrel := hA.hrel
  have hβπ : β < Real.pi := by nlinarith
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile l) v with ⟨k, hk, hang⟩ | h | h | h
  · rw [hang] at hl
    obtain ⟨k', hk'ang, hk'd⟩ :=
      Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent l).symm k
    rw [hl] at hk'ang
    have hk'1 : k' = 1 := by
      by_contra hne
      have hβγ : β ≠ γ := by rw [hγdef]; intro h; linarith
      fin_cases k'
      · exact hαβ.ne (hk'ang.trans hM.hα').symm
      · exact hne rfl
      · exact hβγ (hk'ang.trans hM.hγ')
    subst hk'1
    have hopp : dist ((D.tile l).pts (k + 1)) ((D.tile l).pts (k + 2)) = f ^ 2 - 1 := by
      rw [← hk'd]; exact (model_dists D hM).2.2
    refine ⟨k, hk.symm, hopp, ?_⟩
    obtain ⟨hne1, hne2, hne3⟩ := fin3_succ_ne k
    rcases sides_of_b_edge D hf hM l hne1 hne2 hne3 hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
  · rw [h] at hl; linarith
  · rw [h] at hl; linarith
  · rw [h] at hl; linarith [hA.hα, hA.hαβ]

/-- **A tile presenting `γ` at `v` has a vertex there, opposite side `c`, adjacent sides `{a, b}`.** -/
theorem gamma_corner_data {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) (hA : AngleData α β γ) {l : Fin N} {v : Plane}
    (hl : (D.tile l).localAngle v = γ) :
    ∃ k : Fin 3, (D.tile l).pts k = v ∧
      dist ((D.tile l).pts (k + 1)) ((D.tile l).pts (k + 2)) = f ^ 2 ∧
      ((dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = f ∧
        dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = f ^ 2 - 1) ∨
       (dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = f ^ 2 - 1 ∧
        dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = f)) := by
  have hπ := Real.pi_pos
  have hα := hA.hα; have hαβ := hA.hαβ; have hγdef := hA.hγdef; have hrel := hA.hrel
  have hγπ : γ < Real.pi := by nlinarith
  have hγ0 : 0 < γ := by nlinarith
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile l) v with ⟨k, hk, hang⟩ | h | h | h
  · rw [hang] at hl
    obtain ⟨k', hk'ang, hk'd⟩ :=
      Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent l).symm k
    rw [hl] at hk'ang
    have hk'2 : k' = 2 := by
      by_contra hne
      have hαγ : α ≠ γ := by rw [hγdef]; intro h; linarith
      have hβγ : β ≠ γ := by rw [hγdef]; intro h; linarith
      fin_cases k'
      · exact hαγ (hk'ang.trans hM.hα').symm
      · exact hβγ (hk'ang.trans hM.hβ').symm
      · exact hne rfl
    subst hk'2
    have hopp : dist ((D.tile l).pts (k + 1)) ((D.tile l).pts (k + 2)) = f ^ 2 := by
      rw [← hk'd]; exact (model_dists D hM).1
    refine ⟨k, hk.symm, hopp, ?_⟩
    obtain ⟨hne1, hne2, hne3⟩ := fin3_succ_ne k
    rcases sides_of_c_edge D hf hM l hne1 hne2 hne3 hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
  · rw [h] at hl; linarith
  · rw [h] at hl; linarith
  · rw [h] at hl; linarith

/-- `alpha_corner_data` with the packaged bundle. -/
theorem alpha_corner_data' {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) (hA : AngleData α β γ) {l : Fin N} {v : Plane}
    (hl : (D.tile l).localAngle v = α) :
    ∃ k : Fin 3, (D.tile l).pts k = v ∧
      dist ((D.tile l).pts (k + 1)) ((D.tile l).pts (k + 2)) = f ∧
      ((dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = f ^ 2 ∧
        dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = f ^ 2 - 1) ∨
       (dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = f ^ 2 - 1 ∧
        dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = f ^ 2)) :=
  alpha_corner_data D hf hM hA.hα hA.hαβ hA.hγdef hA.hrel hl

/-! ## 4. The slot tiles' vertex sets, and local angles read off a vertex set -/

theorem range_bSlotTile (x f : ℝ) (hf : 1 < f) :
    Set.range (bSlotTile x f hf).pts
      = {mkPt x 0, mkPt (x + (f ^ 2 - 1)) 0, mkPt (x - 1 / 2) (f / (f ^ 2 - 1) * apexH f)} := by
  rw [range_pts_eq]; rfl

theorem range_bSlotTile' (x f : ℝ) (hf : 1 < f) :
    Set.range (bSlotTile' x f hf).pts
      = {mkPt x 0, mkPt (x + (f ^ 2 - 1)) 0,
         mkPt (x + (f ^ 2 - 1) + 1 / 2) (f / (f ^ 2 - 1) * apexH f)} := by
  rw [range_pts_eq]; rfl

theorem range_cSlotTile (x f : ℝ) (hf : 1 < f) :
    Set.range (cSlotTile x f hf).pts
      = {mkPt x 0, mkPt (x + f ^ 2) 0, mkPt (x + dBG f / f) (1 / f * apexH f)} := by
  rw [range_pts_eq]; rfl

theorem range_cSlotTile' (x f : ℝ) (hf : 1 < f) :
    Set.range (cSlotTile' x f hf).pts
      = {mkPt x 0, mkPt (x + f ^ 2) 0, mkPt (x + f ^ 2 - dBG f / f) (1 / f * apexH f)} := by
  rw [range_pts_eq]; rfl

/-- **Local angle at a vertex, read off the vertex set.**  If the vertex set is `{P, Q, R}` and
the side `QR` has length `a` (resp. `b`, `c`), the tile presents `α` (resp. `β`, `γ`) at `P`. -/
theorem localAngle_of_range {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {P Q R : Plane}
    (hr : Set.range (D.tile i).pts = {P, Q, R}) :
    (dist Q R = f → (D.tile i).localAngle P = α) ∧
    (dist Q R = f ^ 2 - 1 → (D.tile i).localAngle P = β) ∧
    (dist Q R = f ^ 2 → (D.tile i).localAngle P = γ) := by
  obtain ⟨k, hk⟩ := mem_range_of_eq hr (Set.mem_insert P _)
  rw [← hk]
  have h := localAngle_of_oppSide D hf hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' i k
  have hd : dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) = dist Q R := by
    rcases vertex_data_of_range hr hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  rw [hd] at h
  exact h

theorem sqrt_dist_eq {p q : Plane} {s : ℝ} (h : dist p q ^ 2 = s ^ 2) (hs : 0 ≤ s) :
    dist p q = s := dist_eq_of_sq_eq h dist_nonneg hs

/-- The angles of a tile with the vertex set of `bSlotTile' x`: `α` at the left end `(x, 0)`,
`γ` at the right end `(x + b, 0)`, `β` at the apex. -/
theorem bSlot'_angles {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {x : ℝ}
    (hr : Set.range (D.tile i).pts = Set.range (bSlotTile' x f (by linarith)).pts) :
    (D.tile i).localAngle (mkPt x 0) = α ∧
    (D.tile i).localAngle (mkPt (x + (f ^ 2 - 1)) 0) = γ := by
  have hf1 : 1 < f := by linarith
  rw [range_bSlotTile'] at hr
  obtain ⟨⟨-, -⟩, hs1, hs2⟩ := bSlotTile_sides x f hf1
  simp only [bSlotTile', mkTri_pts₀, mkTri_pts₁, mkTri_pts₂] at hs1 hs2
  constructor
  · exact (localAngle_of_range D hf hM hr).1 (sqrt_dist_eq hs1 (by linarith))
  · have hr' : Set.range (D.tile i).pts
        = {mkPt (x + (f ^ 2 - 1)) 0, mkPt x 0,
           mkPt (x + (f ^ 2 - 1) + 1 / 2) (f / (f ^ 2 - 1) * apexH f)} := by
      rw [hr, Set.insert_comm]
    exact (localAngle_of_range D hf hM hr').2.2 (sqrt_dist_eq hs2 (by positivity))

/-- The angles of a tile with the vertex set of `bSlotTile x`: `γ` at `(x, 0)`, `α` at `(x + b, 0)`. -/
theorem bSlot_angles {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {x : ℝ}
    (hr : Set.range (D.tile i).pts = Set.range (bSlotTile x f (by linarith)).pts) :
    (D.tile i).localAngle (mkPt x 0) = γ ∧
    (D.tile i).localAngle (mkPt (x + (f ^ 2 - 1)) 0) = α := by
  have hf1 : 1 < f := by linarith
  rw [range_bSlotTile] at hr
  obtain ⟨⟨hs1, hs2⟩, -, -⟩ := bSlotTile_sides x f hf1
  simp only [bSlotTile, mkTri_pts₀, mkTri_pts₁, mkTri_pts₂] at hs1 hs2
  constructor
  · exact (localAngle_of_range D hf hM hr).2.2 (sqrt_dist_eq hs2 (by positivity))
  · have hr' : Set.range (D.tile i).pts
        = {mkPt (x + (f ^ 2 - 1)) 0, mkPt x 0, mkPt (x - 1 / 2) (f / (f ^ 2 - 1) * apexH f)} := by
      rw [hr, Set.insert_comm]
    exact (localAngle_of_range D hf hM hr').1 (sqrt_dist_eq hs1 (by linarith))

/-- `cSlotTile x`: `β` at `(x, 0)`, `α` at `(x + c, 0)`. -/
theorem cSlot_angles {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {x : ℝ}
    (hr : Set.range (D.tile i).pts = Set.range (cSlotTile x f (by linarith)).pts) :
    (D.tile i).localAngle (mkPt x 0) = β ∧
    (D.tile i).localAngle (mkPt (x + f ^ 2) 0) = α := by
  have hf1 : 1 < f := by linarith
  rw [range_cSlotTile] at hr
  obtain ⟨⟨hs1, hs2⟩, -, -⟩ := cSlotTile_sides x f hf1
  simp only [cSlotTile, mkTri_pts₀, mkTri_pts₁, mkTri_pts₂] at hs1 hs2
  constructor
  · exact (localAngle_of_range D hf hM hr).2.1 (sqrt_dist_eq hs2 (by nlinarith))
  · have hr' : Set.range (D.tile i).pts
        = {mkPt (x + f ^ 2) 0, mkPt x 0, mkPt (x + dBG f / f) (1 / f * apexH f)} := by
      rw [hr, Set.insert_comm]
    exact (localAngle_of_range D hf hM hr').1 (sqrt_dist_eq hs1 (by linarith))

/-- `cSlotTile' x`: `α` at `(x, 0)`, `β` at `(x + c, 0)`. -/
theorem cSlot'_angles {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {x : ℝ}
    (hr : Set.range (D.tile i).pts = Set.range (cSlotTile' x f (by linarith)).pts) :
    (D.tile i).localAngle (mkPt x 0) = α ∧
    (D.tile i).localAngle (mkPt (x + f ^ 2) 0) = β := by
  have hf1 : 1 < f := by linarith
  rw [range_cSlotTile'] at hr
  obtain ⟨-, hs1, hs2⟩ := cSlotTile_sides x f hf1
  simp only [cSlotTile', mkTri_pts₀, mkTri_pts₁, mkTri_pts₂] at hs1 hs2
  constructor
  · exact (localAngle_of_range D hf hM hr).1 (sqrt_dist_eq hs1 (by linarith))
  · have hr' : Set.range (D.tile i).pts
        = {mkPt (x + f ^ 2) 0, mkPt x 0, mkPt (x + f ^ 2 - dBG f / f) (1 / f * apexH f)} := by
      rw [hr, Set.insert_comm]
    exact (localAngle_of_range D hf hM hr').2.1 (sqrt_dist_eq hs2 (by nlinarith))

/-- `aTileBG x`: `β` at `(x, 0)`, `γ` at `(x + f, 0)` (vertex-set form, packaged). -/
theorem aBG_angles {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {x : ℝ}
    (hr : Set.range (D.tile i).pts = Set.range (aTileBG x f (by linarith)).pts) :
    (D.tile i).localAngle (mkPt x 0) = β ∧ (D.tile i).localAngle (mkPt (x + f) 0) = γ :=
  ⟨bg_localAngle_left D hf hM hr, bg_localAngle_right D hf hM hr⟩

/-- `aTileGB x`: `γ` at `(x, 0)`, `β` at `(x + f, 0)`. -/
theorem aGB_angles {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) {i : Fin N} {x : ℝ}
    (hr : Set.range (D.tile i).pts = Set.range (aTileGB x f (by linarith)).pts) :
    (D.tile i).localAngle (mkPt x 0) = γ ∧ (D.tile i).localAngle (mkPt (x + f) 0) = β := by
  have hf1 : 1 < f := by linarith
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  rw [range_aTileGB] at hr
  constructor
  · refine (localAngle_of_range D hf hM hr).2.2 ?_
    refine sqrt_dist_eq ?_ (by positivity)
    rw [dist_sq_zero_apex hf1]
    have := gb_right f hf0
    rw [← this]; ring
  · have hr' : Set.range (D.tile i).pts
        = {mkPt (x + f) 0, mkPt x 0, mkPt (x + dGB f) (apexH f)} := by
      rw [hr, Set.insert_comm]
    refine (localAngle_of_range D hf hM hr').2.1 ?_
    refine sqrt_dist_eq ?_ (by nlinarith)
    rw [dist_sq_zero_apex hf1]
    have := gb_left f hf0
    rw [← this]; ring

/-! ## 5. A tile laying a `b`- or `c`-letter is one of the two reflections -/

/-- Circle intersection along the base: the abscissa of a point at distances `ℓ₁`, `ℓ₂` from
`(x₀, 0)`, `(x₀ + L, 0)`. -/
theorem base_circles_abscissa {X Y x₀ L ℓ₁ ℓ₂ : ℝ} (hL : L ≠ 0)
    (e1 : (X - x₀) ^ 2 + Y ^ 2 = ℓ₁ ^ 2) (e2 : (X - x₀ - L) ^ 2 + Y ^ 2 = ℓ₂ ^ 2) :
    X - x₀ = (ℓ₁ ^ 2 - ℓ₂ ^ 2 + L ^ 2) / (2 * L) := by
  field_simp
  linear_combination e1 - e2

/-- The third vertex of a tile laying an edge `[x₀, x₀ + L]` on the base, given its two
distances: coordinates, with the height determined by its square. -/
theorem third_vertex_coords {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    {j : Fin N} {x₀ L ℓ₁ ℓ₂ X₀ Y₀ : ℝ} (hL : L ≠ 0) (hY₀ : 0 < Y₀) {k m n : Fin 3}
    (hkm : k ≠ m) (hkn : k ≠ n) (hmn : m ≠ n)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + L) 0)
    (hXk : dist ((D.tile j).pts n) ((D.tile j).pts k) = ℓ₁)
    (hXm : dist ((D.tile j).pts n) ((D.tile j).pts m) = ℓ₂)
    (hX₀ : X₀ = x₀ + (ℓ₁ ^ 2 - ℓ₂ ^ 2 + L ^ 2) / (2 * L))
    (hY₀sq : Y₀ ^ 2 = ℓ₁ ^ 2 - ((ℓ₁ ^ 2 - ℓ₂ ^ 2 + L ^ 2) / (2 * L)) ^ 2) :
    (D.tile j).pts n = mkPt X₀ Y₀ := by
  have hf1 : 1 < f := by linarith
  have hY0 : 0 ≤ ((D.tile j).pts n) 1 := by
    have := pts_mem_target D.toDissection j n
    rw [htgt] at this
    exact target_height_nonneg one_pos hf1 _ this
  have hYne : ((D.tile j).pts n) 1 ≠ 0 :=
    third_not_on_line (D.tile j) hkm hkn hmn (by rw [hk]; simp) (by rw [hm]; simp)
  have hYpos : 0 < ((D.tile j).pts n) 1 := lt_of_le_of_ne hY0 (Ne.symm hYne)
  have e1 : (((D.tile j).pts n) 0 - x₀) ^ 2 + ((D.tile j).pts n) 1 ^ 2 = ℓ₁ ^ 2 := by
    have := congrArg (· ^ 2) hXk; simp only at this
    rw [hk, dist_sq_pt_mkPt] at this; simpa using this
  have e2 : (((D.tile j).pts n) 0 - x₀ - L) ^ 2 + ((D.tile j).pts n) 1 ^ 2 = ℓ₂ ^ 2 := by
    have := congrArg (· ^ 2) hXm; simp only at this
    rw [hm, dist_sq_pt_mkPt] at this
    convert this using 2 <;> ring
  have hx := base_circles_abscissa hL e1 e2
  have hy : ((D.tile j).pts n) 1 = Y₀ := by
    refine (sq_eq_sq₀ hYpos.le hY₀.le).mp ?_
    rw [hY₀sq]
    have e1' := e1
    rw [hx] at e1'
    linarith
  exact plane_ext (by simp; linarith) (by simpa using hy)

/-- **A tile laying the `b`-letter `[x₀, x₀ + b]` is `bSlotTile x₀` or `bSlotTile' x₀`** as a
vertex set. -/
theorem b_letter_tile {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {j : Fin N} {x₀ : ℝ} {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + (f ^ 2 - 1)) 0) :
    Set.range (D.tile j).pts = Set.range (bSlotTile x₀ f (by linarith)).pts ∨
    Set.range (D.tile j).pts = Set.range (bSlotTile' x₀ f (by linarith)).pts := by
  have hf1 : 1 < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hpos := apexH_pos hf1
  have hhb : 0 < f / (f ^ 2 - 1) * apexH f := by positivity
  have hhb2 : (f / (f ^ 2 - 1) * apexH f) ^ 2 = f ^ 2 - 1 / 4 := by
    rw [mul_pow, apexH_sq hf1]; unfold h2; field_simp <;> ring
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = f ^ 2 - 1 := by
    rw [hk, hm]; exact dist_mkPt_base _ _ hb.le
  have hcyc := fin3_succ k m n hkm (Ne.symm hnk) (Ne.symm hnm)
  rcases sides_of_b_edge D hf hM j hkm (Ne.symm hnk) (Ne.symm hnm) hd with ⟨hXk, hXm⟩ | ⟨hXk, hXm⟩
  · -- `a` to the left end, `c` to the right: apex at `(x₀ − 1/2, ·)`: `bSlotTile`
    have hX := third_vertex_coords D hf htgt (X₀ := x₀ - 1 / 2) (Y₀ := f / (f ^ 2 - 1) * apexH f)
      hb.ne' hhb hkm (Ne.symm hnk) (Ne.symm hnm) hk hm hXk hXm (by field_simp <;> ring)
      (by rw [hhb2]; field_simp <;> ring)
    left
    rw [range_pts_eq_cyclic _ k, range_bSlotTile]
    rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hk, hm, hX]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · -- `c` to the left end, `a` to the right: apex at `(x₀ + b + 1/2, ·)`: `bSlotTile'`
    have hX := third_vertex_coords D hf htgt (X₀ := x₀ + (f ^ 2 - 1) + 1 / 2)
      (Y₀ := f / (f ^ 2 - 1) * apexH f)
      hb.ne' hhb hkm (Ne.symm hnk) (Ne.symm hnm) hk hm hXk hXm (by field_simp <;> ring)
      (by rw [hhb2]; field_simp <;> ring)
    right
    rw [range_pts_eq_cyclic _ k, range_bSlotTile']
    rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hk, hm, hX]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- **A tile laying the `c`-letter `[x₀, x₀ + c]` is `cSlotTile x₀` or `cSlotTile' x₀`.** -/
theorem c_letter_tile {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {j : Fin N} {x₀ : ℝ} {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + f ^ 2) 0) :
    Set.range (D.tile j).pts = Set.range (cSlotTile x₀ f (by linarith)).pts ∨
    Set.range (D.tile j).pts = Set.range (cSlotTile' x₀ f (by linarith)).pts := by
  have hf1 : 1 < f := by linarith
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hc : (0:ℝ) < f ^ 2 := by positivity
  have hpos := apexH_pos hf1
  have hhc : 0 < 1 / f * apexH f := by positivity
  have hhc2 : (1 / f * apexH f) ^ 2 = f ^ 2 - (dBG f / f) ^ 2 := by
    rw [mul_pow, apexH_sq hf1]
    have := bg_left f hf0
    field_simp; nlinarith [this]
  obtain ⟨n, hnk, hnm⟩ := fin3_third k m hkm
  have hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = f ^ 2 := by
    rw [hk, hm]; exact dist_mkPt_base _ _ hc.le
  have hcyc := fin3_succ k m n hkm (Ne.symm hnk) (Ne.symm hnm)
  have hq : dBG f / f = (3 * f ^ 2 - 1) / (2 * f ^ 2) := by unfold dBG; field_simp <;> ring
  rcases sides_of_c_edge D hf hM j hkm (Ne.symm hnk) (Ne.symm hnm) hd with ⟨hXk, hXm⟩ | ⟨hXk, hXm⟩
  · -- `a` to the left, `b` to the right: `cSlotTile`
    have hX := third_vertex_coords D hf htgt (X₀ := x₀ + dBG f / f) (Y₀ := 1 / f * apexH f)
      hc.ne' hhc hkm (Ne.symm hnk) (Ne.symm hnm) hk hm hXk hXm
      (by rw [hq]; field_simp <;> ring) (by rw [hhc2, hq]; field_simp <;> ring)
    left
    rw [range_pts_eq_cyclic _ k, range_cSlotTile]
    rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hk, hm, hX]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · -- `b` to the left, `a` to the right: `cSlotTile'`
    have hhc2' : (1 / f * apexH f) ^ 2 = (f ^ 2 - 1) ^ 2 - (f ^ 2 - dBG f / f) ^ 2 := by
      have := (cSlotTile_sides x₀ f hf1).2.2
      simp only [cSlotTile', mkTri_pts₀, mkTri_pts₂] at this
      rw [dist_sq_zero_kapex hf1, ← apexH_sq hf1] at this
      nlinarith [this]
    have hX := third_vertex_coords D hf htgt (X₀ := x₀ + f ^ 2 - dBG f / f) (Y₀ := 1 / f * apexH f)
      hc.ne' hhc hkm (Ne.symm hnk) (Ne.symm hnm) hk hm hXk hXm
      (by rw [hq]; field_simp <;> ring) (by rw [hhc2', hq]; field_simp <;> ring)
    right
    rw [range_pts_eq_cyclic _ k, range_cSlotTile']
    rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hk, hm, hX]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-! ## 6. The general wedge lemma and the two placements of a third tile -/

/-- **The general form of `MarchInduction.edge_in_wedge`.**  Tile `i` has vertices `V = (x₀, 0)`,
`(x₀ − u₁, 0)`, `(x₀ + p₁, h₁)` (its corner at `V` opens to the left, up to the ray
`r₁ = (p₁, h₁)`); tile `j` has vertices `V`, `(x₀ + u₂, 0)`, `(x₀ + p₂, h₂)` (corner opening to
the right, up to `r₂ = (p₂, h₂)`).  A third tile `l` with a vertex at `V` and edges to `E`, `E'`
has `E − V` in the closed wedge between `r₁` and `r₂`: `p₁·w ≤ h₁·u` and `h₂·u ≤ p₂·w`. -/
theorem edge_in_wedge_gen {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    {x₀ u₁ p₁ h₁ u₂ p₂ h₂ : ℝ} (hu₁ : 0 < u₁) (hh₁ : 0 < h₁) (hu₂ : 0 < u₂) (hh₂ : 0 < h₂)
    {i j l : Fin N} (hli : l ≠ i) (hlj : l ≠ j)
    (hA : Set.range (D.tile i).pts = {mkPt x₀ 0, mkPt (x₀ - u₁) 0, mkPt (x₀ + p₁) h₁})
    (hB : Set.range (D.tile j).pts = {mkPt x₀ 0, mkPt (x₀ + u₂) 0, mkPt (x₀ + p₂) h₂})
    {k : Fin 3} (hk : (D.tile l).pts k = mkPt x₀ 0) {E E' : Plane}
    (hEE' : ((D.tile l).pts (k + 1) = E ∧ (D.tile l).pts (k + 2) = E') ∨
            ((D.tile l).pts (k + 1) = E' ∧ (D.tile l).pts (k + 2) = E)) :
    p₁ * (E 1) ≤ h₁ * (E 0 - x₀) ∧ h₂ * (E 0 - x₀) ≤ p₂ * (E 1) := by
  have hf1 : 1 < f := by linarith
  -- heights of the two edge points are `≥ 0`
  have hE1 : 0 ≤ E 1 := by
    have h1 := pts_mem_target D.toDissection l (k + 1)
    have h2 := pts_mem_target D.toDissection l (k + 2)
    rw [htgt] at h1 h2
    rcases hEE' with ⟨h, -⟩ | ⟨-, h⟩
    · rw [h] at h1; exact target_height_nonneg one_pos hf1 _ h1
    · rw [h] at h2; exact target_height_nonneg one_pos hf1 _ h2
  have hE1' : 0 ≤ E' 1 := by
    have h1 := pts_mem_target D.toDissection l (k + 1)
    have h2 := pts_mem_target D.toDissection l (k + 2)
    rw [htgt] at h1 h2
    rcases hEE' with ⟨-, h⟩ | ⟨h, -⟩
    · rw [h] at h2; exact target_height_nonneg one_pos hf1 _ h2
    · rw [h] at h1; exact target_height_nonneg one_pos hf1 _ h1
  -- nondegeneracy: `E − v` and `E' − v` are not parallel
  have hcross : (E 0 - x₀) * (E' 1) - (E 1) * (E' 0 - x₀) ≠ 0 := by
    have := cross_edges_ne_zero (D.tile l) k
    rw [hk] at this
    simp only [mkPt_zero, mkPt_one, sub_zero] at this
    rcases hEE' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at this; exact this
    · rw [h1, h2] at this; intro hc; apply this; linear_combination -hc
  -- the two tiles' vertices at `v`
  obtain ⟨kA, hkA⟩ := mem_range_of_eq hA (Set.mem_insert _ _)
  obtain ⟨kB, hkB⟩ := mem_range_of_eq hB (Set.mem_insert _ _)
  have hEpt : E = mkPt (E 0) (E 1) := plane_ext (by simp) (by simp)
  have hEpt' : E' = mkPt (E' 0) (E' 1) := plane_ext (by simp) (by simp)
  have hw : ∀ ε : ℝ, 0 < ε → 0 < E 1 + ε * E' 1 := by
    intro ε hε
    rcases lt_or_eq_of_le hE1 with h1 | h1
    · positivity
    · rcases lt_or_eq_of_le hE1' with h2 | h2
      · rw [← h1]; simp; positivity
      · exfalso; apply hcross; rw [← h1, ← h2]; ring
  constructor
  · by_contra hlt
    have hlt := not_le.mp hlt
    set δ := p₁ * E 1 - h₁ * (E 0 - x₀) with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨hε, hεm⟩ := push_eps (m := h₁ * (E' 0 - x₀) - p₁ * E' 1) hδpos
    set ε := δ / (2 * (|h₁ * (E' 0 - x₀) - p₁ * E' 1| + 1)) with hεdef
    have hwpos := hw ε hε
    have hb : 0 < (E 1 + ε * E' 1) / h₁ := by positivity
    have ha : 0 < (p₁ * (E 1 + ε * E' 1) - h₁ * (E 0 - x₀ + ε * (E' 0 - x₀))) / (u₁ * h₁) := by
      apply div_pos _ (by positivity)
      nlinarith
    rcases vertex_data_of_range hA hkA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hEE' with ⟨hE, hE'⟩ | ⟨hE, hE'⟩
    · refine combo_dies_pts D.toDissection (Ne.symm hli) hkA hk h1 h2 (hE.trans hEpt) (hE'.trans hEpt')
        (ε := 1) (ε' := ε) one_pos hε ha hb ?_ ?_
      · field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hli) hkA hk h1 h2 (hE.trans hEpt') (hE'.trans hEpt)
        (ε := ε) (ε' := 1) hε one_pos ha hb ?_ ?_
      · field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hli) hkA hk h1 h2 (hE.trans hEpt) (hE'.trans hEpt')
        (ε := 1) (ε' := ε) one_pos hε hb ha ?_ ?_
      · field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hli) hkA hk h1 h2 (hE.trans hEpt') (hE'.trans hEpt)
        (ε := ε) (ε' := 1) hε one_pos hb ha ?_ ?_
      · field_simp; ring
      · field_simp; ring
  · by_contra hlt
    have hlt := not_le.mp hlt
    set δ := h₂ * (E 0 - x₀) - p₂ * E 1 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨hε, hεm⟩ := push_eps (m := p₂ * E' 1 - h₂ * (E' 0 - x₀)) hδpos
    set ε := δ / (2 * (|p₂ * E' 1 - h₂ * (E' 0 - x₀)| + 1)) with hεdef
    have hwpos := hw ε hε
    have hb : 0 < (E 1 + ε * E' 1) / h₂ := by positivity
    have ha : 0 < (h₂ * (E 0 - x₀ + ε * (E' 0 - x₀)) - p₂ * (E 1 + ε * E' 1)) / (u₂ * h₂) := by
      apply div_pos _ (by positivity)
      nlinarith
    rcases vertex_data_of_range hB hkB with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hEE' with ⟨hE, hE'⟩ | ⟨hE, hE'⟩
    · refine combo_dies_pts D.toDissection (Ne.symm hlj) hkB hk h1 h2 (hE.trans hEpt) (hE'.trans hEpt')
        (ε := 1) (ε' := ε) one_pos hε ha hb ?_ ?_
      · field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hlj) hkB hk h1 h2 (hE.trans hEpt') (hE'.trans hEpt)
        (ε := ε) (ε' := 1) hε one_pos ha hb ?_ ?_
      · field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hlj) hkB hk h1 h2 (hE.trans hEpt) (hE'.trans hEpt')
        (ε := 1) (ε' := ε) one_pos hε hb ha ?_ ?_
      · field_simp; ring
      · field_simp; ring
    · refine combo_dies_pts D.toDissection (Ne.symm hlj) hkB hk h1 h2 (hE.trans hEpt') (hE'.trans hEpt)
        (ε := ε) (ε' := 1) hε one_pos hb ha ?_ ?_
      · field_simp; ring
      · field_simp; ring

/-- `MarchInduction.gram_extremal` with `κ ≠ 0` in place of `0 < κ` (the `γ`-wedge is obtuse). -/
theorem gram_extremal' {B C κ a₁ b₁ a₂ b₂ : ℝ} (hB : 0 < B) (hC : 0 < C) (hκ : κ ≠ 0)
    (hdet : 0 < B * C - κ ^ 2)
    (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂)
    (G1 : a₁ ^ 2 * B + 2 * a₁ * b₁ * κ + b₁ ^ 2 * C = B)
    (G2 : a₂ ^ 2 * B + 2 * a₂ * b₂ * κ + b₂ ^ 2 * C = C)
    (G3 : a₁ * a₂ * B + (a₁ * b₂ + a₂ * b₁) * κ + b₁ * b₂ * C = κ) :
    (a₁ = 1 ∧ b₁ = 0 ∧ a₂ = 0 ∧ b₂ = 1) ∨
    (a₁ = 0 ∧ b₂ = 0 ∧ b₁ ^ 2 * C = B ∧ a₂ ^ 2 * B = C) := by
  have hgram : (a₁ * b₂ - a₂ * b₁) ^ 2 * (B * C - κ ^ 2) = 1 * (B * C - κ ^ 2) := by
    have e : (a₁ ^ 2 * B + 2 * a₁ * b₁ * κ + b₁ ^ 2 * C) * (a₂ ^ 2 * B + 2 * a₂ * b₂ * κ + b₂ ^ 2 * C)
        - (a₁ * a₂ * B + (a₁ * b₂ + a₂ * b₁) * κ + b₁ * b₂ * C) ^ 2
        = (a₁ * b₂ - a₂ * b₁) ^ 2 * (B * C - κ ^ 2) := by ring
    rw [G1, G2, G3] at e; linarith
  have hd2 : (a₁ * b₂ - a₂ * b₁) ^ 2 = 1 := mul_right_cancel₀ hdet.ne' hgram
  have hfac : (a₁ * b₂ - a₂ * b₁ - 1) * (a₁ * b₂ - a₂ * b₁ + 1) = 0 := by linear_combination hd2
  rcases mul_eq_zero.mp hfac with h | h
  · have Gd : a₁ * b₂ - a₂ * b₁ = 1 := by linarith
    have hsum : a₂ * B + b₁ * C = 0 := by
      linear_combination b₂ * G3 - (b₂ * κ + a₂ * B) * Gd - b₁ * G2
    have ha₂0 : a₂ = 0 := by nlinarith [mul_nonneg ha₂ hB.le, mul_nonneg hb₁ hC.le]
    have hb₁0 : b₁ = 0 := by nlinarith [mul_nonneg ha₂ hB.le, mul_nonneg hb₁ hC.le]
    subst ha₂0; subst hb₁0
    have h1 : a₁ ^ 2 = 1 := by
      have : (a₁ ^ 2 - 1) * B = 0 := by linear_combination G1
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hB.ne'
    have h2 : b₂ ^ 2 = 1 := by
      have : (b₂ ^ 2 - 1) * C = 0 := by linear_combination G2
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hC.ne'
    left
    refine ⟨?_, rfl, rfl, ?_⟩
    · exact (sq_eq_sq₀ ha₁ zero_le_one).mp (by rw [h1]; norm_num)
    · exact (sq_eq_sq₀ hb₂ zero_le_one).mp (by rw [h2]; norm_num)
  · have Gd : a₁ * b₂ - a₂ * b₁ = -1 := by linarith
    have h1 : b₁ * C = a₂ * B - 2 * a₁ * κ := by
      linear_combination a₂ * G1 - a₁ * G3 + (a₁ * κ + b₁ * C) * Gd
    have h2 : a₂ * B = b₁ * C - 2 * b₂ * κ := by
      linear_combination b₁ * G2 - b₂ * G3 + (b₂ * κ + a₂ * B) * Gd
    have hsum : 2 * κ * (a₁ + b₂) = 0 := by linear_combination h1 + h2
    have hab : a₁ + b₂ = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd (by linarith : κ = 0) hκ
      · exact h
    have ha₁0 : a₁ = 0 := by linarith
    have hb₂0 : b₂ = 0 := by linarith
    subst ha₁0; subst hb₂0
    right
    refine ⟨rfl, rfl, by linear_combination G1, by linear_combination G2⟩

/-- **Extremality in a general wedge, scaled.**  Rays `r₁ = (p₁, h₁)` (length `R₁`) and
`r₂ = (p₂, h₂)` (length `R₂`), with `r₂` clockwise from `r₁` (`p₁h₂ − h₁p₂ < 0`) and the wedge not
right-angled.  Two vectors `(u, w)`, `(u', w')` in the closed wedge, of lengths `ℓ₁`, `ℓ₂`, at
distance `ℓ₃` from each other, with the angle condition `2ℓ₁ℓ₂·⟨r₁,r₂⟩ = (ℓ₁²+ℓ₂²−ℓ₃²)·R₁R₂`
(their angle equals the wedge's opening), are the rays scaled — `(ℓ₁/R₁)r₁, (ℓ₂/R₂)r₂` — or the
reflection `(ℓ₁/R₂)r₂, (ℓ₂/R₁)r₁`. -/
theorem wedge_extremal_gen {p₁ h₁ p₂ h₂ R₁ R₂ ℓ₁ ℓ₂ ℓ₃ : ℝ}
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂)
    (hB : p₁ ^ 2 + h₁ ^ 2 = R₁ ^ 2) (hC : p₂ ^ 2 + h₂ ^ 2 = R₂ ^ 2)
    (hX : p₁ * h₂ - h₁ * p₂ < 0) (hκ : p₁ * p₂ + h₁ * h₂ ≠ 0)
    (hang : 2 * ℓ₁ * ℓ₂ * (p₁ * p₂ + h₁ * h₂) = (ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) * (R₁ * R₂))
    {u w u' w' : ℝ}
    (hw1 : p₁ * w ≤ h₁ * u) (hw2 : h₂ * u ≤ p₂ * w)
    (hw1' : p₁ * w' ≤ h₁ * u') (hw2' : h₂ * u' ≤ p₂ * w')
    (he1 : u ^ 2 + w ^ 2 = ℓ₁ ^ 2) (he2 : u' ^ 2 + w' ^ 2 = ℓ₂ ^ 2)
    (he3 : (u - u') ^ 2 + (w - w') ^ 2 = ℓ₃ ^ 2) :
    (u = ℓ₁ / R₁ * p₁ ∧ w = ℓ₁ / R₁ * h₁ ∧ u' = ℓ₂ / R₂ * p₂ ∧ w' = ℓ₂ / R₂ * h₂) ∨
    (u = ℓ₁ / R₂ * p₂ ∧ w = ℓ₁ / R₂ * h₂ ∧ u' = ℓ₂ / R₁ * p₁ ∧ w' = ℓ₂ / R₁ * h₁) := by
  have hXne : p₁ * h₂ - h₁ * p₂ ≠ 0 := hX.ne
  -- the scaled wedge coordinates
  obtain ⟨A₁, hA₁⟩ : ∃ A, A = R₁ / ℓ₁ * ((u * h₂ - w * p₂) / (p₁ * h₂ - h₁ * p₂)) := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B, B = R₁ / ℓ₁ * ((p₁ * w - h₁ * u) / (p₁ * h₂ - h₁ * p₂)) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A, A = R₂ / ℓ₂ * ((u' * h₂ - w' * p₂) / (p₁ * h₂ - h₁ * p₂)) := ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = R₂ / ℓ₂ * ((p₁ * w' - h₁ * u') / (p₁ * h₂ - h₁ * p₂)) := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁]; exact mul_nonneg (by positivity) (div_nonneg_of_nonpos (by linarith) hX.le)
  have hB₁0 : 0 ≤ B₁ := by
    rw [hB₁]; exact mul_nonneg (by positivity) (div_nonneg_of_nonpos (by linarith) hX.le)
  have hA₂0 : 0 ≤ A₂ := by
    rw [hA₂]; exact mul_nonneg (by positivity) (div_nonneg_of_nonpos (by linarith) hX.le)
  have hB₂0 : 0 ≤ B₂ := by
    rw [hB₂]; exact mul_nonneg (by positivity) (div_nonneg_of_nonpos (by linarith) hX.le)
  have cramer : ∀ a b : ℝ,
      (a * h₂ - b * p₂) / (p₁ * h₂ - h₁ * p₂) * p₁ + (p₁ * b - h₁ * a) / (p₁ * h₂ - h₁ * p₂) * p₂ = a ∧
      (a * h₂ - b * p₂) / (p₁ * h₂ - h₁ * p₂) * h₁ + (p₁ * b - h₁ * a) / (p₁ * h₂ - h₁ * p₂) * h₂ = b := by
    intro a b
    constructor <;>
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hXne] <;> ring
  have hu1 : A₁ * p₁ + B₁ * p₂ = R₁ / ℓ₁ * u := by
    rw [hA₁, hB₁]; linear_combination (R₁ / ℓ₁) * (cramer u w).1
  have hv1 : A₁ * h₁ + B₁ * h₂ = R₁ / ℓ₁ * w := by
    rw [hA₁, hB₁]; linear_combination (R₁ / ℓ₁) * (cramer u w).2
  have hu2 : A₂ * p₁ + B₂ * p₂ = R₂ / ℓ₂ * u' := by
    rw [hA₂, hB₂]; linear_combination (R₂ / ℓ₂) * (cramer u' w').1
  have hv2 : A₂ * h₁ + B₂ * h₂ = R₂ / ℓ₂ * w' := by
    rw [hA₂, hB₂]; linear_combination (R₂ / ℓ₂) * (cramer u' w').2
  -- Gram data of the wedge
  have hBpos : 0 < p₁ ^ 2 + h₁ ^ 2 := by rw [hB]; positivity
  have hCpos : 0 < p₂ ^ 2 + h₂ ^ 2 := by rw [hC]; positivity
  have hdet : 0 < (p₁ ^ 2 + h₁ ^ 2) * (p₂ ^ 2 + h₂ ^ 2) - (p₁ * p₂ + h₁ * h₂) ^ 2 := by
    have : (p₁ ^ 2 + h₁ ^ 2) * (p₂ ^ 2 + h₂ ^ 2) - (p₁ * p₂ + h₁ * h₂) ^ 2
        = (p₁ * h₂ - h₁ * p₂) ^ 2 := by ring
    rw [this, sq]; exact mul_pos_of_neg_of_neg hX hX
  have hinner : u * u' + w * w' = (ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) / 2 := by
    linear_combination (1/2 : ℝ) * he1 + (1/2 : ℝ) * he2 - (1/2 : ℝ) * he3
  have G1 : A₁ ^ 2 * (p₁ ^ 2 + h₁ ^ 2) + 2 * A₁ * B₁ * (p₁ * p₂ + h₁ * h₂)
      + B₁ ^ 2 * (p₂ ^ 2 + h₂ ^ 2) = p₁ ^ 2 + h₁ ^ 2 := by
    have key : A₁ ^ 2 * (p₁ ^ 2 + h₁ ^ 2) + 2 * A₁ * B₁ * (p₁ * p₂ + h₁ * h₂)
        + B₁ ^ 2 * (p₂ ^ 2 + h₂ ^ 2) = (A₁ * p₁ + B₁ * p₂) ^ 2 + (A₁ * h₁ + B₁ * h₂) ^ 2 := by ring
    rw [key, hu1, hv1, hB]
    have : (R₁ / ℓ₁ * u) ^ 2 + (R₁ / ℓ₁ * w) ^ 2 = (R₁ / ℓ₁) ^ 2 * (u ^ 2 + w ^ 2) := by ring
    rw [this, he1]; field_simp
  have G2 : A₂ ^ 2 * (p₁ ^ 2 + h₁ ^ 2) + 2 * A₂ * B₂ * (p₁ * p₂ + h₁ * h₂)
      + B₂ ^ 2 * (p₂ ^ 2 + h₂ ^ 2) = p₂ ^ 2 + h₂ ^ 2 := by
    have key : A₂ ^ 2 * (p₁ ^ 2 + h₁ ^ 2) + 2 * A₂ * B₂ * (p₁ * p₂ + h₁ * h₂)
        + B₂ ^ 2 * (p₂ ^ 2 + h₂ ^ 2) = (A₂ * p₁ + B₂ * p₂) ^ 2 + (A₂ * h₁ + B₂ * h₂) ^ 2 := by ring
    rw [key, hu2, hv2, hC]
    have : (R₂ / ℓ₂ * u') ^ 2 + (R₂ / ℓ₂ * w') ^ 2 = (R₂ / ℓ₂) ^ 2 * (u' ^ 2 + w' ^ 2) := by ring
    rw [this, he2]; field_simp
  have G3 : A₁ * A₂ * (p₁ ^ 2 + h₁ ^ 2) + (A₁ * B₂ + A₂ * B₁) * (p₁ * p₂ + h₁ * h₂)
      + B₁ * B₂ * (p₂ ^ 2 + h₂ ^ 2) = p₁ * p₂ + h₁ * h₂ := by
    have key : A₁ * A₂ * (p₁ ^ 2 + h₁ ^ 2) + (A₁ * B₂ + A₂ * B₁) * (p₁ * p₂ + h₁ * h₂)
        + B₁ * B₂ * (p₂ ^ 2 + h₂ ^ 2)
        = (A₁ * p₁ + B₁ * p₂) * (A₂ * p₁ + B₂ * p₂) + (A₁ * h₁ + B₁ * h₂) * (A₂ * h₁ + B₂ * h₂) := by
      ring
    rw [key, hu1, hv1, hu2, hv2]
    have : R₁ / ℓ₁ * u * (R₂ / ℓ₂ * u') + R₁ / ℓ₁ * w * (R₂ / ℓ₂ * w')
        = R₁ * R₂ / (ℓ₁ * ℓ₂) * (u * u' + w * w') := by ring
    rw [this, hinner]
    field_simp
    linear_combination (-1 : ℝ) * hang
  rcases gram_extremal' hBpos hCpos hκ hdet hA₁0 hB₁0 hA₂0 hB₂0 G1 G2 G3 with
    ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    rw [h1, h2] at hu1 hv1; rw [h3, h4] at hu2 hv2
    have e1 : p₁ = R₁ / ℓ₁ * u := by linarith [hu1]
    have e2 : h₁ = R₁ / ℓ₁ * w := by linarith [hv1]
    have e3 : p₂ = R₂ / ℓ₂ * u' := by linarith [hu2]
    have e4 : h₂ = R₂ / ℓ₂ * w' := by linarith [hv2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1]; field_simp
    · rw [e2]; field_simp
    · rw [e3]; field_simp
    · rw [e4]; field_simp
  · right
    rw [hB, hC] at h3 h4
    have hB₁v : B₁ = R₁ / R₂ := by
      refine (sq_eq_sq₀ hB₁0 (by positivity)).mp ?_
      field_simp; linear_combination h3
    have hA₂v : A₂ = R₂ / R₁ := by
      refine (sq_eq_sq₀ hA₂0 (by positivity)).mp ?_
      field_simp; linear_combination h4
    rw [h1, hB₁v] at hu1 hv1; rw [h2, hA₂v] at hu2 hv2
    have e1 : R₁ / R₂ * p₂ = R₁ / ℓ₁ * u := by linarith [hu1]
    have e2 : R₁ / R₂ * h₂ = R₁ / ℓ₁ * w := by linarith [hv1]
    have e3 : R₂ / R₁ * p₁ = R₂ / ℓ₂ * u' := by linarith [hu2]
    have e4 : R₂ / R₁ * h₁ = R₂ / ℓ₂ * w' := by linarith [hv2]
    have f1 : p₂ = R₂ / R₁ * (R₁ / ℓ₁ * u) := by rw [← e1]; field_simp
    have f2 : h₂ = R₂ / R₁ * (R₁ / ℓ₁ * w) := by rw [← e2]; field_simp
    have f3 : p₁ = R₁ / R₂ * (R₂ / ℓ₂ * u') := by rw [← e3]; field_simp
    have f4 : h₁ = R₁ / R₂ * (R₂ / ℓ₂ * w') := by rw [← e4]; field_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [f1]; field_simp
    · rw [f2]; field_simp
    · rw [f3]; field_simp
    · rw [f4]; field_simp

/-- **THE TWO PLACEMENTS OF A THIRD TILE**, in vertex-set form.  Neighbour tiles `i`, `j` as in
`edge_in_wedge_gen`; a tile `l` with vertex `k` at `V`, opposite side `ℓ₃`, adjacent sides
`{ℓ₁, ℓ₂}` in either order, whose corner angle equals the wedge's opening (`hang`).  Then its
vertex set is `{V, V + (ℓ₁/R₁)r₁, V + (ℓ₂/R₂)r₂}` or `{V, V + (ℓ₂/R₁)r₁, V + (ℓ₁/R₂)r₂}`. -/
theorem third_tile_range {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    {x₀ u₁ p₁ h₁ u₂ p₂ h₂ R₁ R₂ ℓ₁ ℓ₂ ℓ₃ : ℝ}
    (hu₁ : 0 < u₁) (hh₁ : 0 < h₁) (hu₂ : 0 < u₂) (hh₂ : 0 < h₂)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂)
    (hB : p₁ ^ 2 + h₁ ^ 2 = R₁ ^ 2) (hC : p₂ ^ 2 + h₂ ^ 2 = R₂ ^ 2)
    (hX : p₁ * h₂ - h₁ * p₂ < 0) (hκ : p₁ * p₂ + h₁ * h₂ ≠ 0)
    (hang : 2 * ℓ₁ * ℓ₂ * (p₁ * p₂ + h₁ * h₂) = (ℓ₁ ^ 2 + ℓ₂ ^ 2 - ℓ₃ ^ 2) * (R₁ * R₂))
    {i j l : Fin N} (hli : l ≠ i) (hlj : l ≠ j)
    (hA : Set.range (D.tile i).pts = {mkPt x₀ 0, mkPt (x₀ - u₁) 0, mkPt (x₀ + p₁) h₁})
    (hB' : Set.range (D.tile j).pts = {mkPt x₀ 0, mkPt (x₀ + u₂) 0, mkPt (x₀ + p₂) h₂})
    {k : Fin 3} (hk : (D.tile l).pts k = mkPt x₀ 0)
    (hopp : dist ((D.tile l).pts (k + 1)) ((D.tile l).pts (k + 2)) = ℓ₃)
    (hsides : (dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = ℓ₁ ∧
               dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = ℓ₂) ∨
              (dist ((D.tile l).pts k) ((D.tile l).pts (k + 1)) = ℓ₂ ∧
               dist ((D.tile l).pts k) ((D.tile l).pts (k + 2)) = ℓ₁)) :
    Set.range (D.tile l).pts
      = {mkPt x₀ 0, mkPt (x₀ + ℓ₁ / R₁ * p₁) (ℓ₁ / R₁ * h₁), mkPt (x₀ + ℓ₂ / R₂ * p₂) (ℓ₂ / R₂ * h₂)} ∨
    Set.range (D.tile l).pts
      = {mkPt x₀ 0, mkPt (x₀ + ℓ₂ / R₁ * p₁) (ℓ₂ / R₁ * h₁), mkPt (x₀ + ℓ₁ / R₂ * p₂) (ℓ₁ / R₂ * h₂)} := by
  have hw1 := edge_in_wedge_gen D hf htgt hu₁ hh₁ hu₂ hh₂ hli hlj hA hB' hk
    (E := (D.tile l).pts (k + 1)) (E' := (D.tile l).pts (k + 2)) (Or.inl ⟨rfl, rfl⟩)
  have hw2 := edge_in_wedge_gen D hf htgt hu₁ hh₁ hu₂ hh₂ hli hlj hA hB' hk
    (E := (D.tile l).pts (k + 2)) (E' := (D.tile l).pts (k + 1)) (Or.inr ⟨rfl, rfl⟩)
  set E := (D.tile l).pts (k + 1) with hE
  set E' := (D.tile l).pts (k + 2) with hE'
  have hEpt : E = mkPt (E 0) (E 1) := plane_ext (by simp) (by simp)
  have hEpt' : E' = mkPt (E' 0) (E' 1) := plane_ext (by simp) (by simp)
  have hd1 : dist ((D.tile l).pts k) E ^ 2 = (E 0 - x₀) ^ 2 + E 1 ^ 2 := by
    rw [dist_comm, hk, dist_sq_pt_mkPt]; ring
  have hd2 : dist ((D.tile l).pts k) E' ^ 2 = (E' 0 - x₀) ^ 2 + E' 1 ^ 2 := by
    rw [dist_comm, hk, dist_sq_pt_mkPt]; ring
  have hd12 : dist E E' ^ 2 = ((E 0 - x₀) - (E' 0 - x₀)) ^ 2 + (E 1 - E' 1) ^ 2 := by
    rw [dist_sq_pts]; ring
  have hopp2 : ((E 0 - x₀) - (E' 0 - x₀)) ^ 2 + (E 1 - E' 1) ^ 2 = ℓ₃ ^ 2 := by
    rw [← hd12, hopp]
  have hrange : Set.range (D.tile l).pts = {mkPt x₀ 0, E, E'} := by
    rw [range_pts_eq_cyclic _ k, hk]
  rcases hsides with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
  · have he1 : (E 0 - x₀) ^ 2 + E 1 ^ 2 = ℓ₁ ^ 2 := by rw [← hd1, hs1]
    have he2 : (E' 0 - x₀) ^ 2 + E' 1 ^ 2 = ℓ₂ ^ 2 := by rw [← hd2, hs2]
    rcases wedge_extremal_gen hR₁ hR₂ hℓ₁ hℓ₂ hB hC hX hκ hang hw1.1 hw1.2 hw2.1 hw2.2 he1 he2 hopp2
      with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · left
      rw [hrange, hEpt, hEpt', h2, h4, show E 0 = x₀ + ℓ₁ / R₁ * p₁ by linarith,
        show E' 0 = x₀ + ℓ₂ / R₂ * p₂ by linarith]
    · right
      rw [hrange, hEpt, hEpt', h2, h4, show E 0 = x₀ + ℓ₁ / R₂ * p₂ by linarith,
        show E' 0 = x₀ + ℓ₂ / R₁ * p₁ by linarith]
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · have he1 : (E 0 - x₀) ^ 2 + E 1 ^ 2 = ℓ₂ ^ 2 := by rw [← hd1, hs1]
    have he2 : (E' 0 - x₀) ^ 2 + E' 1 ^ 2 = ℓ₁ ^ 2 := by rw [← hd2, hs2]
    have hang' : 2 * ℓ₂ * ℓ₁ * (p₁ * p₂ + h₁ * h₂) = (ℓ₂ ^ 2 + ℓ₁ ^ 2 - ℓ₃ ^ 2) * (R₁ * R₂) := by
      linear_combination hang
    rcases wedge_extremal_gen hR₁ hR₂ hℓ₂ hℓ₁ hB hC hX hκ hang' hw1.1 hw1.2 hw2.1 hw2.2 he1 he2 hopp2
      with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · right
      rw [hrange, hEpt, hEpt', h2, h4, show E 0 = x₀ + ℓ₂ / R₁ * p₁ by linarith,
        show E' 0 = x₀ + ℓ₁ / R₂ * p₂ by linarith]
    · left
      rw [hrange, hEpt, hEpt', h2, h4, show E 0 = x₀ + ℓ₂ / R₂ * p₂ by linarith,
        show E' 0 = x₀ + ℓ₁ / R₁ * p₁ by linarith]
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-! ## 7. The neighbour tiles in the master lemma's shape -/

theorem mkPt_congr {x y x' y' : ℝ} (hx : x = x') (hy : y = y') : mkPt x y = mkPt x' y' := by
  rw [hx, hy]

theorem triple_congr {A B C A' B' C' : Plane} (h1 : A = A') (h2 : B = B') (h3 : C = C') :
    ({A, B, C} : Set Plane) = {A', B', C'} := by rw [h1, h2, h3]

/-- The coordinate normaliser used in every instantiation: unfold the slot heights and `dBG`,
then `field_simp; ring`. -/
macro "slot_arith" : tactic =>
  `(tactic| ((try simp only [hB, hC]); (try unfold dGB); (try unfold dBG); (first | done | rfl | (field_simp <;> ring))))

/-- The `b`-slot apex height `f·h/(f²−1)`. -/
noncomputable abbrev hB (f : ℝ) : ℝ := f / (f ^ 2 - 1) * apexH f
/-- The `c`-slot apex height `h/f`. -/
noncomputable abbrev hC (f : ℝ) : ℝ := 1 / f * apexH f

section neighbours
variable {f : ℝ} (hf : 1 < f) (x₀ : ℝ)
include hf

theorem left_BG : Set.range (aTileBG (x₀ - f) f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ - f) 0, mkPt (x₀ + (dBG f - f)) (apexH f)} := by
  rw [range_aTileBG]; exact triple_congr (mkPt_congr (by ring) rfl) rfl (mkPt_congr (by ring) rfl)

theorem left_GB : Set.range (aTileGB (x₀ - f) f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ - f) 0, mkPt (x₀ + (dGB f - f)) (apexH f)} := by
  rw [range_aTileGB, Set.insert_comm]
  exact triple_congr (mkPt_congr (by ring) rfl) rfl (mkPt_congr (by ring) rfl)

theorem left_bSlot' : Set.range (bSlotTile' (x₀ - (f ^ 2 - 1)) f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ - (f ^ 2 - 1)) 0, mkPt (x₀ + 1 / 2) (hB f)} := by
  rw [range_bSlotTile', Set.insert_comm]
  exact triple_congr (mkPt_congr (by ring) rfl) rfl (mkPt_congr (by ring) rfl)

theorem left_bSlot : Set.range (bSlotTile (x₀ - (f ^ 2 - 1)) f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ - (f ^ 2 - 1)) 0, mkPt (x₀ + (-(f ^ 2 - 1) - 1 / 2)) (hB f)} := by
  rw [range_bSlotTile, Set.insert_comm]
  exact triple_congr (mkPt_congr (by ring) rfl) rfl (mkPt_congr (by ring) rfl)

theorem left_cSlot : Set.range (cSlotTile (x₀ - f ^ 2) f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ - f ^ 2) 0, mkPt (x₀ + (dBG f / f - f ^ 2)) (hC f)} := by
  rw [range_cSlotTile, Set.insert_comm]
  exact triple_congr (mkPt_congr (by ring) rfl) rfl (mkPt_congr (by ring) rfl)

theorem left_cSlot' : Set.range (cSlotTile' (x₀ - f ^ 2) f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ - f ^ 2) 0, mkPt (x₀ + (-(dBG f / f))) (hC f)} := by
  rw [range_cSlotTile', Set.insert_comm]
  exact triple_congr (mkPt_congr (by ring) rfl) rfl (mkPt_congr (by ring) rfl)

theorem right_BG : Set.range (aTileBG x₀ f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ + f) 0, mkPt (x₀ + dBG f) (apexH f)} := by
  rw [range_aTileBG, Set.insert_comm]

theorem right_GB : Set.range (aTileGB x₀ f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ + f) 0, mkPt (x₀ + dGB f) (apexH f)} := by
  rw [range_aTileGB]

theorem right_bSlot' : Set.range (bSlotTile' x₀ f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ + (f ^ 2 - 1)) 0, mkPt (x₀ + (f ^ 2 - 1 + 1 / 2)) (hB f)} := by
  rw [range_bSlotTile']; exact triple_congr rfl rfl (mkPt_congr (by ring) rfl)

theorem right_bSlot : Set.range (bSlotTile x₀ f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ + (f ^ 2 - 1)) 0, mkPt (x₀ + (-1 / 2)) (hB f)} := by
  rw [range_bSlotTile]; exact triple_congr rfl rfl (mkPt_congr (by ring) rfl)

theorem right_cSlot : Set.range (cSlotTile x₀ f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ + f ^ 2) 0, mkPt (x₀ + dBG f / f) (hC f)} := by
  rw [range_cSlotTile]

theorem right_cSlot' : Set.range (cSlotTile' x₀ f hf).pts
    = {mkPt x₀ 0, mkPt (x₀ + f ^ 2) 0, mkPt (x₀ + (f ^ 2 - dBG f / f)) (hC f)} := by
  rw [range_cSlotTile']; exact triple_congr rfl rfl (mkPt_congr (by ring) rfl)

end neighbours

/-! ### The candidate placements, as sets of three points -/

/-- The **cap** over a `b`-slot: `V`, `(x₀ + 1/2, h_b)`, `(x₀ + b + 1/2, h_b)` — a `β`-tile whose
`b`-edge is horizontal at the `b`-tile's apex height, its `c`-edge along the `b`-tile's `c`-edge. -/
noncomputable def bCapSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ + 1 / 2) (hB f), mkPt (x₀ + (f ^ 2 - 1) + 1 / 2) (hB f)}

/-- The **overshoot** placement at a `b`-slot: `V`, `(x₀ + f/2, (c/b)·h)` (its `c`-edge runs along
the left tile's `b`-edge one unit past that tile's apex — the offset filler's overshoot vertex),
`(x₀ + (2f²−1)/(2f), h/b)` (its `a`-edge along the `b`-tile's `c`-edge). -/
noncomputable def bOverSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ + f / 2) (f ^ 2 / (f ^ 2 - 1) * apexH f),
   mkPt (x₀ + (2 * f ^ 2 - 1) / (2 * f)) (apexH f / (f ^ 2 - 1))}

/-- The mirror images (for a `γ`-tile on the right, `GB`): cap and overshoot opening to the left. -/
noncomputable def bCapMSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ - 1 / 2) (hB f), mkPt (x₀ - (f ^ 2 - 1) - 1 / 2) (hB f)}

noncomputable def bOverMSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ - f / 2) (f ^ 2 / (f ^ 2 - 1) * apexH f),
   mkPt (x₀ - (2 * f ^ 2 - 1) / (2 * f)) (apexH f / (f ^ 2 - 1))}

/-- The mirrored fillers at `V` (the `GB` march's fillers): flush and offset opening to the left. -/
noncomputable def flushMSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ - (dBG f - f)) (apexH f), mkPt (x₀ - dBG f) (apexH f)}

noncomputable def offsetMSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ - (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f),
   mkPt (x₀ - f / 2) (f ^ 2 / (f ^ 2 - 1) * apexH f)}

/-- The flat **cap** over a `c`-slot: a `γ`-tile with a horizontal `c`-edge at the `c`-tile's apex
height, sharing the `c`-tile's `b`-edge. -/
noncomputable def cCapSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ + dBG f / f) (hC f), mkPt (x₀ + (dBG f / f - f ^ 2)) (hC f)}

/-- The **split** placement at a `c|a` junction (`cSlotTile + BG`): the `γ`-tile's `a`-edge along
the `c`-tile's `b`-edge, its `b`-edge along the `BG` tile's `c`-edge, one unit short of its apex. -/
noncomputable def cSplitSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ - (2 * f ^ 2 - 1) / (2 * f)) (apexH f / (f ^ 2 - 1)),
   mkPt (x₀ + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)}

/-- The mirror of `cCapSet`: the flat `γ`-cap over a `c`-slot whose `β`-end is at `V`. -/
noncomputable def cCapMSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ - dBG f / f) (hC f), mkPt (x₀ - dBG f / f + f ^ 2) (hC f)}

/-- The mirror of `cSplitSet`, at a `c'|b'` pin. -/
noncomputable def cSplitMSet (x₀ f : ℝ) : Set Plane :=
  {mkPt x₀ 0, mkPt (x₀ - (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f),
   mkPt (x₀ + (2 * f ^ 2 - 1) / (2 * f)) (apexH f / (f ^ 2 - 1))}

/-! ### Coordinate facts shared by the instantiations -/

section coords
variable {f : ℝ} (hf : 2 ≤ f)
include hf

theorem hf1' : 1 < f := by linarith
theorem hb_pos : 0 < f ^ 2 - 1 := by nlinarith
theorem hB_pos : 0 < hB f := by
  have := apexH_pos (hf1' hf); have := hb_pos hf; positivity
theorem hC_pos : 0 < hC f := by
  have := apexH_pos (hf1' hf); positivity
theorem p_pos : 0 < dBG f - f := by linarith [dBG_gt_f (hf1' hf)]

/-- `(dBG − f)² + h² = b²`. -/
theorem sq_r_BG_right : (dBG f - f) ^ 2 + apexH f ^ 2 = (f ^ 2 - 1) ^ 2 := by
  rw [apexH_sq (hf1' hf)]; exact bg_right f (by linarith : (0:ℝ) < f).ne'
/-- `dBG² + h² = c²`. -/
theorem sq_r_BG_left : dBG f ^ 2 + apexH f ^ 2 = (f ^ 2) ^ 2 := by
  rw [apexH_sq (hf1' hf)]; exact bg_left f (by linarith : (0:ℝ) < f).ne'
/-- `(dGB − f)² + h² = c²`. -/
theorem sq_r_GB_right : (dGB f - f) ^ 2 + apexH f ^ 2 = (f ^ 2) ^ 2 := by
  rw [apexH_sq (hf1' hf)]; exact gb_right f (by linarith : (0:ℝ) < f).ne'
/-- `dGB² + h² = b²`. -/
theorem sq_r_GB_left : dGB f ^ 2 + apexH f ^ 2 = (f ^ 2 - 1) ^ 2 := by
  rw [apexH_sq (hf1' hf)]; exact gb_left f (by linarith : (0:ℝ) < f).ne'
/-- `(1/2)² + h_b² = a²`. -/
theorem sq_r_b_a : (1 / 2) ^ 2 + hB f ^ 2 = f ^ 2 := by
  have := hb_pos hf
  simp only [hB]; rw [mul_pow, apexH_sq (hf1' hf)]; unfold h2; field_simp; ring
/-- `(b + 1/2)² + h_b² = c²`. -/
theorem sq_r_b_c : (f ^ 2 - 1 + 1 / 2) ^ 2 + hB f ^ 2 = (f ^ 2) ^ 2 := by
  have := hb_pos hf
  simp only [hB]; rw [mul_pow, apexH_sq (hf1' hf)]; unfold h2; field_simp; ring
/-- `(dBG/f)² + h_c² = a²`. -/
theorem sq_r_c_a : (dBG f / f) ^ 2 + hC f ^ 2 = f ^ 2 := by
  have hf0 : (0:ℝ) < f := by linarith
  simp only [hC]; rw [mul_pow, apexH_sq (hf1' hf)]; unfold h2 dBG; field_simp; ring
/-- `(c − dBG/f)² + h_c² = b²`. -/
theorem sq_r_c_b : (f ^ 2 - dBG f / f) ^ 2 + hC f ^ 2 = (f ^ 2 - 1) ^ 2 := by
  have hf0 : (0:ℝ) < f := by linarith
  simp only [hC]; rw [mul_pow, apexH_sq (hf1' hf)]; unfold h2 dBG; field_simp; ring

/-- `(dBG/f − c)² + h_c² = b²` (the `c`-tile's `b`-edge at its `α`-end, as a left neighbour). -/
theorem sq_r_c_b' : (dBG f / f - f ^ 2) ^ 2 + hC f ^ 2 = (f ^ 2 - 1) ^ 2 := by
  have := sq_r_c_b hf
  have e : (dBG f / f - f ^ 2) ^ 2 = (f ^ 2 - dBG f / f) ^ 2 := by ring
  rw [e]; exact this
/-- `(−dBG/f)² + h_c² = a²`. -/
theorem sq_r_c_a' : (-(dBG f / f)) ^ 2 + hC f ^ 2 = f ^ 2 := by
  have := sq_r_c_a hf
  have e : (-(dBG f / f)) ^ 2 = (dBG f / f) ^ 2 := by ring
  rw [e]; exact this

/-- `(−1/2)² + h_b² = a²`. -/
theorem sq_r_b_a' : (-1 / 2) ^ 2 + hB f ^ 2 = f ^ 2 := by
  have := sq_r_b_a hf
  have e : (-1 / 2 : ℝ) ^ 2 = (1 / 2) ^ 2 := by ring
  rw [e]; exact this

/-- `h · h_b = (f/b) · h2`. -/
theorem h_mul_hB : apexH f * hB f = f / (f ^ 2 - 1) * h2 f := by
  simp only [hB]; rw [← apexH_sq (hf1' hf)]; ring
theorem h_mul_hC : apexH f * hC f = 1 / f * h2 f := by
  simp only [hC]; rw [← apexH_sq (hf1' hf)]; ring
theorem h_mul_h : apexH f * apexH f = h2 f := by rw [← apexH_sq (hf1' hf)]; ring

end coords

/-! ## 8. The junction theorems -/

/-- **THE `a|b` JUNCTION.**  `BG` on `[x₀ − f, x₀]` and a tile laying `b` on `[x₀, x₀ + b]`:
the `b`-tile is `bSlotTile' x₀` (the other reflection presents `γ` against the `BG` tile's `γ` and
dies), and exactly one further tile covers `V = (x₀, 0)`, presenting `β`, with vertex set
`bCapSet x₀ f` or `bOverSet x₀ f`. -/
theorem junction_a_b {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (aTileBG (x₀ - f) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + (f ^ 2 - 1)) 0) :
    Set.range (D.tile j).pts = Set.range (bSlotTile' x₀ f (by linarith)).pts ∧
    ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = β ∧
      (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = β → l' = l) ∧
      (Set.range (D.tile l).pts = bCapSet x₀ f ∨ Set.range (D.tile l).pts = bOverSet x₀ f) := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb := hb_pos hf
  have hh := apexH_pos hf1
  have hiγ : (D.tile i).localAngle (mkPt x₀ 0) = γ := by
    have := (aBG_angles D hf hM hi).2; rwa [show x₀ - f + f = x₀ by ring] at this
  have hij : i ≠ j := by
    refine ne_of_vertex D.toDissection hi hm ?_
    rw [range_aTileBG]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_snd hh.ne⟩
  have hj : Set.range (D.tile j).pts = Set.range (bSlotTile' x₀ f hf1).pts := by
    rcases b_letter_tile D hf htgt hM hkm hk hm with h | h
    · exact absurd (bSlot_angles D hf hM h).1 (fun hjγ => no_two_gamma D hf htgt hM hA hx0 hxL hij hiγ hjγ)
    · exact h
  refine ⟨hj, ?_⟩
  have hjα := (bSlot'_angles D hf hM hj).1
  obtain ⟨l, hli, hlj, hl, huniq⟩ := third_of_gamma_alpha D hf htgt hM hA hx0 hxL hiγ hjα
  refine ⟨l, hli, hlj, hl, huniq, ?_⟩
  obtain ⟨k', hk', hopp, hsides⟩ := beta_corner_data D hf hM hA hl
  have hA' := hi; rw [left_BG hf1] at hA'
  have hB' := hj; rw [right_bSlot' hf1] at hB'
  have hr := third_tile_range D hf htgt (R₁ := f ^ 2 - 1) (R₂ := f ^ 2) (ℓ₁ := f) (ℓ₂ := f ^ 2)
    (ℓ₃ := f ^ 2 - 1) hf0 hh hb (hB_pos hf) hb (by positivity) hf0 (by positivity)
    (sq_r_BG_right hf) (sq_r_b_c hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
  · refine hr.imp (fun h => h.trans (triple_congr rfl ?_ ?_)) (fun h => h.trans (triple_congr rfl ?_ ?_))
    · exact mkPt_congr (by slot_arith) (by slot_arith)
    · exact mkPt_congr (by slot_arith) (by slot_arith)
    · exact mkPt_congr (by slot_arith) (by slot_arith)
    · exact mkPt_congr (by slot_arith) (by slot_arith)
  · -- `r₂` is clockwise from `r₁`: `(dBG − f)·h_b − h·(b + 1/2) = −b·h < 0`
    have : (dBG f - f) * hB f - apexH f * (f ^ 2 - 1 + 1 / 2) = -((f ^ 2 - 1) * apexH f) := by
      simp only [hB]; unfold dBG; field_simp; ring
    rw [this]; have : 0 < (f ^ 2 - 1) * apexH f := by positivity
    linarith
  · -- `κ = b · dBG > 0`
    have : (dBG f - f) * (f ^ 2 - 1 + 1 / 2) + apexH f * hB f = (f ^ 2 - 1) * dBG f := by
      rw [h_mul_hB hf]; unfold dBG h2; field_simp; ring
    rw [this]; exact (mul_pos hb (dBG_pos hf1)).ne'
  · -- the angle condition: the wedge opening is `β`
    rw [h_mul_hB hf]; unfold dBG h2; field_simp; ring

theorem triple_swap {A B C : Plane} : ({A, B, C} : Set Plane) = {A, C, B} := by
  rw [Set.pair_comm]

/-- The flush filler of the virtual junction at `x₀`, in the shape the master lemma produces. -/
theorem flush_at {f : ℝ} (hf : 1 < f) (x₀ : ℝ) :
    Set.range (flushFiller (x₀ - f) f hf).pts
      = {mkPt x₀ 0, mkPt (x₀ + (dBG f - f)) (apexH f), mkPt (x₀ + dBG f) (apexH f)} := by
  rw [range_flushFiller, triple_swap]
  exact triple_congr (mkPt_congr (by ring) rfl) (mkPt_congr (by ring) rfl) (mkPt_congr (by ring) rfl)

/-- The offset filler of the virtual junction at `x₀`. -/
theorem offset_at {f : ℝ} (hf : 1 < f) (x₀ : ℝ) :
    Set.range (offsetFiller (x₀ - f) f hf).pts
      = {mkPt x₀ 0, mkPt (x₀ + f / 2) (f ^ 2 / (f ^ 2 - 1) * apexH f),
         mkPt (x₀ + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)} := by
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  rw [range_offsetFiller, triple_swap]
  refine triple_congr (mkPt_congr (by ring) rfl) (mkPt_congr ?_ rfl) (mkPt_congr (by ring) rfl)
  unfold dBG; field_simp <;> ring

section more_coords
variable {f : ℝ} (hf : 2 ≤ f)
include hf

theorem hB_mul_hC : hB f * hC f = 1 / (f ^ 2 - 1) * h2 f := by
  have hf0 : (0:ℝ) < f := by linarith
  simp only [hB, hC]; rw [← apexH_sq (hf1' hf)]; field_simp <;> ring
theorem hC_mul_h : hC f * apexH f = 1 / f * h2 f := by rw [mul_comm]; exact h_mul_hC hf
theorem hB_mul_h : hB f * apexH f = f / (f ^ 2 - 1) * h2 f := by rw [mul_comm]; exact h_mul_hB hf
theorem hC_mul_hB : hC f * hB f = 1 / (f ^ 2 - 1) * h2 f := by rw [mul_comm]; exact hB_mul_hC hf
theorem dGB_eq : dGB f = -(dBG f - f) := by unfold dGB dBG; field_simp; ring

end more_coords

/-- **THE `b|a` JUNCTION** (the `b`-tile in its forced reflection `bSlotTile'`).  A tile laying
`a` on `[x₀, x₀ + f]` after `bSlotTile' (x₀ − b)` is `BG` (`GB` presents `γ` against the
`b`-tile's `γ` and dies), and the junction carries exactly one further tile, presenting `α`,
whose vertex set is that of the **flush or offset filler of the virtual junction** — the same two
chiralities as at an `a|a` junction. -/
theorem junction_b'_a {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (bSlotTile' (x₀ - (f ^ 2 - 1)) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + f) 0) :
    Set.range (D.tile j).pts = Set.range (aTileBG x₀ f (by linarith)).pts ∧
    ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = α ∧
      (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = α → l' = l) ∧
      (Set.range (D.tile l).pts = Set.range (flushFiller (x₀ - f) f (by linarith)).pts ∨
       Set.range (D.tile l).pts = Set.range (offsetFiller (x₀ - f) f (by linarith)).pts) := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb := hb_pos hf
  have hh := apexH_pos hf1
  have hhB := hB_pos hf
  have hiγ : (D.tile i).localAngle (mkPt x₀ 0) = γ := by
    have := (bSlot'_angles D hf hM hi).2; rwa [show x₀ - (f ^ 2 - 1) + (f ^ 2 - 1) = x₀ by ring] at this
  have hij : i ≠ j := by
    refine ne_of_vertex D.toDissection hi hm ?_
    rw [range_bSlotTile']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_snd hhB.ne⟩
  have hj : Set.range (D.tile j).pts = Set.range (aTileBG x₀ f hf1).pts := by
    rcases a_letter_tile D hf htgt hM hkm hk hm with h | h
    · exact h
    · exact absurd (aGB_angles D hf hM h).1 (fun hjγ => no_two_gamma D hf htgt hM hA hx0 hxL hij hiγ hjγ)
  refine ⟨hj, ?_⟩
  have hjβ := (aBG_angles D hf hM hj).1
  obtain ⟨l, hli, hlj, hl, huniq⟩ := third_of_gamma_beta D hf htgt hM hA hx0 hxL hiγ hjβ
  refine ⟨l, hli, hlj, hl, huniq, ?_⟩
  obtain ⟨k', hk', hopp, hsides⟩ := alpha_corner_data' D hf hM hA hl
  have hA' := hi; rw [left_bSlot' hf1] at hA'
  have hB' := hj; rw [right_BG hf1] at hB'
  have hr := third_tile_range D hf htgt (R₁ := f) (R₂ := f ^ 2) (ℓ₁ := f ^ 2) (ℓ₂ := f ^ 2 - 1)
    (ℓ₃ := f) hb hhB hf0 hh hf0 (by positivity) (by positivity) hb
    (sq_r_b_a hf) (sq_r_BG_left hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
  · rw [flush_at hf1, offset_at hf1]
    exact hr.symm.imp
      (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
        (mkPt_congr (by slot_arith) (by slot_arith))))
      (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
        (mkPt_congr (by slot_arith) (by slot_arith))))
  · -- `(1/2)·h − h_b·dBG = −(f·h/b)·(dBG − b/(2f)) < 0`
    have : 1 / 2 * apexH f - hB f * dBG f = -(apexH f * f ^ 2 / (f ^ 2 - 1)) := by
      simp only [hB]; unfold dBG; field_simp; ring
    rw [this]; have : 0 < apexH f * f ^ 2 / (f ^ 2 - 1) := by positivity
    linarith
  · -- `κ = f(2f² − 1)/2 > 0`
    have : 1 / 2 * dBG f + hB f * apexH f = f * (2 * f ^ 2 - 1) / 2 := by
      rw [hB_mul_h hf]; unfold dBG h2; field_simp; ring
    rw [this]; have : 0 < f * (2 * f ^ 2 - 1) / 2 := by apply div_pos (mul_pos hf0 (by nlinarith)) two_pos
    exact this.ne'
  · rw [hB_mul_h hf]; unfold dBG h2; field_simp; ring

/-- **THE `a|c` JUNCTION.**  `BG` on `[x₀ − f, x₀]` and a tile laying `c` on `[x₀, x₀ + c]`.
Both reflections survive the figure.  With `cSlotTile x₀` (`β` at `V`) the junction carries
exactly one further tile, presenting `α`: the flush or offset filler of the virtual junction.
With `cSlotTile' x₀` (`α` at `V`) it carries exactly one further tile, presenting `β`:
`bCapSet x₀ f` or `bOverSet x₀ f`. -/
theorem junction_a_c {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (aTileBG (x₀ - f) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + f ^ 2) 0) :
    (Set.range (D.tile j).pts = Set.range (cSlotTile x₀ f (by linarith)).pts ∧
      ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = α ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = α → l' = l) ∧
        (Set.range (D.tile l).pts = Set.range (flushFiller (x₀ - f) f (by linarith)).pts ∨
         Set.range (D.tile l).pts = Set.range (offsetFiller (x₀ - f) f (by linarith)).pts)) ∨
    (Set.range (D.tile j).pts = Set.range (cSlotTile' x₀ f (by linarith)).pts ∧
      ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = β ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = β → l' = l) ∧
        (Set.range (D.tile l).pts = bCapSet x₀ f ∨ Set.range (D.tile l).pts = bOverSet x₀ f)) := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb := hb_pos hf
  have hh := apexH_pos hf1
  have hhC := hC_pos hf
  have hc : (0:ℝ) < f ^ 2 := by positivity
  have hiγ : (D.tile i).localAngle (mkPt x₀ 0) = γ := by
    have := (aBG_angles D hf hM hi).2; rwa [show x₀ - f + f = x₀ by ring] at this
  have hij : i ≠ j := by
    refine ne_of_vertex D.toDissection hi hm ?_
    rw [range_aTileBG]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_snd hh.ne⟩
  have hA' := hi; rw [left_BG hf1] at hA'
  rcases c_letter_tile D hf htgt hM hkm hk hm with hj | hj
  · -- `cSlotTile`: `β` at `V`; the third tile is an `α`-tile in the `α`-wedge `(dBG−f, h)`, `(dBG/f, h_c)`
    left
    refine ⟨hj, ?_⟩
    have hjβ := (cSlot_angles D hf hM hj).1
    obtain ⟨l, hli, hlj, hl, huniq⟩ := third_of_gamma_beta D hf htgt hM hA hx0 hxL hiγ hjβ
    refine ⟨l, hli, hlj, hl, huniq, ?_⟩
    obtain ⟨k', hk', hopp, hsides⟩ := alpha_corner_data' D hf hM hA hl
    have hB' := hj; rw [right_cSlot hf1] at hB'
    have hr := third_tile_range D hf htgt (R₁ := f ^ 2 - 1) (R₂ := f) (ℓ₁ := f ^ 2) (ℓ₂ := f ^ 2 - 1)
      (ℓ₃ := f) hf0 hh hc hhC hb hf0 hc hb
      (sq_r_BG_right hf) (sq_r_c_a hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
    · rw [flush_at hf1, offset_at hf1]
      exact hr.symm.imp
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
    · -- `(dBG − f)·h_c − h·dBG/f = −h < 0`
      have : (dBG f - f) * hC f - apexH f * (dBG f / f) = -apexH f := by
        simp only [hC]; field_simp; ring
      rw [this]; linarith
    · have : (dBG f - f) * (dBG f / f) + apexH f * hC f = (2 * f ^ 4 - 3 * f ^ 2 + 1) / (2 * f) := by
        rw [h_mul_hC hf]; unfold dBG h2; field_simp; ring
      rw [this]
      have : 0 < 2 * f ^ 4 - 3 * f ^ 2 + 1 := by nlinarith [sq_nonneg (f ^ 2 - 1), sq_nonneg f]
      positivity
    · rw [h_mul_hC hf]; unfold dBG h2; field_simp; ring
  · -- `cSlotTile'`: `α` at `V`; the third tile is a `β`-tile in the `β`-wedge `(dBG−f, h)`, `(c − dBG/f, h_c)`
    right
    refine ⟨hj, ?_⟩
    have hjα := (cSlot'_angles D hf hM hj).1
    obtain ⟨l, hli, hlj, hl, huniq⟩ := third_of_gamma_alpha D hf htgt hM hA hx0 hxL hiγ hjα
    refine ⟨l, hli, hlj, hl, huniq, ?_⟩
    obtain ⟨k', hk', hopp, hsides⟩ := beta_corner_data D hf hM hA hl
    have hB' := hj; rw [right_cSlot' hf1] at hB'
    have hr := third_tile_range D hf htgt (R₁ := f ^ 2 - 1) (R₂ := f ^ 2 - 1) (ℓ₁ := f) (ℓ₂ := f ^ 2)
      (ℓ₃ := f ^ 2 - 1) hf0 hh hc hhC hb hb hf0 hc
      (sq_r_BG_right hf) (sq_r_c_b hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
    · exact hr.imp
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
    · -- `(dBG − f)·h_c − h·(c − dBG/f) = −h·b²/f² < 0`
      have : (dBG f - f) * hC f - apexH f * (f ^ 2 - dBG f / f)
          = -(apexH f * (f ^ 2 - 1) ^ 2 / f ^ 2) := by
        simp only [hC]; unfold dBG; field_simp; ring
      rw [this]
      have : 0 < apexH f * (f ^ 2 - 1) ^ 2 / f ^ 2 := by positivity
      linarith
    · have : (dBG f - f) * (f ^ 2 - dBG f / f) + apexH f * hC f
          = (f ^ 2 - 1) ^ 2 * (3 * f ^ 2 - 1) / (2 * f ^ 3) := by
        rw [h_mul_hC hf]; unfold dBG h2; field_simp; ring
      rw [this]
      have : 0 < 3 * f ^ 2 - 1 := by nlinarith
      positivity
    · rw [h_mul_hC hf]; unfold dBG h2; field_simp; ring

/-- **THE `c|a` JUNCTION, `c`-tile in the reflection `cSlotTile` (`α` at `V`).**  A tile laying
`a` on `[x₀, x₀ + f]` is `GB` or `BG` — **the figure kills neither**.  With `GB` (`γ` at `V`) the
junction carries exactly one further tile, presenting `β`: `bCapMSet x₀ f` or `bOverMSet x₀ f`
(the mirrored cap and overshoot).  With `BG` (`β` at `V`) the figure `{α, β, ·}` is completed
either by exactly one `γ`-tile — `cCapSet x₀ f` (the flat cap over the `c`-slot) or
`cSplitSet x₀ f` — or by the fan `{3α, 2β}`: two more `α`-tiles and one more `β`-tile at `V`. -/
theorem junction_c_a {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + f) 0) :
    (Set.range (D.tile j).pts = Set.range (aTileGB x₀ f (by linarith)).pts ∧
      ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = β ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = β → l' = l) ∧
        (Set.range (D.tile l).pts = bCapMSet x₀ f ∨ Set.range (D.tile l).pts = bOverMSet x₀ f)) ∨
    (Set.range (D.tile j).pts = Set.range (aTileBG x₀ f (by linarith)).pts ∧
      ((∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = γ ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = γ → l' = l) ∧
        (Set.range (D.tile l).pts = cCapSet x₀ f ∨ Set.range (D.tile l).pts = cSplitSet x₀ f)) ∨
       (({n | (D.tile n).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 3 ∧
        ({n | (D.tile n).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 2 ∧
        ({n | (D.tile n).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0))) := by
  classical
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb := hb_pos hf
  have hh := apexH_pos hf1
  have hhC := hC_pos hf
  have hc : (0:ℝ) < f ^ 2 := by positivity
  have hiα : (D.tile i).localAngle (mkPt x₀ 0) = α := by
    have := (cSlot_angles D hf hM hi).2; rwa [show x₀ - f ^ 2 + f ^ 2 = x₀ by ring] at this
  have hij : i ≠ j := by
    refine ne_of_vertex D.toDissection hi hm ?_
    rw [range_cSlotTile]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_snd hhC.ne⟩
  have hA' := hi; rw [left_cSlot hf1] at hA'
  rcases a_letter_tile D hf htgt hM hkm hk hm with hj | hj
  · -- `BG`: `α + β`
    right
    refine ⟨hj, ?_⟩
    have hjβ := (aBG_angles D hf hM hj).1
    rcases alpha_beta_cases D hf htgt hM hA hx0 hxL hiα hjβ with ⟨l, hli, hlj, hl, huniq⟩ | hfan
    · left
      refine ⟨l, hli, hlj, hl, huniq, ?_⟩
      obtain ⟨k', hk', hopp, hsides⟩ := gamma_corner_data D hf hM hA hl
      have hB' := hj; rw [right_BG hf1] at hB'
      have hr := third_tile_range D hf htgt (R₁ := f ^ 2 - 1) (R₂ := f ^ 2) (ℓ₁ := f) (ℓ₂ := f ^ 2 - 1)
        (ℓ₃ := f ^ 2) hc hhC hf0 hh hb hc hf0 hb
        (sq_r_c_b' hf) (sq_r_BG_left hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
      · exact hr.symm.imp
          (fun h => h.trans ((triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
            (mkPt_congr (by slot_arith) (by slot_arith))).trans triple_swap))
          (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
            (mkPt_congr (by slot_arith) (by slot_arith))))
      · -- `(dBG/f − c)·h − h_c·dBG = −c·h < 0`
        have : (dBG f / f - f ^ 2) * apexH f - hC f * dBG f = -(f ^ 2 * apexH f) := by
          simp only [hC]; field_simp; ring
        rw [this]; have : 0 < f ^ 2 * apexH f := by positivity
        linarith
      · -- `κ = −c·(dBG − f) < 0`: the `γ`-wedge is obtuse
        have : (dBG f / f - f ^ 2) * dBG f + hC f * apexH f = -(f ^ 2 * (dBG f - f)) := by
          rw [hC_mul_h hf]; unfold dBG h2; field_simp; ring
        rw [this]; have := p_pos hf
        have : 0 < f ^ 2 * (dBG f - f) := by positivity
        linarith
      · rw [hC_mul_h hf]; unfold dBG h2; field_simp; ring
    · exact Or.inr hfan
  · -- `GB`: `α + γ`
    left
    refine ⟨hj, ?_⟩
    have hjγ := (aGB_angles D hf hM hj).1
    obtain ⟨l, hlj, hli, hl, huniq⟩ := third_of_gamma_alpha D hf htgt hM hA hx0 hxL hjγ hiα
    refine ⟨l, hli, hlj, hl, huniq, ?_⟩
    obtain ⟨k', hk', hopp, hsides⟩ := beta_corner_data D hf hM hA hl
    have hB' := hj; rw [right_GB hf1] at hB'
    have hr := third_tile_range D hf htgt (R₁ := f ^ 2 - 1) (R₂ := f ^ 2 - 1) (ℓ₁ := f) (ℓ₂ := f ^ 2)
      (ℓ₃ := f ^ 2 - 1) hc hhC hf0 hh hb hb hf0 hc
      (sq_r_c_b' hf) (sq_r_GB_left hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
    · exact hr.symm.imp
        (fun h => h.trans ((triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))).trans triple_swap))
        (fun h => h.trans ((triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))).trans triple_swap))
    · -- `(dBG/f − c)·h − h_c·dGB = −h·b²/f² < 0`
      have : (dBG f / f - f ^ 2) * apexH f - hC f * dGB f = -(apexH f * (f ^ 2 - 1) ^ 2 / f ^ 2) := by
        simp only [hC]; unfold dGB dBG; field_simp; ring
      rw [this]; have : 0 < apexH f * (f ^ 2 - 1) ^ 2 / f ^ 2 := by positivity
      linarith
    · have : (dBG f / f - f ^ 2) * dGB f + hC f * apexH f
          = (f ^ 2 - 1) ^ 2 * (3 * f ^ 2 - 1) / (2 * f ^ 3) := by
        rw [hC_mul_h hf]; unfold dGB dBG h2; field_simp; ring
      rw [this]; have : 0 < 3 * f ^ 2 - 1 := by nlinarith
      positivity
    · rw [hC_mul_h hf]; unfold dGB dBG h2; field_simp; ring

/-- **THE `c|a` JUNCTION, `c`-tile in the reflection `cSlotTile'` (`β` at `V`).**  With `GB`
(`γ` at `V`) the junction carries exactly one further tile, presenting `α`: the mirrored flush or
offset filler (`flushMSet`, `offsetMSet`).  With `BG` (`β` at `V`) the figure is `{3α, 2β}`: three
`α`-tiles at `V` — the fan — and no `γ`-tile.  Neither orientation is killed by the figure. -/
theorem junction_c'_a {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile' (x₀ - f ^ 2) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + f) 0) :
    (Set.range (D.tile j).pts = Set.range (aTileGB x₀ f (by linarith)).pts ∧
      ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = α ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = α → l' = l) ∧
        (Set.range (D.tile l).pts = flushMSet x₀ f ∨ Set.range (D.tile l).pts = offsetMSet x₀ f)) ∨
    (Set.range (D.tile j).pts = Set.range (aTileBG x₀ f (by linarith)).pts ∧
      ({n | (D.tile n).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 3 ∧
      ({n | (D.tile n).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 2 ∧
      ({n | (D.tile n).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0) := by
  classical
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb := hb_pos hf
  have hh := apexH_pos hf1
  have hhC := hC_pos hf
  have hc : (0:ℝ) < f ^ 2 := by positivity
  have hiβ : (D.tile i).localAngle (mkPt x₀ 0) = β := by
    have := (cSlot'_angles D hf hM hi).2; rwa [show x₀ - f ^ 2 + f ^ 2 = x₀ by ring] at this
  have hij : i ≠ j := by
    refine ne_of_vertex D.toDissection hi hm ?_
    rw [range_cSlotTile']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_snd hhC.ne⟩
  have hA' := hi; rw [left_cSlot' hf1] at hA'
  rcases a_letter_tile D hf htgt hM hkm hk hm with hj | hj
  · -- `BG`: `β + β`, the fan
    right
    exact ⟨hj, beta_beta_fan D hf htgt hM hA hx0 hxL hij hiβ (aBG_angles D hf hM hj).1⟩
  · -- `GB`: `β + γ`
    left
    refine ⟨hj, ?_⟩
    have hjγ := (aGB_angles D hf hM hj).1
    obtain ⟨l, hlj, hli, hl, huniq⟩ := third_of_gamma_beta D hf htgt hM hA hx0 hxL hjγ hiβ
    refine ⟨l, hli, hlj, hl, huniq, ?_⟩
    obtain ⟨k', hk', hopp, hsides⟩ := alpha_corner_data' D hf hM hA hl
    have hB' := hj; rw [right_GB hf1] at hB'
    have hr := third_tile_range D hf htgt (R₁ := f) (R₂ := f ^ 2 - 1) (ℓ₁ := f ^ 2) (ℓ₂ := f ^ 2 - 1)
      (ℓ₃ := f) hc hhC hf0 hh hf0 hb hc hb
      (sq_r_c_a' hf) (sq_r_GB_left hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
    · exact hr.imp
        (fun h => h.trans ((triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))).trans triple_swap))
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
    · -- `(−dBG/f)·h − h_c·dGB = −h < 0`
      have : -(dBG f / f) * apexH f - hC f * dGB f = -apexH f := by
        simp only [hC]; unfold dGB dBG; field_simp; ring
      rw [this]; linarith
    · have : -(dBG f / f) * dGB f + hC f * apexH f = (2 * f ^ 4 - 3 * f ^ 2 + 1) / (2 * f) := by
        rw [hC_mul_h hf]; unfold dGB dBG h2; field_simp; ring
      rw [this]
      have : 0 < 2 * f ^ 4 - 3 * f ^ 2 + 1 := by nlinarith [sq_nonneg (f ^ 2 - 1), sq_nonneg f]
      positivity
    · rw [hC_mul_h hf]; unfold dGB dBG h2; field_simp; ring

/-! ### The pins `b|c` and `c|b` -/

/-- **THE `b|c` PIN** (`b`-tile in its forced reflection `bSlotTile'`, `γ` at `V`).  Both
reflections of the `c`-tile survive.  With `cSlotTile x₀` the junction carries exactly one `α`-tile:
the flush or offset filler of the virtual junction; with `cSlotTile' x₀` exactly one `β`-tile:
`bCapSet`/`bOverSet` — the same candidate lists as at `a|c`. -/
theorem junction_b'_c {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (bSlotTile' (x₀ - (f ^ 2 - 1)) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + f ^ 2) 0) :
    (Set.range (D.tile j).pts = Set.range (cSlotTile x₀ f (by linarith)).pts ∧
      ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = α ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = α → l' = l) ∧
        (Set.range (D.tile l).pts = Set.range (flushFiller (x₀ - f) f (by linarith)).pts ∨
         Set.range (D.tile l).pts = Set.range (offsetFiller (x₀ - f) f (by linarith)).pts)) ∨
    (Set.range (D.tile j).pts = Set.range (cSlotTile' x₀ f (by linarith)).pts ∧
      ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = β ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = β → l' = l) ∧
        (Set.range (D.tile l).pts = bCapSet x₀ f ∨ Set.range (D.tile l).pts = bOverSet x₀ f)) := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb := hb_pos hf
  have hh := apexH_pos hf1
  have hhB := hB_pos hf
  have hhC := hC_pos hf
  have hc : (0:ℝ) < f ^ 2 := by positivity
  have hiγ : (D.tile i).localAngle (mkPt x₀ 0) = γ := by
    have := (bSlot'_angles D hf hM hi).2; rwa [show x₀ - (f ^ 2 - 1) + (f ^ 2 - 1) = x₀ by ring] at this
  have hij : i ≠ j := by
    refine ne_of_vertex D.toDissection hi hm ?_
    rw [range_bSlotTile']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_snd hhB.ne⟩
  have hA' := hi; rw [left_bSlot' hf1] at hA'
  rcases c_letter_tile D hf htgt hM hkm hk hm with hj | hj
  · left
    refine ⟨hj, ?_⟩
    have hjβ := (cSlot_angles D hf hM hj).1
    obtain ⟨l, hli, hlj, hl, huniq⟩ := third_of_gamma_beta D hf htgt hM hA hx0 hxL hiγ hjβ
    refine ⟨l, hli, hlj, hl, huniq, ?_⟩
    obtain ⟨k', hk', hopp, hsides⟩ := alpha_corner_data' D hf hM hA hl
    have hB' := hj; rw [right_cSlot hf1] at hB'
    have hr := third_tile_range D hf htgt (R₁ := f) (R₂ := f) (ℓ₁ := f ^ 2) (ℓ₂ := f ^ 2 - 1)
      (ℓ₃ := f) hb hhB hc hhC hf0 hf0 hc hb
      (sq_r_b_a hf) (sq_r_c_a hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
    · rw [flush_at hf1, offset_at hf1]
      exact hr.symm.imp
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
    · have : 1 / 2 * hC f - hB f * (dBG f / f) = -(apexH f * f / (f ^ 2 - 1)) := by
        simp only [hB, hC]; unfold dBG; field_simp; ring
      rw [this]; have : 0 < apexH f * f / (f ^ 2 - 1) := by positivity
      linarith
    · have : 1 / 2 * (dBG f / f) + hB f * hC f = (2 * f ^ 2 - 1) / 2 := by
        rw [hB_mul_hC hf]; unfold dBG h2; field_simp; ring
      rw [this]; have : 0 < (2 * f ^ 2 - 1) / 2 := by apply div_pos (by nlinarith) two_pos
      exact this.ne'
    · rw [hB_mul_hC hf]; unfold dBG h2; field_simp; ring
  · right
    refine ⟨hj, ?_⟩
    have hjα := (cSlot'_angles D hf hM hj).1
    obtain ⟨l, hli, hlj, hl, huniq⟩ := third_of_gamma_alpha D hf htgt hM hA hx0 hxL hiγ hjα
    refine ⟨l, hli, hlj, hl, huniq, ?_⟩
    obtain ⟨k', hk', hopp, hsides⟩ := beta_corner_data D hf hM hA hl
    have hB' := hj; rw [right_cSlot' hf1] at hB'
    have hr := third_tile_range D hf htgt (R₁ := f) (R₂ := f ^ 2 - 1) (ℓ₁ := f) (ℓ₂ := f ^ 2)
      (ℓ₃ := f ^ 2 - 1) hb hhB hc hhC hf0 hb hf0 hc
      (sq_r_b_a hf) (sq_r_c_b hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
    · exact hr.imp
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
    · have : 1 / 2 * hC f - hB f * (f ^ 2 - dBG f / f) = -(apexH f * (f ^ 2 - 1) / f) := by
        simp only [hB, hC]; unfold dBG; field_simp; ring
      rw [this]; have : 0 < apexH f * (f ^ 2 - 1) / f := by positivity
      linarith
    · have : 1 / 2 * (f ^ 2 - dBG f / f) + hB f * hC f = (f ^ 2 - 1) * (3 * f ^ 2 - 1) / (2 * f ^ 2) := by
        rw [hB_mul_hC hf]; unfold dBG h2; field_simp; ring
      rw [this]; have : 0 < 3 * f ^ 2 - 1 := by nlinarith
      positivity
    · rw [hB_mul_hC hf]; unfold dBG h2; field_simp; ring

/-- **THE `c|b` PIN, `c`-tile `cSlotTile` (`α` at `V`).**  The `b`-tile is `bSlotTile x₀` (`γ` at
`V`; then exactly one `β`-tile, `bCapMSet`/`bOverMSet`) or `bSlotTile' x₀` (`α` at `V`; then the
figure is `{3α, 2β}`: one more `α`-tile and two `β`-tiles).  Neither reflection is killed. -/
theorem junction_c_b {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + (f ^ 2 - 1)) 0) :
    (Set.range (D.tile j).pts = Set.range (bSlotTile x₀ f (by linarith)).pts ∧
      ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = β ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = β → l' = l) ∧
        (Set.range (D.tile l).pts = bCapMSet x₀ f ∨ Set.range (D.tile l).pts = bOverMSet x₀ f)) ∨
    (Set.range (D.tile j).pts = Set.range (bSlotTile' x₀ f (by linarith)).pts ∧
      ({n | (D.tile n).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 3 ∧
      ({n | (D.tile n).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 2 ∧
      ({n | (D.tile n).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0) := by
  classical
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb := hb_pos hf
  have hh := apexH_pos hf1
  have hhB := hB_pos hf
  have hhC := hC_pos hf
  have hc : (0:ℝ) < f ^ 2 := by positivity
  have hiα : (D.tile i).localAngle (mkPt x₀ 0) = α := by
    have := (cSlot_angles D hf hM hi).2; rwa [show x₀ - f ^ 2 + f ^ 2 = x₀ by ring] at this
  have hij : i ≠ j := by
    refine ne_of_vertex D.toDissection hi hm ?_
    rw [range_cSlotTile]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_snd hhC.ne⟩
  have hA' := hi; rw [left_cSlot hf1] at hA'
  rcases b_letter_tile D hf htgt hM hkm hk hm with hj | hj
  · left
    refine ⟨hj, ?_⟩
    have hjγ := (bSlot_angles D hf hM hj).1
    obtain ⟨l, hlj, hli, hl, huniq⟩ := third_of_gamma_alpha D hf htgt hM hA hx0 hxL hjγ hiα
    refine ⟨l, hli, hlj, hl, huniq, ?_⟩
    obtain ⟨k', hk', hopp, hsides⟩ := beta_corner_data D hf hM hA hl
    have hB' := hj; rw [right_bSlot hf1] at hB'
    have hr := third_tile_range D hf htgt (R₁ := f ^ 2 - 1) (R₂ := f) (ℓ₁ := f) (ℓ₂ := f ^ 2)
      (ℓ₃ := f ^ 2 - 1) hc hhC hb hhB hb hf0 hf0 hc
      (sq_r_c_b' hf) (sq_r_b_a' hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
    · exact hr.symm.imp
        (fun h => h.trans ((triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))).trans triple_swap))
        (fun h => h.trans ((triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))).trans triple_swap))
    · have : (dBG f / f - f ^ 2) * hB f - hC f * (-1 / 2) = -(apexH f * (f ^ 2 - 1) / f) := by
        simp only [hB, hC]; unfold dBG; field_simp; ring
      rw [this]; have : 0 < apexH f * (f ^ 2 - 1) / f := by positivity
      linarith
    · have : (dBG f / f - f ^ 2) * (-1 / 2) + hC f * hB f
          = (f ^ 2 - 1) * (3 * f ^ 2 - 1) / (2 * f ^ 2) := by
        rw [hC_mul_hB hf]; unfold dBG h2; field_simp; ring
      rw [this]; have : 0 < 3 * f ^ 2 - 1 := by nlinarith
      positivity
    · rw [hC_mul_hB hf]; unfold dBG h2; field_simp; ring
  · right
    exact ⟨hj, alpha_alpha_fan D hf htgt hM hA hx0 hxL hij hiα (bSlot'_angles D hf hM hj).1⟩

/-- **THE `c|b` PIN, `c`-tile `cSlotTile'` (`β` at `V`).**  With `bSlotTile x₀` (`γ`) exactly one
`α`-tile: `flushMSet`/`offsetMSet`.  With `bSlotTile' x₀` (`α`) the figure `{α, β, ·}` is completed
by exactly one `γ`-tile — `cCapMSet`/`cSplitMSet` — or by the fan `{3α, 2β}`. -/
theorem junction_c'_b {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx0 : 0 < x₀) (hxL : x₀ < baseLen 1 f)
    {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile' (x₀ - f ^ 2) f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm : (D.tile j).pts m = mkPt (x₀ + (f ^ 2 - 1)) 0) :
    (Set.range (D.tile j).pts = Set.range (bSlotTile x₀ f (by linarith)).pts ∧
      ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = α ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = α → l' = l) ∧
        (Set.range (D.tile l).pts = flushMSet x₀ f ∨ Set.range (D.tile l).pts = offsetMSet x₀ f)) ∨
    (Set.range (D.tile j).pts = Set.range (bSlotTile' x₀ f (by linarith)).pts ∧
      ((∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = γ ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = γ → l' = l) ∧
        (Set.range (D.tile l).pts = cCapMSet x₀ f ∨ Set.range (D.tile l).pts = cSplitMSet x₀ f)) ∨
       (({n | (D.tile n).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 3 ∧
        ({n | (D.tile n).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 2 ∧
        ({n | (D.tile n).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0))) := by
  classical
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb := hb_pos hf
  have hh := apexH_pos hf1
  have hhB := hB_pos hf
  have hhC := hC_pos hf
  have hc : (0:ℝ) < f ^ 2 := by positivity
  have hiβ : (D.tile i).localAngle (mkPt x₀ 0) = β := by
    have := (cSlot'_angles D hf hM hi).2; rwa [show x₀ - f ^ 2 + f ^ 2 = x₀ by ring] at this
  have hij : i ≠ j := by
    refine ne_of_vertex D.toDissection hi hm ?_
    rw [range_cSlotTile']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_fst (by nlinarith), mkPt_ne_of_snd hhC.ne⟩
  have hA' := hi; rw [left_cSlot' hf1] at hA'
  rcases b_letter_tile D hf htgt hM hkm hk hm with hj | hj
  · left
    refine ⟨hj, ?_⟩
    have hjγ := (bSlot_angles D hf hM hj).1
    obtain ⟨l, hlj, hli, hl, huniq⟩ := third_of_gamma_beta D hf htgt hM hA hx0 hxL hjγ hiβ
    refine ⟨l, hli, hlj, hl, huniq, ?_⟩
    obtain ⟨k', hk', hopp, hsides⟩ := alpha_corner_data' D hf hM hA hl
    have hB' := hj; rw [right_bSlot hf1] at hB'
    have hr := third_tile_range D hf htgt (R₁ := f) (R₂ := f) (ℓ₁ := f ^ 2) (ℓ₂ := f ^ 2 - 1)
      (ℓ₃ := f) hc hhC hb hhB hf0 hf0 hc hb
      (sq_r_c_a' hf) (sq_r_b_a' hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
    · exact hr.imp
        (fun h => h.trans ((triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))).trans triple_swap))
        (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
          (mkPt_congr (by slot_arith) (by slot_arith))))
    · have : -(dBG f / f) * hB f - hC f * (-1 / 2) = -(apexH f * f / (f ^ 2 - 1)) := by
        simp only [hB, hC]; unfold dBG; field_simp; ring
      rw [this]; have : 0 < apexH f * f / (f ^ 2 - 1) := by positivity
      linarith
    · have : -(dBG f / f) * (-1 / 2) + hC f * hB f = (2 * f ^ 2 - 1) / 2 := by
        rw [hC_mul_hB hf]; unfold dBG h2; field_simp; ring
      rw [this]; have : 0 < (2 * f ^ 2 - 1) / 2 := by apply div_pos (by nlinarith) two_pos
      exact this.ne'
    · rw [hC_mul_hB hf]; unfold dBG h2; field_simp; ring
  · right
    refine ⟨hj, ?_⟩
    have hjα := (bSlot'_angles D hf hM hj).1
    rcases alpha_beta_cases D hf htgt hM hA hx0 hxL hjα hiβ with ⟨l, hlj, hli, hl, huniq⟩ | hfan
    · left
      refine ⟨l, hli, hlj, hl, huniq, ?_⟩
      obtain ⟨k', hk', hopp, hsides⟩ := gamma_corner_data D hf hM hA hl
      have hB' := hj; rw [right_bSlot' hf1] at hB'
      have hr := third_tile_range D hf htgt (R₁ := f) (R₂ := f ^ 2) (ℓ₁ := f) (ℓ₂ := f ^ 2 - 1)
        (ℓ₃ := f ^ 2) hc hhC hb hhB hf0 hc hf0 hb
        (sq_r_c_a' hf) (sq_r_b_c hf) ?_ ?_ ?_ hli hlj hA' hB' hk' hopp hsides
      · exact hr.imp
          (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
            (mkPt_congr (by slot_arith) (by slot_arith))))
          (fun h => h.trans (triple_congr rfl (mkPt_congr (by slot_arith) (by slot_arith))
            (mkPt_congr (by slot_arith) (by slot_arith))))
      · have e : -(dBG f / f) * hB f - hC f * (f ^ 2 - 1 + 1 / 2)
            = -(dBG f / f * hB f + hC f * (f ^ 2 - 1 + 1 / 2)) := by ring
        rw [e]
        have t1 : 0 < dBG f / f * hB f := by have := dBG_pos hf1; positivity
        have t2 : 0 < hC f * (f ^ 2 - 1 + 1 / 2) := by positivity
        linarith
      · have : -(dBG f / f) * (f ^ 2 - 1 + 1 / 2) + hC f * hB f = -(f ^ 2 / 2) := by
          rw [hC_mul_hB hf]; unfold dBG h2; field_simp; ring
        rw [this]; have : 0 < f ^ 2 / 2 := by positivity
        linarith
      · rw [hC_mul_hB hf]; unfold dBG h2; field_simp; ring
    · exact Or.inr hfan

/-! ## 9. The composite along a base word, up to the first `c|a` junction -/

/-- **The `BG` tile at the end of a laid `a`-run** `[t, t + n f]`, `t > 0`, `n ≥ 1`, whose first
letter is laid `BG`: the run is the march (`MarchUpTo t (n − 1)`) and its last tile is
`aTileBG (t + n f − f)`. -/
theorem run_last_tile {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 1 ≤ n)
    (hnL : t + n * f ≤ baseLen 1 f) (hrun : LaysARun D f t n)
    (hbase : ∃ i, Set.range (D.tile i).pts = Set.range (aTileBG t f (by linarith)).pts) :
    MarchUpTo D f (by linarith) t (n - 1) ∧
    ∃ i, Set.range (D.tile i).pts = Set.range (aTileBG (t + n * f - f) f (by linarith)).pts := by
  have hM' := run_rigid D hf htgt hM hA.hα hA.hαβ hA.hγdef hA.hrel hA.hirr ht hnL hrun hbase (n - 1)
    (by omega)
  refine ⟨hM', ?_⟩
  obtain ⟨i, hi⟩ := hM'.1 (n - 1) le_rfl
  refine ⟨i, ?_⟩
  rw [hi]; congr 3
  rw [Nat.cast_sub hn]; push_cast; ring

/-- **The first run, from the corner.**  A laid `a`-run `[0, p f]`, `p ≥ 1`, `p f ≤ L`: the corner
tile is `BG` (`first_letter_bg`), the last tile of the run is `aTileBG (p f − f)`, and for
`p ≥ 2` the corner junction carries the flush filler (`corner_junction_flush`) and the run from
`f` on is the march (`MarchUpTo f (p − 2)`). -/
theorem first_run {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {p : ℕ} (hp : 1 ≤ p) (hpL : p * f ≤ baseLen 1 f)
    (hrun : LaysARun D f 0 p) :
    (∃ i, Set.range (D.tile i).pts = Set.range (aTileBG 0 f (by linarith)).pts) ∧
    (∃ i, Set.range (D.tile i).pts = Set.range (aTileBG (p * f - f) f (by linarith)).pts) ∧
    (2 ≤ p → (∃ l, Set.range (D.tile l).pts = Set.range (flushFiller 0 f (by linarith)).pts) ∧
      MarchUpTo D f (by linarith) f (p - 2)) := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  obtain ⟨i0, k0, m0, hk0m0, hk0, hm0⟩ := hrun 0 (by omega)
  have hk0' : (D.tile i0).pts k0 = mkPt 0 0 := by rw [hk0]; congr 1; simp
  have hm0' : (D.tile i0).pts m0 = mkPt (0 + f) 0 := by rw [hm0]; congr 1; simp
  have hbase0 := first_letter_bg D hf htgt hM hk0m0 hk0' hm0'
  refine ⟨⟨i0, hbase0⟩, ?_⟩
  rcases Nat.lt_or_ge p 2 with hp2 | hp2
  · have hp1 : p = 1 := by omega
    subst hp1
    refine ⟨⟨i0, by rw [hbase0]; congr 3; simp⟩, fun h => absurd h (by omega)⟩
  · -- the second letter is laid `BG` (`a_letter_after_bg` at `x₀ = f`, no `0 < t` needed)
    obtain ⟨i1, k1, m1, hk1m1, hk1, hm1⟩ := hrun 1 (by omega)
    have hk1' : (D.tile i1).pts k1 = mkPt f 0 := by rw [hk1]; congr 1; simp
    have hm1' : (D.tile i1).pts m1 = mkPt (f + f) 0 := by rw [hm1]; congr 1; simp
    have h01 : i0 ≠ i1 := by
      refine ne_of_vertex D.toDissection hbase0 hm1' ?_
      rw [range_aTileBG]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      have := apexH_pos hf1
      exact ⟨mkPt_ne_of_fst (by linarith), mkPt_ne_of_fst (by linarith), mkPt_ne_of_snd this.ne⟩
    have hbase0' : Set.range (D.tile i0).pts = Set.range (aTileBG (f - f) f hf1).pts := by
      rw [hbase0]; congr 3; ring
    have hB1 := a_letter_after_bg D hf htgt hM h01 hbase0' hk1m1 hk1' hm1'
    have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp2
    have hrun' : LaysARun D f f (p - 1) := by
      intro j hj
      obtain ⟨i, k, m, hkm, hk, hm⟩ := hrun (j + 1) (by omega)
      exact ⟨i, k, m, hkm, by rw [hk]; congr 1; push_cast; ring, by rw [hm]; congr 1; push_cast; ring⟩
    have hnL : f + ((p - 1 : ℕ) : ℝ) * f ≤ baseLen 1 f := by
      rw [Nat.cast_sub hp]; push_cast; linarith
    obtain ⟨hMf, i2, hi2⟩ := run_last_tile D hf htgt hM hA hf0 (n := p - 1) (by omega) hnL hrun' ⟨i1, hB1⟩
    refine ⟨⟨i2, ?_⟩, fun _ => ⟨?_, by simpa using hMf⟩⟩
    · rw [hi2]; congr 3; rw [Nat.cast_sub hp]; push_cast; ring
    · obtain ⟨l, hl⟩ := corner_junction_flush D hf htgt hM hA.hα hA.hαβ hA.hγdef hA.hrel hA.hirr
        (by nlinarith) hbase0 hk1m1 (by rw [hk1']; congr 1; ring) (by rw [hm1']; congr 1; ring)
      exact ⟨l, hl⟩

/-- **THE COMPOSITE, `b` before `c`: the base word `a^p b a^q c …` up to the `c`-slot.**  For a
`CongruentDissection` of the `e = 1` target with the standard bundle, and the base word laid —
an `a`-run of length `p ≥ 1` from the corner, then `b`, then an `a`-run of length `q ≥ 1`, then
`c`, all fitting in the base:

1. the first run is the `BG` march from the corner (`first_run`);
2. the `b`-tile is `bSlotTile' (pf)` and the junction `(pf, 0)` carries a `β`-tile in
   `bCapSet`/`bOverSet` (`junction_a_b`);
3. the first `a` after `b` is `BG` and the junction `(pf + b, 0)` carries an `α`-tile which is
   the flush or offset filler (`junction_b'_a`);
4. the second run is the `BG` march (`MarchUpTo (pf + b) (q − 1)`);
5. at the `c`-slot's left junction `X = pf + b + qf` the `c`-tile is `cSlotTile X` with an
   `α`-tile (flush/offset) or `cSlotTile' X` with a `β`-tile (`bCapSet`/`bOverSet`)
   (`junction_a_c`).

**This is where the method stops deciding**: the orientation of the `a` after the `c`-slot is
not fixed by the figure (`junction_c_a`, `junction_c'_a`), so the run induction does not restart
and the far corner is not reached. -/
theorem word_b_first {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hrun1 : LaysARun D f 0 p)
    {jb : Fin N} {kb mb : Fin 3} (hkmb : kb ≠ mb)
    (hkb : (D.tile jb).pts kb = mkPt (p * f) 0)
    (hmb : (D.tile jb).pts mb = mkPt (p * f + (f ^ 2 - 1)) 0)
    (hrun2 : LaysARun D f (p * f + (f ^ 2 - 1)) q)
    {jc : Fin N} {kc mc : Fin 3} (hkmc : kc ≠ mc)
    (hkc : (D.tile jc).pts kc = mkPt (p * f + (f ^ 2 - 1) + q * f) 0)
    (hmc : (D.tile jc).pts mc = mkPt (p * f + (f ^ 2 - 1) + q * f + f ^ 2) 0)
    (hL : p * f + (f ^ 2 - 1) + q * f + f ^ 2 ≤ baseLen 1 f) :
    ((∃ i, Set.range (D.tile i).pts = Set.range (aTileBG 0 f (by linarith)).pts) ∧
     (2 ≤ p → (∃ l, Set.range (D.tile l).pts = Set.range (flushFiller 0 f (by linarith)).pts) ∧
       MarchUpTo D f (by linarith) f (p - 2))) ∧
    Set.range (D.tile jb).pts = Set.range (bSlotTile' (p * f) f (by linarith)).pts ∧
    (∃ l : Fin N, (D.tile l).localAngle (mkPt (p * f) 0) = β ∧
      (Set.range (D.tile l).pts = bCapSet (p * f) f ∨ Set.range (D.tile l).pts = bOverSet (p * f) f)) ∧
    (∃ i, Set.range (D.tile i).pts
      = Set.range (aTileBG (p * f + (f ^ 2 - 1)) f (by linarith)).pts) ∧
    (∃ l : Fin N, (D.tile l).localAngle (mkPt (p * f + (f ^ 2 - 1)) 0) = α ∧
      (Set.range (D.tile l).pts = Set.range (flushFiller (p * f + (f ^ 2 - 1) - f) f (by linarith)).pts ∨
       Set.range (D.tile l).pts = Set.range (offsetFiller (p * f + (f ^ 2 - 1) - f) f (by linarith)).pts)) ∧
    MarchUpTo D f (by linarith) (p * f + (f ^ 2 - 1)) (q - 1) ∧
    ((Set.range (D.tile jc).pts
        = Set.range (cSlotTile (p * f + (f ^ 2 - 1) + q * f) f (by linarith)).pts ∧
      ∃ l : Fin N, (D.tile l).localAngle (mkPt (p * f + (f ^ 2 - 1) + q * f) 0) = α ∧
        (Set.range (D.tile l).pts
            = Set.range (flushFiller (p * f + (f ^ 2 - 1) + q * f - f) f (by linarith)).pts ∨
         Set.range (D.tile l).pts
            = Set.range (offsetFiller (p * f + (f ^ 2 - 1) + q * f - f) f (by linarith)).pts)) ∨
     (Set.range (D.tile jc).pts
        = Set.range (cSlotTile' (p * f + (f ^ 2 - 1) + q * f) f (by linarith)).pts ∧
      ∃ l : Fin N, (D.tile l).localAngle (mkPt (p * f + (f ^ 2 - 1) + q * f) 0) = β ∧
        (Set.range (D.tile l).pts = bCapSet (p * f + (f ^ 2 - 1) + q * f) f ∨
         Set.range (D.tile l).pts = bOverSet (p * f + (f ^ 2 - 1) + q * f) f))) := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb := hb_pos hf
  have hc : (0:ℝ) < f ^ 2 := by positivity
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hpf : 0 < (p:ℝ) * f := by positivity
  have hqf : f ≤ (q:ℝ) * f := by nlinarith
  -- 1. the first run
  obtain ⟨hcorner, ⟨i1, hi1⟩, hrest⟩ := first_run D hf htgt hM hA hp (by nlinarith) hrun1
  refine ⟨⟨hcorner, hrest⟩, ?_⟩
  -- 2. the `a|b` junction at `pf`
  have hi1' : Set.range (D.tile i1).pts = Set.range (aTileBG (p * f - f) f hf1).pts := hi1
  obtain ⟨hjb, l1, -, -, hl1, -, hl1r⟩ := junction_a_b D hf htgt hM hA hpf (by nlinarith) hi1' hkmb hkb hmb
  refine ⟨hjb, ⟨l1, hl1, hl1r⟩, ?_⟩
  -- 3. the `b|a` junction at `pf + b`
  obtain ⟨j2, k2, m2, hk2m2, hk2, hm2⟩ := hrun2 0 (by omega)
  have hk2' : (D.tile j2).pts k2 = mkPt (p * f + (f ^ 2 - 1)) 0 := by rw [hk2]; congr 1; simp
  have hm2' : (D.tile j2).pts m2 = mkPt (p * f + (f ^ 2 - 1) + f) 0 := by rw [hm2]; congr 1; simp
  have hjb' : Set.range (D.tile jb).pts
      = Set.range (bSlotTile' (p * f + (f ^ 2 - 1) - (f ^ 2 - 1)) f hf1).pts := by
    rw [hjb]; congr 3; ring
  obtain ⟨hj2, l2, -, -, hl2, -, hl2r⟩ := junction_b'_a D hf htgt hM hA (by positivity) (by nlinarith)
    hjb' hk2m2 hk2' hm2'
  refine ⟨⟨j2, hj2⟩, ⟨l2, hl2, hl2r⟩, ?_⟩
  -- 4. the second run
  obtain ⟨hM2, i3, hi3⟩ := run_last_tile D hf htgt hM hA (by positivity) hq (by nlinarith) hrun2 ⟨j2, hj2⟩
  refine ⟨hM2, ?_⟩
  -- 5. the `a|c` junction at `X = pf + b + qf`
  have hi3' : Set.range (D.tile i3).pts
      = Set.range (aTileBG (p * f + (f ^ 2 - 1) + q * f - f) f hf1).pts := hi3
  rcases junction_a_c D hf htgt hM hA (by positivity) (by nlinarith) hi3' hkmc hkc hmc with
    ⟨hjc, l3, -, -, hl3, -, hl3r⟩ | ⟨hjc, l3, -, -, hl3, -, hl3r⟩
  · exact Or.inl ⟨hjc, l3, hl3, hl3r⟩
  · exact Or.inr ⟨hjc, l3, hl3, hl3r⟩

/-- **THE COMPOSITE, `c` before `b`: the base word `a^p c a …` up to and into the `c|a`
junction.**  The first run is the `BG` march; at the `c`-slot's left junction `X = pf` the
`c`-tile is `cSlotTile X` or `cSlotTile' X` with the corresponding third tile (`junction_a_c`);
and at its right junction `Y = pf + c` the next `a` is **`BG` or `GB` — undecided by the figure**,
with the four sub-cases of `junction_c_a`/`junction_c'_a`.  The run induction does not restart
here; this is the exact point where the method stops. -/
theorem word_c_first {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {p : ℕ} (hp : 1 ≤ p)
    (hrun1 : LaysARun D f 0 p)
    {jc : Fin N} {kc mc : Fin 3} (hkmc : kc ≠ mc)
    (hkc : (D.tile jc).pts kc = mkPt (p * f) 0)
    (hmc : (D.tile jc).pts mc = mkPt (p * f + f ^ 2) 0)
    {ja : Fin N} {ka ma : Fin 3} (hkma : ka ≠ ma)
    (hka : (D.tile ja).pts ka = mkPt (p * f + f ^ 2) 0)
    (hma : (D.tile ja).pts ma = mkPt (p * f + f ^ 2 + f) 0)
    (hL : p * f + f ^ 2 + f ≤ baseLen 1 f) :
    ((∃ i, Set.range (D.tile i).pts = Set.range (aTileBG 0 f (by linarith)).pts) ∧
     (2 ≤ p → (∃ l, Set.range (D.tile l).pts = Set.range (flushFiller 0 f (by linarith)).pts) ∧
       MarchUpTo D f (by linarith) f (p - 2))) ∧
    ((Set.range (D.tile jc).pts = Set.range (cSlotTile (p * f) f (by linarith)).pts ∧
      (∃ l : Fin N, (D.tile l).localAngle (mkPt (p * f) 0) = α ∧
        (Set.range (D.tile l).pts = Set.range (flushFiller (p * f - f) f (by linarith)).pts ∨
         Set.range (D.tile l).pts = Set.range (offsetFiller (p * f - f) f (by linarith)).pts)) ∧
      ((Set.range (D.tile ja).pts = Set.range (aTileGB (p * f + f ^ 2) f (by linarith)).pts ∧
        ∃ l : Fin N, (D.tile l).localAngle (mkPt (p * f + f ^ 2) 0) = β ∧
          (Set.range (D.tile l).pts = bCapMSet (p * f + f ^ 2) f ∨
           Set.range (D.tile l).pts = bOverMSet (p * f + f ^ 2) f)) ∨
       (Set.range (D.tile ja).pts = Set.range (aTileBG (p * f + f ^ 2) f (by linarith)).pts ∧
        ((∃ l : Fin N, (D.tile l).localAngle (mkPt (p * f + f ^ 2) 0) = γ ∧
          (Set.range (D.tile l).pts = cCapSet (p * f + f ^ 2) f ∨
           Set.range (D.tile l).pts = cSplitSet (p * f + f ^ 2) f)) ∨
         (({n | (D.tile n).localAngle (mkPt (p * f + f ^ 2) 0) = α} : Finset (Fin N)).card = 3 ∧
          ({n | (D.tile n).localAngle (mkPt (p * f + f ^ 2) 0) = β} : Finset (Fin N)).card = 2 ∧
          ({n | (D.tile n).localAngle (mkPt (p * f + f ^ 2) 0) = γ} : Finset (Fin N)).card = 0))))) ∨
     (Set.range (D.tile jc).pts = Set.range (cSlotTile' (p * f) f (by linarith)).pts ∧
      (∃ l : Fin N, (D.tile l).localAngle (mkPt (p * f) 0) = β ∧
        (Set.range (D.tile l).pts = bCapSet (p * f) f ∨ Set.range (D.tile l).pts = bOverSet (p * f) f)) ∧
      ((Set.range (D.tile ja).pts = Set.range (aTileGB (p * f + f ^ 2) f (by linarith)).pts ∧
        ∃ l : Fin N, (D.tile l).localAngle (mkPt (p * f + f ^ 2) 0) = α ∧
          (Set.range (D.tile l).pts = flushMSet (p * f + f ^ 2) f ∨
           Set.range (D.tile l).pts = offsetMSet (p * f + f ^ 2) f)) ∨
       (Set.range (D.tile ja).pts = Set.range (aTileBG (p * f + f ^ 2) f (by linarith)).pts ∧
        ({n | (D.tile n).localAngle (mkPt (p * f + f ^ 2) 0) = α} : Finset (Fin N)).card = 3 ∧
        ({n | (D.tile n).localAngle (mkPt (p * f + f ^ 2) 0) = β} : Finset (Fin N)).card = 2 ∧
        ({n | (D.tile n).localAngle (mkPt (p * f + f ^ 2) 0) = γ} : Finset (Fin N)).card = 0)))) := by
  classical
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hc : (0:ℝ) < f ^ 2 := by positivity
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hpf : 0 < (p:ℝ) * f := by positivity
  obtain ⟨hcorner, ⟨i1, hi1⟩, hrest⟩ := first_run D hf htgt hM hA hp (by nlinarith) hrun1
  refine ⟨⟨hcorner, hrest⟩, ?_⟩
  have hi1' : Set.range (D.tile i1).pts = Set.range (aTileBG (p * f - f) f hf1).pts := hi1
  have hka' : (D.tile ja).pts ka = mkPt (p * f + f ^ 2) 0 := hka
  rcases junction_a_c D hf htgt hM hA hpf (by nlinarith) hi1' hkmc hkc hmc with
    ⟨hjc, l3, -, -, hl3, -, hl3r⟩ | ⟨hjc, l3, -, -, hl3, -, hl3r⟩
  · left
    refine ⟨hjc, ⟨l3, hl3, hl3r⟩, ?_⟩
    have hjc' : Set.range (D.tile jc).pts
        = Set.range (cSlotTile (p * f + f ^ 2 - f ^ 2) f hf1).pts := by rw [hjc]; congr 3; ring
    rcases junction_c_a D hf htgt hM hA (by positivity) (by nlinarith) hjc' hkma hka' hma with
      ⟨hja, l4, -, -, hl4, -, hl4r⟩ | ⟨hja, (⟨l4, -, -, hl4, -, hl4r⟩ | hfan)⟩
    · exact Or.inl ⟨hja, l4, hl4, hl4r⟩
    · exact Or.inr ⟨hja, Or.inl ⟨l4, hl4, hl4r⟩⟩
    · exact Or.inr ⟨hja, Or.inr hfan⟩
  · right
    refine ⟨hjc, ⟨l3, hl3, hl3r⟩, ?_⟩
    have hjc' : Set.range (D.tile jc).pts
        = Set.range (cSlotTile' (p * f + f ^ 2 - f ^ 2) f hf1).pts := by rw [hjc]; congr 3; ring
    rcases junction_c'_a D hf htgt hM hA (by positivity) (by nlinarith) hjc' hkma hka' hma with
      ⟨hja, l4, -, -, hl4, -, hl4r⟩ | ⟨hja, hfan⟩
    · exact Or.inl ⟨hja, l4, hl4, hl4r⟩
    · exact Or.inr ⟨hja, hfan⟩

/-! ## 10. Non-vacuity: the configurations named exist inside the target -/

/-- **The overshoot placement at the corner slot leaves the target.**  `bOverSet f f`'s vertex
`(3f/2, (c/b)·h)` is the offset filler's overshoot vertex at the corner junction
(`offsetFiller 0 f`), which `MarchInduction.offset_at_corner_junction_outside` places outside. -/
theorem bOver_corner_outside {f : ℝ} (hf : 1 < f) :
    mkPt (f + f / 2) (f ^ 2 / (f ^ 2 - 1) * apexH f) ∉ (baseBetaTarget 1 f one_pos hf).carrier := by
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have e : mkPt (f + f / 2) (f ^ 2 / (f ^ 2 - 1) * apexH f) = (offsetFiller 0 f hf).pts 2 := by
    show _ = mkPt (0 + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f)
    exact mkPt_congr (by unfold dBG; field_simp; ring) rfl
  rw [e]; exact offset_at_corner_junction_outside hf

/-- **A small new kill: at the corner slot (`x₀ = f`, base word `a b …`) only the cap survives.**
The `β`-tile at `(f, 0)` is `bCapSet f f`; the overshoot placement has a vertex outside the
target. -/
theorem junction_a_b_corner {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) (hxL : f < baseLen 1 f)
    {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (aTileBG 0 f (by linarith)).pts)
    {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile j).pts k = mkPt f 0) (hm : (D.tile j).pts m = mkPt (f + (f ^ 2 - 1)) 0) :
    Set.range (D.tile j).pts = Set.range (bSlotTile' f f (by linarith)).pts ∧
    ∃ l : Fin N, (D.tile l).localAngle (mkPt f 0) = β ∧ Set.range (D.tile l).pts = bCapSet f f := by
  have hf1 : 1 < f := by linarith
  have hi' : Set.range (D.tile i).pts = Set.range (aTileBG (f - f) f hf1).pts := by
    rw [hi]; congr 3; ring
  obtain ⟨hj, l, -, -, hl, -, hr⟩ := junction_a_b D hf htgt hM hA (by linarith) hxL hi' hkm hk hm
  refine ⟨hj, l, hl, ?_⟩
  rcases hr with hr | hr
  · exact hr
  · exfalso
    have hmem : mkPt (f + f / 2) (f ^ 2 / (f ^ 2 - 1) * apexH f) ∈ Set.range (D.tile l).pts := by
      rw [hr]; unfold bOverSet; simp
    obtain ⟨n, hn⟩ := hmem
    have := pts_mem_target D.toDissection l n
    rw [hn, htgt] at this
    exact bOver_corner_outside hf1 this

/-- **The `a|b` configuration at `f = 4` (`N = 47`, prime), `x₀ = 8` (word `a a b …`), in
numbers.**  Tile `(4, 15, 16)`, `L = 47`, `dBG = 47/8`, `h_b = 4h/15`: `bSlotTile' 8` on `[8, 23]`
with apex `(47/2, 4h/15)`; the cap `{(8,0), (17/2, 4h/15), (47/2, 4h/15)}`, the overshoot
`{(8,0), (10, 16h/15), (95/8, h/15)}`; every vertex is inside the target. -/
theorem ab_config_f4 :
    bCapSet 8 4 = {mkPt 8 0, mkPt (17 / 2) (4 / 15 * apexH 4), mkPt (47 / 2) (4 / 15 * apexH 4)} ∧
    bOverSet 8 4 = {mkPt 8 0, mkPt 10 (16 / 15 * apexH 4), mkPt (95 / 8) (apexH 4 / 15)} ∧
    (bSlotTile' 8 4 (by norm_num)).pts 2 = mkPt (47 / 2) (4 / 15 * apexH 4) ∧
    mkPt (47 / 2) (4 / 15 * apexH 4) ∈ (baseBetaTarget 1 4 one_pos (by norm_num)).carrier ∧
    mkPt 10 (16 / 15 * apexH 4) ∈ (baseBetaTarget 1 4 one_pos (by norm_num)).carrier ∧
    mkPt (95 / 8) (apexH 4 / 15) ∈ (baseBetaTarget 1 4 one_pos (by norm_num)).carrier := by
  have hd : dBG 4 = 47 / 8 := by unfold dBG; norm_num
  have hL : baseLen 1 4 = 47 := by rw [baseLen_one]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold bCapSet; simp only [hB]; norm_num
  · unfold bOverSet; norm_num
  · show mkPt (8 + (4 ^ 2 - 1) + 1 / 2) (4 / (4 ^ 2 - 1) * apexH 4) = _; norm_num
  · have := mem_target_at_level (f := 4) (by norm_num) (a := 47 / 2) (μ := 4 / 15) (by norm_num)
      (by rw [hd]; norm_num) (by rw [hd, hL]; norm_num)
    simpa using this
  · have := mem_target_at_level (f := 4) (by norm_num) (a := 10) (μ := 16 / 15) (by norm_num)
      (by rw [hd]; norm_num) (by rw [hd, hL]; norm_num)
    simpa using this
  · have := mem_target_at_level (f := 4) (by norm_num) (a := 95 / 8) (μ := 1 / 15) (by norm_num)
      (by rw [hd]; norm_num) (by rw [hd, hL]; norm_num)
    simpa [div_eq_inv_mul] using this

/-- **The `c|a` configuration at `f = 4` (`N = 47`, prime), `x₀ = 20`, in numbers.**  Tile
`(4, 15, 16)`, `L = 47`, `dBG = 47/8`, `h_c = h/4`: `cSlotTile 4` on `[4, 20]` with apex
`(175/32, h/4)`; the flat cap `cCapSet 20 4 = {(20,0), (687/32, h/4), (175/32, h/4)}` — whose
third vertex **is** the `c`-tile's apex; the
`GB` candidate's apex `(20 + dGB, h) = (145/8, h)` is inside the target. -/
theorem ca_config_f4 :
    dBG 4 = 47 / 8 ∧ dGB 4 = -15 / 8 ∧ baseLen 1 4 = 47 ∧
    (cSlotTile 4 4 (by norm_num)).pts 2 = mkPt (175 / 32) (1 / 4 * apexH 4) ∧
    cCapSet 20 4 = {mkPt 20 0, mkPt (687 / 32) (1 / 4 * apexH 4), mkPt (175 / 32) (1 / 4 * apexH 4)} ∧
    mkPt (145 / 8) (apexH 4) ∈ (baseBetaTarget 1 4 one_pos (by norm_num)).carrier ∧
    mkPt (687 / 32) (1 / 4 * apexH 4) ∈ (baseBetaTarget 1 4 one_pos (by norm_num)).carrier := by
  have hd : dBG 4 = 47 / 8 := by unfold dBG; norm_num
  have hd' : dGB 4 = -15 / 8 := by unfold dGB; norm_num
  have hL : baseLen 1 4 = 47 := by rw [baseLen_one]; norm_num
  refine ⟨hd, hd', hL, ?_, ?_, ?_, ?_⟩
  · show mkPt (4 + dBG 4 / 4) (1 / 4 * apexH 4) = _; rw [hd]; norm_num
  · unfold cCapSet; simp only [hC]; rw [hd]; norm_num
  · have := mem_target_at_level (f := 4) (by norm_num) (a := 145 / 8) (μ := 1) (by norm_num)
      (by rw [hd]; norm_num) (by rw [hd, hL]; norm_num)
    simpa using this
  · have := mem_target_at_level (f := 4) (by norm_num) (a := 687 / 32) (μ := 1 / 4) (by norm_num)
      (by rw [hd]; norm_num) (by rw [hd, hL]; norm_num)
    simpa using this

/-- The hypotheses of `word_b_first` at `f = 4`, `p = 1`, `q = 2` (word `a b a a c a`, `N = 47`):
the positions `4`, `19`, `27`, `43` and the fit `43 ≤ 47`; the angle bundle is inhabited
(`angleData_f3`, and `MarchKillsFan.modelAlpha_irrational` at any natural `f ≥ 2`). -/
theorem word_b_first_hyps_f4 :
    (1 : ℝ) * 4 = 4 ∧ (1 : ℝ) * 4 + (4 ^ 2 - 1) = 19 ∧ (1 : ℝ) * 4 + (4 ^ 2 - 1) + 2 * 4 = 27 ∧
    (1 : ℝ) * 4 + (4 ^ 2 - 1) + 2 * 4 + 4 ^ 2 ≤ baseLen 1 4 ∧ ∃ α β γ, AngleData α β γ := by
  refine ⟨by norm_num, by norm_num, by norm_num, by rw [baseLen_one]; norm_num, angleData_f3⟩

/-! ## 11. Axiom audit -/

#print axioms b_letter_tile
#print axioms c_letter_tile
#print axioms no_two_gamma
#print axioms third_of_gamma_beta
#print axioms third_of_gamma_alpha
#print axioms beta_beta_fan
#print axioms alpha_alpha_fan
#print axioms alpha_beta_cases
#print axioms beta_corner_data
#print axioms gamma_corner_data
#print axioms edge_in_wedge_gen
#print axioms gram_extremal'
#print axioms wedge_extremal_gen
#print axioms third_tile_range
#print axioms junction_a_b
#print axioms junction_b'_a
#print axioms junction_a_c
#print axioms junction_c_a
#print axioms junction_c'_a
#print axioms junction_b'_c
#print axioms junction_c_b
#print axioms junction_c'_b
#print axioms first_run
#print axioms run_last_tile
#print axioms word_b_first
#print axioms word_c_first
#print axioms bOver_corner_outside
#print axioms junction_a_b_corner
#print axioms ab_config_f4
#print axioms ca_config_f4

end Erdos634.MarchSlots
