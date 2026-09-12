import Erdos634.TP_erdos
import Erdos634.ChordStraddleTotal
import Erdos634.MarchSlots

/-!
# The run-partition lemma: a straight boundary run clamped at both ends is exactly partitioned

Written 2026-09-12, sequential step 4 after `MarchSlots.lean`.  Step 3 located the `e = 1`
residue: the placements surviving the six junction theorems are killed by the engine through
*region-level* tests — the run `b − a` at the `c`-slot (K2), the stub `c − b = 1` (K1), the
pockets (P1a) — and the corpus had no dissection-level statement of the one geometric tool they
all use: **a straight run of the uncovered boundary between two convex corners is exactly
partitioned by whole tile edges**.  This file proves that tool and applies it.

## Ledger (what existed, checked 2026-09-12)

* `Dissection.wall_partition` (`WallChain.lean`): the near-side chain's *traces* on a wall
  segment partition it: `∑ μH¹(edge ∩ S) = μH¹ S`.  Traces, not whole edges.
* `TPErdos.chord_clamp` / `chain_edge_subset_chord` / `chain_edge_lengths_sum` (`TP_erdos.lean`,
  room `tileplace`): the "no overhang" upgrade — every chain edge is *contained in* the chord, so
  the chain's own edge lengths sum to the chord's length — **when the clamp is by two supporting
  half-planes of the target** (both chord endpoints on `∂ABC`, transversal).  This is
  `prop:cornerpara`'s argument at the target boundary.  It does **not** cover a run whose ends are
  clamped by *placed tiles*: no supporting functional of the target exists there.
* `Dissection.sameside_edges_subsingleton` (`EdgeChain.lean`): two same-side edges on a line meet
  in at most a point; `Dissection.edge_point_not_interior`, `carrier_point_not_interior`
  (`WallChain.lean`): an edge point is interior to no tile.
* `ChordStraddleTotal.straddlers`, `ChordDecompositionNoStraddle`: "no straddling *tile*" ⟹ the
  chain partitions the chord.  A different notion (tile crossing the line), not edge overhang.

So the clamped-chord lemma does **not** give the run partition when the clamp is by placed tiles.
The new content is exactly that: the two ways a placed configuration blocks the line beyond an
endpoint, and the dichotomy they force on every chain edge.

## What is proved

* `Straddles E P' P Q`: `E` meets both the open extension `(P', P)` and the open run `(P, Q)`.
* `edge_clamped`: a segment on the line that straddles neither endpoint is either contained in
  `[P, Q]` or meets it in at most a point.
* `not_straddles_of_interior` (**convex corner, type (a)**): if the open extension beyond `P`
  lies in the interior of some tile, no tile edge straddles `P`.
* `not_straddles_of_sameside_edge` (**convex corner, type (b)**): if a placed tile *on the run's
  side* has an edge on the line containing the extension `[P', P]`, no other chain edge straddles
  `P`.
* `not_straddles_of_outside` (**target boundary, type (c)**): if the extension is outside the
  target, no edge straddles — the `prop:cornerpara` case, now uniform with (a), (b).
* `run_partition`: **THE RUN-PARTITION LEMMA.**  For a wall segment `[P, Q]` (on a line, inside
  the target, meeting no tile interior) with no chain edge straddling `P` or `Q`, the near-side
  chain edges *contained in* `[P, Q]` have lengths summing to `dist P Q`.
* `run_partition_semigroup`: for a `CongruentDissection` with `ModelData` (sides `f, f²−1, f²`),
  `dist P Q = x·f + y·(f²−1) + z·f²` for naturals `x, y, z`.
* `run_b_sub_a_dies`, `run_one_dies`: a clamped run of length `b − a = f² − f − 1` (`f ≥ 3`) or
  of length `1` is impossible (`OrderForcing.east_cover_gap`, `FanKill.one_is_gap`).
* Non-vacuity: `run_partition_witness` on `TPErdos.wallDissection` — both ends clamped by (c),
  the chain nonempty, the sum `√2` realised by one whole edge.
* §B, the application at the `c|a` junction (`cslot_run_kill` and its instances): see below.

## What is NOT proved

* The pocket kill (P1a): "a bounded component of the uncovered region is a union of tiles, so
  its area is a multiple of the tile's".  Not built; the pocket placements survive here.
* The overlap kills (`bCapMSet` against the filler at `B`): a coordinate interior-intersection;
  not built here, so `bCapMSet` survives here.
* The mirror family (`cSlotTile'` + `bOverSet` at `B` + `flushMSet`/`offsetMSet` at `V`): the same
  argument reflected; not built.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.RunPartition

open Erdos634.Geometry Erdos634.CertCoord Set

/-! ## A. The lemma -/

/-- **`E` straddles `P`** (relative to the run `[P, Q]` and the extension `[P', P]`): `E` meets
both the open extension `(P', P)` and the open run `(P, Q)`. -/
def Straddles (E : Set Plane) (P' P Q : Plane) : Prop :=
  (E ∩ openSegment ℝ P' P).Nonempty ∧ (E ∩ openSegment ℝ P Q).Nonempty

/-! ### Parameters on the line -/

theorem lineMap_zero' (u v : Plane) : AffineMap.lineMap u v (0 : ℝ) = u := by simp
theorem lineMap_one' (u v : Plane) : AffineMap.lineMap u v (1 : ℝ) = v := by simp

/-- Membership in a segment of the line, in parameters. -/
theorem mem_segment_lineMap_iff {u v : Plane} (huv : u ≠ v) (a b t : ℝ) :
    AffineMap.lineMap u v t ∈ segment ℝ (AffineMap.lineMap u v a) (AffineMap.lineMap u v b)
      ↔ t ∈ segment ℝ a b := by
  rw [← image_segment ℝ (AffineMap.lineMap u v : ℝ →ᵃ[ℝ] Plane)]
  constructor
  · rintro ⟨s, hs, hst⟩
    rwa [← Erdos634.LineParam.lineMap_injective_of_ne huv hst]
  · intro ht; exact ⟨t, ht, rfl⟩

/-- Membership in an open segment of the line, in parameters. -/
theorem mem_openSegment_lineMap_iff {u v : Plane} (huv : u ≠ v) (a b t : ℝ) :
    AffineMap.lineMap u v t ∈ openSegment ℝ (AffineMap.lineMap u v a) (AffineMap.lineMap u v b)
      ↔ t ∈ openSegment ℝ a b := by
  rw [← image_openSegment ℝ (AffineMap.lineMap u v : ℝ →ᵃ[ℝ] Plane)]
  constructor
  · rintro ⟨s, hs, hst⟩
    rwa [← Erdos634.LineParam.lineMap_injective_of_ne huv hst]
  · intro ht; exact ⟨t, ht, rfl⟩

/-- Every point of `segment (lineMap u v a) (lineMap u v b)` is a `lineMap` point. -/
theorem exists_param_of_mem_segment (u v : Plane) {a b : ℝ} {x : Plane}
    (hx : x ∈ segment ℝ (AffineMap.lineMap u v a) (AffineMap.lineMap u v b)) :
    ∃ t ∈ segment ℝ a b, x = AffineMap.lineMap u v t := by
  rw [← image_segment ℝ (AffineMap.lineMap u v : ℝ →ᵃ[ℝ] Plane)] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t, ht, rfl⟩

theorem exists_param_of_mem_openSegment (u v : Plane) {a b : ℝ} {x : Plane}
    (hx : x ∈ openSegment ℝ (AffineMap.lineMap u v a) (AffineMap.lineMap u v b)) :
    ∃ t ∈ openSegment ℝ a b, x = AffineMap.lineMap u v t := by
  rw [← image_openSegment ℝ (AffineMap.lineMap u v : ℝ →ᵃ[ℝ] Plane)] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨t, ht, rfl⟩

/-- `0 ∈ openSegment t' 1` forces `t' < 0`. -/
theorem neg_of_zero_mem_openSegment {t' : ℝ} (h : (0:ℝ) ∈ openSegment ℝ t' 1) : t' < 0 := by
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := h
  simp only [smul_eq_mul, mul_one] at hcomb
  by_contra hc
  push_neg at hc
  nlinarith [mul_nonneg ha.le hc]

/-- `1 ∈ openSegment 0 s'` forces `1 < s'`. -/
theorem one_lt_of_one_mem_openSegment {s' : ℝ} (h : (1:ℝ) ∈ openSegment ℝ 0 s') : 1 < s' := by
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := h
  simp only [smul_eq_mul, mul_zero, zero_add] at hcomb
  by_contra hc
  push_neg at hc
  nlinarith [mul_le_mul_of_nonneg_left hc hb.le]

/-- A real in `openSegment a b` with `a < b` is in `Ioo a b`; general membership unpacked. -/
theorem mem_openSegment_real {a b t : ℝ} (hab : a ≠ b) (h : t ∈ openSegment ℝ a b) :
    min a b < t ∧ t < max a b := by
  rw [openSegment_eq_Ioo' hab] at h
  exact ⟨h.1, h.2⟩

theorem mem_segment_real {a b t : ℝ} (h : t ∈ segment ℝ a b) :
    min a b ≤ t ∧ t ≤ max a b := by
  rw [segment_eq_uIcc] at h
  exact ⟨h.1, h.2⟩

theorem mem_segment_real_of {a b t : ℝ} (h1 : min a b ≤ t) (h2 : t ≤ max a b) :
    t ∈ segment ℝ a b := by
  rw [segment_eq_uIcc]; exact ⟨h1, h2⟩

theorem mem_openSegment_real_of {a b t : ℝ} (h1 : min a b < t) (h2 : t < max a b) :
    t ∈ openSegment ℝ a b := by
  have hab : a ≠ b := by
    rintro rfl
    simp only [min_self, max_self] at h1 h2; linarith
  rw [openSegment_eq_Ioo' hab]; exact ⟨h1, h2⟩

/-- The extension point `P'` with `P ∈ (P', Q)` has a negative parameter on the line `P Q`. -/
theorem param_of_left (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q P' : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c) (hfQ : f Q = c) (hfP' : f P' = c) (hP' : P ∈ openSegment ℝ P' Q) :
    ∃ t' : ℝ, t' < 0 ∧ P' = AffineMap.lineMap P Q t' := by
  obtain ⟨t', rfl⟩ := Erdos634.TPErdos.line_eq_lineMap f hf c hfP hfQ hPQ hfP'
  refine ⟨t', ?_, rfl⟩
  have h0 : AffineMap.lineMap P Q (0:ℝ) ∈ openSegment ℝ (AffineMap.lineMap P Q t')
      (AffineMap.lineMap P Q (1:ℝ)) := by
    rw [lineMap_zero', lineMap_one']; exact hP'
  rw [mem_openSegment_lineMap_iff hPQ] at h0
  exact neg_of_zero_mem_openSegment h0

/-- The extension point `Q'` with `Q ∈ (P, Q')` has parameter `> 1` on the line `P Q`. -/
theorem param_of_right (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q Q' : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c) (hfQ : f Q = c) (hfQ' : f Q' = c) (hQ' : Q ∈ openSegment ℝ P Q') :
    ∃ s' : ℝ, 1 < s' ∧ Q' = AffineMap.lineMap P Q s' := by
  obtain ⟨s', rfl⟩ := Erdos634.TPErdos.line_eq_lineMap f hf c hfP hfQ hPQ hfQ'
  refine ⟨s', ?_, rfl⟩
  have h1 : AffineMap.lineMap P Q (1:ℝ) ∈ openSegment ℝ (AffineMap.lineMap P Q (0:ℝ))
      (AffineMap.lineMap P Q s') := by
    rw [lineMap_zero', lineMap_one']; exact hQ'
  rw [mem_openSegment_lineMap_iff hPQ] at h1
  exact one_lt_of_one_mem_openSegment h1

/-! ### The dichotomy -/

/-- **A segment on the line that straddles neither end of the run is clamped**: it is contained
in `[P, Q]`, or it meets `[P, Q]` in at most one point. -/
theorem edge_clamped (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q P' Q' : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c) (hfQ : f Q = c) (hfP' : f P' = c) (hfQ' : f Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    {p₁ p₂ : Plane} (h₁ : f p₁ = c) (h₂ : f p₂ = c)
    (hnoP : ¬ Straddles (segment ℝ p₁ p₂) P' P Q)
    (hnoQ : ¬ Straddles (segment ℝ p₁ p₂) Q' Q P) :
    (segment ℝ p₁ p₂ ∩ segment ℝ P Q).Subsingleton ∨ segment ℝ p₁ p₂ ⊆ segment ℝ P Q := by
  obtain ⟨t', ht', rfl⟩ := param_of_left f hf c hPQ hfP hfQ hfP' hP'
  obtain ⟨s', hs', rfl⟩ := param_of_right f hf c hPQ hfP hfQ hfQ' hQ'
  obtain ⟨t₁, rfl⟩ := Erdos634.TPErdos.line_eq_lineMap f hf c hfP hfQ hPQ h₁
  obtain ⟨t₂, rfl⟩ := Erdos634.TPErdos.line_eq_lineMap f hf c hfP hfQ hPQ h₂
  have hP0 : P = AffineMap.lineMap P Q (0:ℝ) := (lineMap_zero' P Q).symm
  have hQ1 : Q = AffineMap.lineMap P Q (1:ℝ) := (lineMap_one' P Q).symm
  -- a point of the parameter interval straddling below
  have hmemI : ∀ t ∈ segment ℝ t₁ t₂, AffineMap.lineMap P Q t ∈ segment ℝ (AffineMap.lineMap P Q t₁) (AffineMap.lineMap P Q t₂) := fun t ht =>
    (mem_segment_lineMap_iff hPQ t₁ t₂ t).mpr ht
  by_cases hmeet : ∃ u ∈ segment ℝ t₁ t₂, 0 < u ∧ u < 1
  · right
    obtain ⟨u, hu, hu0, hu1⟩ := hmeet
    have hlo : ∀ t ∈ segment ℝ t₁ t₂, 0 ≤ t := by
      intro t ht
      by_contra hneg
      push_neg at hneg
      apply hnoP
      set w := max t t' / 2 with hw
      have hwt : t < w := by
        have := le_max_left t t'; rw [hw]; linarith
      have hwt' : t' < w := by
        have := le_max_right t t'; rw [hw]; linarith
      have hw0 : w < 0 := by
        rw [hw]; have := max_lt hneg ht'; linarith
      have hwI : w ∈ segment ℝ t₁ t₂ := by
        obtain ⟨h1, h2⟩ := mem_segment_real ht
        obtain ⟨h3, h4⟩ := mem_segment_real hu
        exact mem_segment_real_of (by linarith) (by linarith)
      refine ⟨⟨AffineMap.lineMap P Q w, hmemI w hwI, ?_⟩, ⟨AffineMap.lineMap P Q u, hmemI u hu, ?_⟩⟩
      · have := (mem_openSegment_lineMap_iff hPQ t' (0:ℝ) w).mpr
          (mem_openSegment_real_of (by rw [min_eq_left ht'.le]; exact hwt')
            (by rw [max_eq_right ht'.le]; exact hw0))
        rwa [lineMap_zero'] at this
      · have := (mem_openSegment_lineMap_iff hPQ (0:ℝ) (1:ℝ) u).mpr
          (mem_openSegment_real_of (by rw [min_eq_left zero_le_one]; exact hu0)
            (by rw [max_eq_right zero_le_one]; exact hu1))
        rwa [lineMap_zero', lineMap_one'] at this
    have hhi : ∀ t ∈ segment ℝ t₁ t₂, t ≤ 1 := by
      intro t ht
      by_contra hgt
      push_neg at hgt
      apply hnoQ
      set w := (min t s' + 1) / 2 with hw
      have hwt : w < t := by
        have := min_le_left t s'; rw [hw]; linarith
      have hws' : w < s' := by
        have := min_le_right t s'; rw [hw]; linarith
      have hw1 : 1 < w := by
        rw [hw]; have := lt_min hgt hs'; linarith
      have hwI : w ∈ segment ℝ t₁ t₂ := by
        obtain ⟨h1, h2⟩ := mem_segment_real ht
        obtain ⟨h3, h4⟩ := mem_segment_real hu
        exact mem_segment_real_of (by linarith) (by linarith)
      refine ⟨⟨AffineMap.lineMap P Q w, hmemI w hwI, ?_⟩, ⟨AffineMap.lineMap P Q u, hmemI u hu, ?_⟩⟩
      · have := (mem_openSegment_lineMap_iff hPQ s' (1:ℝ) w).mpr
          (mem_openSegment_real_of (by rw [min_eq_right hs'.le]; exact hw1)
            (by rw [max_eq_left hs'.le]; exact hws'))
        rwa [lineMap_one'] at this
      · have := (mem_openSegment_lineMap_iff hPQ (1:ℝ) (0:ℝ) u).mpr
          (mem_openSegment_real_of (by rw [min_eq_right zero_le_one]; exact hu0)
            (by rw [max_eq_left zero_le_one]; exact hu1))
        rwa [lineMap_zero', lineMap_one'] at this
    intro x hx
    obtain ⟨t, ht, rfl⟩ := exists_param_of_mem_segment P Q hx
    have := (mem_segment_lineMap_iff hPQ (0:ℝ) (1:ℝ) t).mpr
      (mem_segment_real_of (by rw [min_eq_left zero_le_one]; exact hlo t ht)
        (by rw [max_eq_right zero_le_one]; exact hhi t ht))
    rwa [lineMap_zero', lineMap_one'] at this
  · left
    push_neg at hmeet
    intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := exists_param_of_mem_segment P Q hx.1
    obtain ⟨r, hr, rfl⟩ := exists_param_of_mem_segment P Q hy.1
    have hs01 : 0 ≤ s ∧ s ≤ 1 := by
      have := (mem_segment_lineMap_iff hPQ (0:ℝ) (1:ℝ) s).mp
        (by rw [lineMap_zero', lineMap_one']; exact hx.2)
      obtain ⟨h1, h2⟩ := mem_segment_real this
      rw [min_eq_left zero_le_one] at h1; rw [max_eq_right zero_le_one] at h2
      exact ⟨h1, h2⟩
    have hr01 : 0 ≤ r ∧ r ≤ 1 := by
      have := (mem_segment_lineMap_iff hPQ (0:ℝ) (1:ℝ) r).mp
        (by rw [lineMap_zero', lineMap_one']; exact hy.2)
      obtain ⟨h1, h2⟩ := mem_segment_real this
      rw [min_eq_left zero_le_one] at h1; rw [max_eq_right zero_le_one] at h2
      exact ⟨h1, h2⟩
    by_contra hne
    have hsr : s ≠ r := fun h => hne (by rw [h])
    have hmid : (s + r) / 2 ∈ segment ℝ t₁ t₂ := by
      obtain ⟨h1, h2⟩ := mem_segment_real hs
      obtain ⟨h3, h4⟩ := mem_segment_real hr
      exact mem_segment_real_of (by linarith) (by linarith)
    have h0 : 0 < (s + r) / 2 := by
      rcases lt_or_gt_of_ne hsr with h | h <;> linarith [hs01.1, hr01.1]
    have h1 : (s + r) / 2 < 1 := by
      rcases lt_or_gt_of_ne hsr with h | h <;> linarith [hs01.2, hr01.2]
    exact absurd h1 (not_lt.mpr (hmeet _ hmid h0))

/-! ### The three ways an end is clamped -/

/-- **(a) Convex corner by a tile interior.**  If the open extension `(P', P)` lies in the
interior of some tile, no tile edge straddles `P`. -/
theorem not_straddles_of_interior {N : ℕ} (D : Dissection N) {P' P Q : Plane} {j : Fin N}
    (hj : openSegment ℝ P' P ⊆ interior (D.tile j).carrier) (i : Fin N) (k : Fin 3) :
    ¬ Straddles ((D.tile i).edge k) P' P Q := by
  rintro ⟨⟨y, hyE, hyP⟩, -⟩
  exact D.edge_point_not_interior hyE j (hj hyP)

/-- **(c) Target boundary.**  If the open extension `(P', P)` is outside the target, no tile edge
straddles `P`. -/
theorem not_straddles_of_outside {N : ℕ} (D : Dissection N) {P' P Q : Plane}
    (hout : ∀ y ∈ openSegment ℝ P' P, y ∉ D.target.carrier) (i : Fin N) (k : Fin 3) :
    ¬ Straddles ((D.tile i).edge k) P' P Q := by
  rintro ⟨⟨y, hyE, hyP⟩, -⟩
  exact hout y hyP (Erdos634.BaseSelection.tile_subset_target D i
    ((D.tile i).edge_subset_carrier k hyE))

/-- **(b) Convex corner by a same-side placed edge.**  If a placed tile `j₁` on the run's side
(`f ≤ c`) has an edge on the line containing the whole extension `[P', P]`, then no *other*
near-side chain edge straddles `P`: it would share a nondegenerate piece with `j₁`'s edge, against
`sameside_edges_subsingleton`. -/
theorem not_straddles_of_sameside_edge {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ)
    (hf : f ≠ 0) (c : ℝ) {P Q P' : Plane} (hPQ : P ≠ Q)
    (hfP : f P = c) (hfQ : f Q = c) (hfP' : f P' = c) (hP' : P ∈ openSegment ℝ P' Q)
    {j₁ : Fin N} {k₁ : Fin 3} (hle₁ : ∀ y ∈ (D.tile j₁).carrier, f y ≤ c)
    (hE₁ : ∀ y ∈ (D.tile j₁).edge k₁, f y = c) (hcont : segment ℝ P' P ⊆ (D.tile j₁).edge k₁)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) (hne : e ≠ (j₁, k₁)) :
    ¬ Straddles ((D.tile e.1).edge e.2) P' P Q := by
  rintro ⟨⟨y, hyE, hyP⟩, ⟨z, hzE, hzQ⟩⟩
  obtain ⟨t', ht', rfl⟩ := param_of_left f hf c hPQ hfP hfQ hfP' hP'
  have hP0 : P = AffineMap.lineMap P Q (0:ℝ) := (lineMap_zero' P Q).symm
  have hQ1 : Q = AffineMap.lineMap P Q (1:ℝ) := (lineMap_one' P Q).symm
  -- parameters of `y` and `z`
  have hy' : y ∈ openSegment ℝ (AffineMap.lineMap P Q t') (AffineMap.lineMap P Q (0:ℝ)) := by rw [← hP0]; exact hyP
  have hz' : z ∈ openSegment ℝ (AffineMap.lineMap P Q (0:ℝ)) (AffineMap.lineMap P Q (1:ℝ)) := by rw [← hP0, ← hQ1]; exact hzQ
  obtain ⟨u, hu, rfl⟩ := exists_param_of_mem_openSegment P Q hy'
  obtain ⟨v, hv, rfl⟩ := exists_param_of_mem_openSegment P Q hz'
  obtain ⟨hu1, hu2⟩ := mem_openSegment_real ht'.ne hu
  obtain ⟨hv1, hv2⟩ := mem_openSegment_real zero_ne_one hv
  rw [min_eq_left ht'.le] at hu1; rw [max_eq_right ht'.le] at hu2
  rw [min_eq_left zero_le_one] at hv1; rw [max_eq_right zero_le_one] at hv2
  -- `P` lies between `y` and `z`, hence on `e`'s edge
  have hPyz : P ∈ segment ℝ (AffineMap.lineMap P Q u) (AffineMap.lineMap P Q v) := by
    have := (mem_segment_lineMap_iff hPQ u v (0:ℝ)).mpr
      (mem_segment_real_of (by rw [min_eq_left (by linarith)]; linarith)
        (by rw [max_eq_right (by linarith)]; linarith))
    rwa [lineMap_zero'] at this
  have hPE : P ∈ (D.tile e.1).edge e.2 :=
    (convex_segment _ _).segment_subset hyE hzE hPyz
  -- `y` and `P` both lie on `j₁`'s edge too
  have hyE₁ : AffineMap.lineMap P Q u ∈ (D.tile j₁).edge k₁ := hcont (openSegment_subset_segment ℝ _ _ hyP)
  have hPE₁ : P ∈ (D.tile j₁).edge k₁ := hcont (right_mem_segment ℝ _ _)
  obtain ⟨hp, hq, hle⟩ := Dissection.mem_lineChain.mp he
  have hss := D.sameside_edges_subsingleton f c hf hne
    ((D.tile e.1).carrier_subset_halfplane f c hle) hle₁ (D.lineChain_edge_subset he) hE₁
  have heq : AffineMap.lineMap P Q u = P := hss ⟨hyE, hyE₁⟩ ⟨hPE, hPE₁⟩
  have heq' : AffineMap.lineMap P Q u = AffineMap.lineMap P Q (0:ℝ) := by
    rw [lineMap_zero']; exact heq
  have := Erdos634.LineParam.lineMap_injective_of_ne hPQ heq'
  linarith

/-- A segment ending at `P` from the extension side does not straddle `P` (used for the placed
tile's own edge). -/
theorem not_straddles_extension (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P Q P' : Plane}
    (hPQ : P ≠ Q) (hfP : f P = c) (hfQ : f Q = c) (hfP' : f P' = c)
    (hP' : P ∈ openSegment ℝ P' Q) {E : Set Plane} (hE : E ⊆ segment ℝ P' P) :
    ¬ Straddles E P' P Q := by
  rintro ⟨-, ⟨z, hzE, hzQ⟩⟩
  obtain ⟨t', ht', rfl⟩ := param_of_left f hf c hPQ hfP hfQ hfP' hP'
  have hP0 : P = AffineMap.lineMap P Q (0:ℝ) := (lineMap_zero' P Q).symm
  have hQ1 : Q = AffineMap.lineMap P Q (1:ℝ) := (lineMap_one' P Q).symm
  have hz' : z ∈ openSegment ℝ (AffineMap.lineMap P Q (0:ℝ)) (AffineMap.lineMap P Q (1:ℝ)) := by rw [← hP0, ← hQ1]; exact hzQ
  obtain ⟨v, hv, rfl⟩ := exists_param_of_mem_openSegment P Q hz'
  obtain ⟨hv1, hv2⟩ := mem_openSegment_real zero_ne_one hv
  rw [min_eq_left zero_le_one] at hv1
  have hzP : AffineMap.lineMap P Q v ∈ segment ℝ (AffineMap.lineMap P Q t') (AffineMap.lineMap P Q (0:ℝ)) := by rw [← hP0]; exact hE hzE
  rw [mem_segment_lineMap_iff hPQ] at hzP
  obtain ⟨-, h2⟩ := mem_segment_real hzP
  rw [max_eq_right ht'.le] at h2
  linarith

/-! ### The run partition -/

open Classical in
/-- **THE RUN-PARTITION LEMMA.**  Let `[P, Q]` be a wall segment on the line `{f = c}` — inside
the target, meeting no tile's interior — and let no near-side chain edge straddle `P` (relative to
an extension point `P'` beyond `P`) or `Q` (relative to `Q'` beyond `Q`).  Then the near-side
chain edges **contained in** `[P, Q]` have lengths summing exactly to `dist P Q`: the run is
partitioned by whole tile edges. -/
theorem run_partition {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hfP' : f P' = c) (hfQ' : f Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hS : segment ℝ P Q ⊆ {y | f y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ e ∈ D.lineChain f c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q)
    (hQ : ∀ e ∈ D.lineChain f c, ¬ Straddles ((D.tile e.1).edge e.2) Q' Q P) :
    ∑ e ∈ (D.lineChain f c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P Q),
        dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist P Q := by
  have hfP : f P = c := hS (left_mem_segment ℝ P Q)
  have hfQ : f Q = c := hS (right_mem_segment ℝ P Q)
  have hpart := D.wall_partition f c hf hPQ hS hint hwall
  set μ := (MeasureTheory.Measure.hausdorffMeasure 1 : MeasureTheory.Measure Plane) with hμ
  have hstep : ∀ e ∈ D.lineChain f c,
      μ ((D.tile e.1).edge e.2 ∩ segment ℝ P Q)
        = if (D.tile e.1).edge e.2 ⊆ segment ℝ P Q then
            ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) else 0 := by
    intro e he
    obtain ⟨hp, hq, -⟩ := Dissection.mem_lineChain.mp he
    by_cases hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ P Q
    · rw [if_pos hsub, Set.inter_eq_self_of_subset_left hsub]
      show μ (segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) = _
      rw [hμ, MeasureTheory.hausdorffMeasure_segment, edist_dist]
    · rw [if_neg hsub]
      have hdich := edge_clamped f hf c hPQ hfP hfQ hfP' hfQ' hP' hQ' hp hq (hP e he) (hQ e he)
      have hss : ((D.tile e.1).edge e.2 ∩ segment ℝ P Q).Subsingleton := hdich.resolve_right hsub
      exact Erdos634.ChordTraceReal.hausdorffMeasure_one_subsingleton_eq_zero hss
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, MeasureTheory.hausdorffMeasure_segment,
    edist_dist] at hpart
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => dist_nonneg)] at hpart
  exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun _ _ => dist_nonneg)
    dist_nonneg).mp hpart

/-! ### The arithmetic consequence for congruent tiles -/

/-- A finite sum of terms each in `{a, b, c}` is a nonnegative integer combination. -/
theorem sum_mem_semigroup {ι : Type*} (s : Finset ι) (g : ι → ℝ) (a b c : ℝ)
    (h : ∀ i ∈ s, g i = a ∨ g i = b ∨ g i = c) :
    ∃ x y z : ℕ, (x : ℝ) * a + y * b + z * c = ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨x, y, z, hxyz⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi]
    rcases h i (Finset.mem_insert_self i s) with hg | hg | hg
    · exact ⟨x + 1, y, z, by rw [hg]; push_cast; linarith⟩
    · exact ⟨x, y + 1, z, by rw [hg]; push_cast; linarith⟩
    · exact ⟨x, y, z + 1, by rw [hg]; push_cast; linarith⟩

/-- **Every edge of a tile of a `CongruentDissection` with `ModelData` has length `f`, `f²−1`
or `f²`.** -/
theorem edge_length_cases {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ}
    (hM : Erdos634.MarchKillsFan.ModelData D f α β γ) (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = f ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = f ^ 2 - 1 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = f ^ 2 := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
  obtain ⟨m01, m12, m20⟩ := Erdos634.MarchInduction.model_dists D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = f ^ 2 := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = f := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = f ^ 2 - 1 := by rw [dist_comm]; exact m20
  have hk : k ≠ k + 1 := by fin_cases k <;> decide
  have hne : σ k ≠ σ (k + 1) := fun h => hk (σ.injective h)
  rw [hσ]
  generalize σ k = p at hne ⊢
  generalize σ (k + 1) = q at hne ⊢
  fin_cases p <;> fin_cases q <;> simp_all

/-- **The run partition, arithmetic form**: for a `CongruentDissection` with the tile
`(f, f²−1, f²)`, a clamped run's length is a nonnegative integer combination of the three sides. -/
theorem run_partition_semigroup {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ}
    (hM : Erdos634.MarchKillsFan.ModelData D f α β γ)
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hS : segment ℝ P Q ⊆ {y | F y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q)
    (hQ : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) Q' Q P) :
    ∃ x y z : ℕ, (x : ℝ) * f + y * (f ^ 2 - 1) + z * f ^ 2 = dist P Q := by
  classical
  have h := run_partition D.toDissection F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ
  rw [← h]
  exact sum_mem_semigroup _ _ f (f ^ 2 - 1) (f ^ 2) (fun e _ => edge_length_cases D hM e.1 e.2)

/-- Casting the semigroup equation to `ℕ`, for `f = n`. -/
theorem nat_of_real_combo {n x y z : ℕ} {r : ℕ} (hn : 1 ≤ n)
    (h : (x : ℝ) * n + y * ((n : ℝ) ^ 2 - 1) + z * (n : ℝ) ^ 2 = r) :
    x * n + y * (n * n - 1) + z * (n * n) = r := by
  have h1 : ((n * n - 1 : ℕ) : ℝ) = (n : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [h1]
  linear_combination h

/-- **A clamped run of length `b − a = f² − f − 1` is impossible** (`f ≥ 3`). -/
theorem run_b_sub_a_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ}
    (hM : Erdos634.MarchKillsFan.ModelData D f α β γ) {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hS : segment ℝ P Q ⊆ {y | F y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q)
    (hQ : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) Q' Q P)
    (hlen : dist P Q = f ^ 2 - 1 - f) : False := by
  obtain ⟨x, y, z, h⟩ := run_partition_semigroup D hM F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ
  rw [hlen, ← hn] at h
  have h9 : 9 ≤ n * n := by nlinarith
  have hnn : n + 1 ≤ n * n := by nlinarith
  have hr : ((n * n - 1 - n : ℕ) : ℝ) = (n : ℝ) ^ 2 - 1 - n := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [← hr] at h
  exact Erdos634.OrderForcing.east_cover_gap hn3 (nat_of_real_combo (by omega) h)

/-- **A clamped run of length `1` is impossible** (`f ≥ 2`). -/
theorem run_one_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ}
    (hM : Erdos634.MarchKillsFan.ModelData D f α β γ) {n : ℕ} (hn : (n : ℝ) = f) (hn2 : 2 ≤ n)
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ)
    {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hS : segment ℝ P Q ⊆ {y | F y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) P' P Q)
    (hQ : ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) Q' Q P)
    (hlen : dist P Q = 1) : False := by
  obtain ⟨x, y, z, h⟩ := run_partition_semigroup D hM F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ
  rw [hlen, ← hn] at h
  have h' : (x : ℝ) * n + y * ((n : ℝ) ^ 2 - 1) + z * (n : ℝ) ^ 2 = ((1 : ℕ) : ℝ) := by
    rw [h]; norm_num
  have hnat := nat_of_real_combo (by omega) h'
  refine Erdos634.FanKill.one_is_gap n x y z hn2 ?_
  have e1 : n ^ 2 - 1 = n * n - 1 := by ring_nf
  have e2 : n ^ 2 = n * n := by ring
  rw [e1, e2]; exact hnat

/-! ### Non-vacuity: the lemma on `TPErdos.wallDissection` -/

open Erdos634.TPErdos in
/-- Points of the open extension `((−1,−1), (0,0))` are outside the wall target (`y < 0`). -/
theorem wall_left_outside :
    ∀ y ∈ openSegment ℝ (mkPt (-1) (-1)) wallU, y ∉ wallDissection.target.carrier := by
  intro y hy hmem
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have h := gBase_bound_target _ hmem
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, wallU, gBase_pt, gBase_pt] at h
  linarith

open Erdos634.TPErdos in
/-- Points of the open extension `((1,1), (2,2))` are outside the wall target (`x + y > 2`). -/
theorem wall_right_outside :
    ∀ y ∈ openSegment ℝ (mkPt 2 2) wallV, y ∉ wallDissection.target.carrier := by
  intro y hy hmem
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have h := hHyp_bound _ hmem
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, wallV, hHyp_pt, hHyp_pt] at h
  linarith

open Erdos634.TPErdos in
theorem wallU_mem : wallU ∈ openSegment ℝ (mkPt (-1) (-1)) wallV := by
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [wallU, wallV]
  refine Erdos634.MarchInduction.plane_ext ?_ ?_ <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> norm_num

open Erdos634.TPErdos in
theorem wallV_mem : wallV ∈ openSegment ℝ wallU (mkPt 2 2) := by
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [wallU, wallV]
  refine Erdos634.MarchInduction.plane_ext ?_ ?_ <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> norm_num

open Classical Erdos634.TPErdos in
/-- **`run_partition` is not vacuous**: on `wallDissection`, with both ends of the wall
`[(0,0), (1,1)]` clamped by the target boundary (type (c)), the chain edges contained in the wall
have lengths summing to `√2` — and hence there is at least one such edge. -/
theorem run_partition_witness :
    (∑ e ∈ (wallDissection.lineChain wallF 0).filter
        (fun e => (wallDissection.tile e.1).edge e.2 ⊆ segment ℝ wallU wallV),
        dist ((wallDissection.tile e.1).pts e.2) ((wallDissection.tile e.1).pts (e.2 + 1))
      = dist wallU wallV) ∧
    (∃ e ∈ wallDissection.lineChain wallF 0,
      (wallDissection.tile e.1).edge e.2 ⊆ segment ℝ wallU wallV) := by
  have h := run_partition wallDissection wallF wallF_ne 0 wallU_ne_wallV
    (P' := mkPt (-1) (-1)) (Q' := mkPt 2 2) (by rw [wallF_pt]; norm_num)
    (by rw [wallF_pt]; norm_num) wallU_mem wallV_mem wall_hS wall_hint wall_hwall
    (fun e _ => not_straddles_of_outside _ wall_left_outside _ _)
    (fun e _ => not_straddles_of_outside _ wall_right_outside _ _)
  refine ⟨h, ?_⟩
  by_contra hne
  push_neg at hne
  have hempty : (wallDissection.lineChain wallF 0).filter
      (fun e => (wallDissection.tile e.1).edge e.2 ⊆ segment ℝ wallU wallV) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e he; exact hne e he
  rw [hempty, Finset.sum_empty] at h
  exact (dist_pos.mpr wallU_ne_wallV).ne h


/-! ## B. The application: the `c|a` junction's run `b − a` on the `c`-tile's `b`-edge

Configuration (`MarchSlots.junction_c_a`, `cSlotTile` reflection): the `c`-tile on `[x₀ − f², x₀]`
with `β` at `B = (x₀ − f², 0)`, `α` at `V = (x₀, 0)`, apex `A = (x₀ + dBG/f − f², h/f)`; its
`b`-edge is `[V, A]`.  The third tile at `V` in the `GB` branch is `bOverMSet` and in the `BG`
branch's `γ` case `cSplitSet`; **both** lay an `a`-edge `[V, K]` along `[V, A]`, with
`K = V + (a/b)(A − V)`, leaving the run `[K, A]` of length `b − a` exposed.  At `K` the run is
clamped by that tile's own edge (type (b)); at `A` it is clamped by the filler at `B` from
`junction_a_c` (flush or offset), whose edge through `A` carries the tile's interior across the
line beyond `A` (type (a)).  Hence the run is partitioned by whole edges and `b − a` must lie in
`⟨f, f²−1, f²⟩` — it does not (`east_cover_gap`). -/

namespace CSlot

open Erdos634.MarchCoords Erdos634.MarchKills Erdos634.MarchKillsFan Erdos634.MarchInduction
  Erdos634.MarchSlots Erdos634.BaseBetaTargetCoord

/-- The functional `p ↦ −(Y·p₀) − X·p₁`; its level sets are the lines of direction `(−X, Y)`. -/
noncomputable def lineF (X Y : ℝ) : Plane →ₗ[ℝ] ℝ where
  toFun p := -(Y * p 0) - X * p 1
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem lineF_apply (X Y : ℝ) (p : Plane) : lineF X Y p = -(Y * p 0) - X * p 1 := rfl
theorem lineF_pt (X Y u w : ℝ) : lineF X Y (mkPt u w) = -(Y * u) - X * w := by simp

theorem lineF_ne_zero {X Y : ℝ} (hX : X ≠ 0) : lineF X Y ≠ 0 := by
  intro h
  have := congrArg (fun F : Plane →ₗ[ℝ] ℝ => F (mkPt 0 1)) h
  simp only [lineF_pt, LinearMap.zero_apply, mul_zero, neg_zero, mul_one, zero_sub,
    neg_eq_zero] at this
  exact hX this

/-- A segment between two points of a level set lies in it. -/
theorem segment_subset_level (F : Plane →ₗ[ℝ] ℝ) (c : ℝ) {u v : Plane} (hu : F u = c)
    (hv : F v = c) : segment ℝ u v ⊆ {y | F y = c} := by
  rintro y ⟨a, b, ha, hb, hab, rfl⟩
  simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul, hu, hv]
  rw [← add_mul, hab, one_mul]

/-- `lineMap` in coordinates. -/
theorem lineMap_mkPt (a b c d t : ℝ) :
    AffineMap.lineMap (mkPt a b) (mkPt c d) t = mkPt (a + t * (c - a)) (b + t * (d - b)) := by
  apply plane_ext <;> simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] <;> ring

/-- **The edge of a tile between two named vertices**, from its vertex set: some edge is the
segment `P Q` (in one orientation), and the third vertex `R` lies on both other edges. -/
theorem edge_index_of_range {T : Tri} {P Q R : Plane} (hr : Set.range T.pts = {P, Q, R}) :
    ∃ k : Fin 3, (T.edge k = segment ℝ P Q ∨ T.edge k = segment ℝ Q P) ∧
      ∀ k', k' ≠ k → R ∈ T.edge k' := by
  have hP : P ∈ Set.range T.pts := by rw [hr]; simp
  obtain ⟨k₀, hk₀⟩ := hP
  have h3 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  have h3' : ∀ k : Fin 3, k + 1 + 1 = k + 2 := by decide
  have hcov : ∀ k k' : Fin 3, k' ≠ k → k' = k + 1 ∨ k' = k + 2 := by decide
  have hcov2 : ∀ k k' : Fin 3, k' ≠ k + 2 → k' = k ∨ k' = k + 1 := by decide
  rcases vertex_data_of_range hr hk₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨k₀, Or.inl ?_, ?_⟩
    · simp only [Tri.edge, hk₀, h1]
    · intro k' hk'
      rcases hcov k₀ k' hk' with rfl | rfl
      · simp only [Tri.edge, h3', h2]; exact right_mem_segment ℝ _ _
      · simp only [Tri.edge, h3, h2, hk₀]; exact left_mem_segment ℝ _ _
  · refine ⟨k₀ + 2, Or.inr ?_, ?_⟩
    · simp only [Tri.edge, h3, h2, hk₀]
    · intro k' hk'
      rcases hcov2 k₀ k' hk' with rfl | rfl
      · simp only [Tri.edge, hk₀, h1]; exact right_mem_segment ℝ _ _
      · simp only [Tri.edge, h3', h1, h2]; exact left_mem_segment ℝ _ _

/-! ### The points of the configuration -/

/-- `X = f² − dBG/f`: the horizontal extent of the `c`-tile's `b`-edge. -/
noncomputable abbrev Xc (f : ℝ) : ℝ := f ^ 2 - dBG f / f
/-- `Y = h/f`: its vertical extent. -/
noncomputable abbrev Yc (f : ℝ) : ℝ := 1 / f * apexH f

/-- `V = (x₀, 0)`, the `c|a` junction. -/
noncomputable abbrev Vpt (x₀ : ℝ) : Plane := mkPt x₀ 0
/-- `A`, the `c`-tile's apex (as `MarchSlots.left_cSlot` writes it). -/
noncomputable abbrev Apt (x₀ f : ℝ) : Plane := mkPt (x₀ + (dBG f / f - f ^ 2)) (hC f)
/-- `K = V + (a/b)(A − V)`, the far end of the `a`-edge laid along `[V, A]` (as `bOverMSet` and
`cSplitSet` write it). -/
noncomputable abbrev Kpt (x₀ f : ℝ) : Plane :=
  mkPt (x₀ - (2 * f ^ 2 - 1) / (2 * f)) (apexH f / (f ^ 2 - 1))
/-- `A' = V + (1 + 1/(2b))(A − V)`, a point of the line just beyond `A`. -/
noncomputable abbrev Apt' (x₀ f : ℝ) : Plane :=
  mkPt (x₀ - (2 * f ^ 2 - 1) ^ 2 / (4 * f ^ 2)) ((2 * f ^ 2 - 1) / (2 * f * (f ^ 2 - 1)) * apexH f)
/-- The functional of the line `V A`; the uncovered side is `{Fc ≤ cc}`. -/
noncomputable abbrev Fc (f : ℝ) : Plane →ₗ[ℝ] ℝ := lineF (Xc f) (Yc f)
noncomputable abbrev cc (x₀ f : ℝ) : ℝ := -(Yc f * x₀)

/-- The overshoot vertex of `bOverMSet`. -/
noncomputable abbrev Opt (x₀ f : ℝ) : Plane :=
  mkPt (x₀ - f / 2) (f ^ 2 / (f ^ 2 - 1) * apexH f)
/-- The third vertex of `cSplitSet`. -/
noncomputable abbrev Ppt (x₀ f : ℝ) : Plane :=
  mkPt (x₀ + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)

section coords
variable {f : ℝ} (hf : 2 ≤ f) (x₀ : ℝ)
include hf

theorem Xc_pos : 0 < Xc f := by
  have hf0 : (0:ℝ) < f := by linarith
  have : Xc f = (f ^ 2 - 1) * (2 * f ^ 2 - 1) / (2 * f ^ 2) := by
    unfold Xc dBG; field_simp; ring
  rw [this]; have : 0 < f ^ 2 - 1 := by nlinarith
  have : 0 < 2 * f ^ 2 - 1 := by nlinarith
  positivity

theorem Yc_pos : 0 < Yc f := by
  have := apexH_pos (by linarith : 1 < f); unfold Yc; positivity

theorem Fc_V : Fc f (Vpt x₀) = cc x₀ f := by simp [lineF_pt]

theorem Fc_A : Fc f (Apt x₀ f) = cc x₀ f := by
  simp only [Fc, Apt, cc, lineF_pt, Xc, Yc, hC]; ring

theorem Fc_K : Fc f (Kpt x₀ f) = cc x₀ f := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  simp only [Fc, Kpt, cc, lineF_pt, Xc, Yc]; unfold dBG; field_simp; ring

theorem Fc_A' : Fc f (Apt' x₀ f) = cc x₀ f := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  simp only [Fc, Apt', cc, lineF_pt, Xc, Yc]; unfold dBG; field_simp; ring

theorem Fc_O_lt : Fc f (Opt x₀ f) < cc x₀ f := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hh := apexH_pos (by linarith : 1 < f)
  have e : Fc f (Opt x₀ f) - cc x₀ f = -((f ^ 2 - 1) * apexH f) := by
    simp only [Fc, Opt, cc, lineF_pt, Xc, Yc]; unfold dBG; field_simp; ring
  have : 0 < (f ^ 2 - 1) * apexH f := by positivity
  linarith

theorem Fc_P_lt : Fc f (Ppt x₀ f) < cc x₀ f := by
  have hf0 : (0:ℝ) < f := by linarith
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hh := apexH_pos (by linarith : 1 < f)
  have hd := dBG_pos (by linarith : 1 < f)
  have hX := Xc_pos hf
  have hY := Yc_pos hf
  have e : Fc f (Ppt x₀ f) - cc x₀ f
      = -((f ^ 2 - 1) / f ^ 2 * (Yc f * dBG f + Xc f * apexH f)) := by
    simp only [Fc, Ppt, cc, lineF_pt]; ring
  have : 0 < (f ^ 2 - 1) / f ^ 2 * (Yc f * dBG f + Xc f * apexH f) := by positivity
  linarith

theorem Fc_B_gt : cc x₀ f < Fc f (mkPt (x₀ - f ^ 2) 0) := by
  have hY := Yc_pos hf
  have e : Fc f (mkPt (x₀ - f ^ 2) 0) - cc x₀ f = Yc f * f ^ 2 := by
    simp only [Fc, cc, lineF_pt]; ring
  have : 0 < Yc f * f ^ 2 := by positivity
  linarith

theorem K_eq_lineMap : Kpt x₀ f = AffineMap.lineMap (Vpt x₀) (Apt x₀ f) (f / (f ^ 2 - 1)) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  simp only [Kpt, Vpt, Apt, lineMap_mkPt, hC]
  exact mkPt_congr (by unfold dBG; field_simp; ring) (by field_simp; ring)

theorem A'_eq_lineMap :
    Apt' x₀ f = AffineMap.lineMap (Vpt x₀) (Apt x₀ f) ((2 * f ^ 2 - 1) / (2 * (f ^ 2 - 1))) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  simp only [Apt', Vpt, Apt, lineMap_mkPt, hC]
  exact mkPt_congr (by unfold dBG; field_simp; ring) (by field_simp; ring)

theorem V_ne_A : Vpt x₀ ≠ Apt x₀ f := by
  have := hC_pos hf
  exact mkPt_ne_of_snd this.ne

theorem K_ne_A : Kpt x₀ f ≠ Apt x₀ f := by
  have hh := apexH_pos (by linarith : 1 < f)
  have hf0 : (0:ℝ) < f := by linarith
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  refine mkPt_ne_of_snd ?_
  intro h
  simp only [hC] at h
  have h2 := h
  rw [div_eq_iff hb.ne'] at h2
  have h3 : apexH f * f = apexH f * (f ^ 2 - 1) := by
    calc apexH f * f = (1 / f * apexH f * (f ^ 2 - 1)) * f := by rw [← h2]
      _ = apexH f * (f ^ 2 - 1) := by field_simp
  have h4 := mul_left_cancel₀ hh.ne' h3
  nlinarith

theorem K_mem_open : Kpt x₀ f ∈ openSegment ℝ (Vpt x₀) (Apt x₀ f) := by
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hlt : f / (f ^ 2 - 1) < 1 := by rw [div_lt_one hb]; nlinarith
  have hpos : 0 < f / (f ^ 2 - 1) := by positivity
  rw [K_eq_lineMap hf]
  have := (mem_openSegment_lineMap_iff (V_ne_A hf x₀) (0:ℝ) (1:ℝ) (f / (f ^ 2 - 1))).mpr
    (mem_openSegment_real_of (by rw [min_eq_left zero_le_one]; exact hpos)
      (by rw [max_eq_right zero_le_one]; exact hlt))
  rwa [lineMap_zero', lineMap_one'] at this

theorem A_mem_open : Apt x₀ f ∈ openSegment ℝ (Kpt x₀ f) (Apt' x₀ f) := by
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hlt : f / (f ^ 2 - 1) < 1 := by rw [div_lt_one hb]; nlinarith
  have hgt : 1 < (2 * f ^ 2 - 1) / (2 * (f ^ 2 - 1)) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  rw [K_eq_lineMap hf, A'_eq_lineMap hf]
  have := (mem_openSegment_lineMap_iff (V_ne_A hf x₀) (f / (f ^ 2 - 1))
    ((2 * f ^ 2 - 1) / (2 * (f ^ 2 - 1))) (1:ℝ)).mpr
    (mem_openSegment_real_of (by rw [min_eq_left (by linarith)]; exact hlt)
      (by rw [max_eq_right (by linarith)]; exact hgt))
  rwa [lineMap_one'] at this

/-- `|KA| = b − a = f² − 1 − f`. -/
theorem dist_K_A : dist (Kpt x₀ f) (Apt x₀ f) = f ^ 2 - 1 - f := by
  have hf1 : 1 < f := by linarith
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by nlinarith)
  simp only [Kpt, Apt, hC]
  rw [dist_sq_mkPt]
  have hsq := apexH_sq hf1
  have e : (apexH f / (f ^ 2 - 1) - 1 / f * apexH f) ^ 2
      = ((1 / (f ^ 2 - 1) - 1 / f)) ^ 2 * apexH f ^ 2 := by ring
  rw [e, hsq]; unfold h2 dBG; field_simp; ring

/-- `A` is in the target. -/
theorem A_mem_target (hx : f ^ 2 ≤ x₀) (hL : x₀ + f ≤ baseLen 1 f) :
    Apt x₀ f ∈ (baseBetaTarget 1 f one_pos (by linarith)).carrier := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hd := dBG_pos hf1
  have hL' := baseLen_one f
  have e : Apt x₀ f = mkPt (x₀ + (dBG f / f - f ^ 2)) (1 / f * apexH f) := rfl
  rw [e]
  have h1 : 1 / f * dBG f = dBG f / f := by ring
  have hdd : dBG f / f ≤ 3 / 2 := by
    unfold dBG; rw [div_div, div_le_iff₀ (by positivity)]; nlinarith
  refine mem_target_at_level hf1 (by positivity) ?_ ?_
  · rw [h1]; linarith
  · rw [h1]; nlinarith

/-- `K` is in the target's interior. -/
theorem K_mem_interior (hx : f ^ 2 ≤ x₀) (hL : x₀ + f ≤ baseLen 1 f) :
    Kpt x₀ f ∈ interior (baseBetaTarget 1 f one_pos (by linarith)).carrier := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hH := height_pos one_pos hf1
  have hL' := baseLen_one f
  have hapexH : apexH f = height 1 f / f := rfl
  refine Erdos634.ChordChartPlanar.mem_interior_carrier_of_dets_pos (target_det_pos one_pos hf1)
    ?_ ?_ ?_
  · have e : det3 (x₀ - (2 * f ^ 2 - 1) / (2 * f)) (apexH f / (f ^ 2 - 1)) (baseLen 1 f) 0
        (baseLen 1 f / 2) (height 1 f)
        = height 1 f * ((baseLen 1 f - x₀) + (f ^ 4 - 3 * f ^ 2 + 1) / (f * (f ^ 2 - 1))) := by
      unfold det3; rw [hapexH, hL']; field_simp; ring
    rw [e]
    have h1 : 0 < (f ^ 4 - 3 * f ^ 2 + 1) / (f * (f ^ 2 - 1)) := by
      apply div_pos _ (by positivity)
      have h4 : 4 ≤ f ^ 2 := by nlinarith
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f ^ 2 - 4) (by linarith : (0:ℝ) ≤ f ^ 2)]
    have h2 : 0 < baseLen 1 f - x₀ := by linarith
    positivity
  · have e : det3 0 0 (x₀ - (2 * f ^ 2 - 1) / (2 * f)) (apexH f / (f ^ 2 - 1))
        (baseLen 1 f / 2) (height 1 f)
        = height 1 f * ((x₀ * (f ^ 2 - 1) - f ^ 3) / (f ^ 2 - 1)) := by
      unfold det3; rw [hapexH, hL']; field_simp; ring
    rw [e]
    have h1 : 0 < x₀ * (f ^ 2 - 1) - f ^ 3 := by
      have h5 : f ^ 2 * (f ^ 2 - 1) ≤ x₀ * (f ^ 2 - 1) := mul_le_mul_of_nonneg_right hx hb.le
      have h6 : (1:ℝ) ≤ f ^ 2 - f - 1 := by nlinarith
      have h7 : f ^ 2 * 1 ≤ f ^ 2 * (f ^ 2 - f - 1) := mul_le_mul_of_nonneg_left h6 (by positivity)
      nlinarith
    positivity
  · have e : det3 0 0 (baseLen 1 f) 0 (x₀ - (2 * f ^ 2 - 1) / (2 * f)) (apexH f / (f ^ 2 - 1))
        = baseLen 1 f * (apexH f / (f ^ 2 - 1)) := by unfold det3; ring
    rw [e]; have := apexH_pos hf1; have := baseLen_pos one_pos hf1; positivity

/-- **The flush filler at `B` carries its interior across the line beyond `A`.** -/
theorem flush_blocks :
    openSegment ℝ (Apt x₀ f) (Apt' x₀ f) ⊆ interior (flushFiller (x₀ - f ^ 2 - f) f (by linarith)).carrier := by
  have hf1 : 1 < f := by linarith
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hh := apexH_pos hf1
  have hD : 0 < det3 (x₀ - f ^ 2 - f + f) 0 (x₀ - f ^ 2 - f + f + dBG f) (apexH f)
      (x₀ - f ^ 2 - f + dBG f) (apexH f) := by
    have : det3 (x₀ - f ^ 2 - f + f) 0 (x₀ - f ^ 2 - f + f + dBG f) (apexH f)
      (x₀ - f ^ 2 - f + dBG f) (apexH f) = f * apexH f := by unfold det3; ring
    rw [this]; positivity
  have hA : Apt x₀ f ∈ (flushFiller (x₀ - f ^ 2 - f) f hf1).carrier := by
    unfold flushFiller
    refine mem_carrier_of_dets hD ?_ ?_ ?_
    · have e : det3 (x₀ + (dBG f / f - f ^ 2)) (hC f) (x₀ - f ^ 2 - f + f + dBG f) (apexH f)
          (x₀ - f ^ 2 - f + dBG f) (apexH f) = (f - 1) * apexH f := by
        unfold det3 hC; field_simp; ring
      rw [e]; have : (0:ℝ) ≤ f - 1 := by linarith
      positivity
    · have e : det3 (x₀ - f ^ 2 - f + f) 0 (x₀ + (dBG f / f - f ^ 2)) (hC f)
          (x₀ - f ^ 2 - f + dBG f) (apexH f) = apexH f := by
        unfold det3 hC; field_simp; ring
      rw [e]; exact hh.le
    · have e : det3 (x₀ - f ^ 2 - f + f) 0 (x₀ - f ^ 2 - f + f + dBG f) (apexH f)
          (x₀ + (dBG f / f - f ^ 2)) (hC f) = 0 := by
        unfold det3 hC; field_simp; ring
      rw [e]
  have hA' : Apt' x₀ f ∈ interior (flushFiller (x₀ - f ^ 2 - f) f hf1).carrier := by
    unfold flushFiller
    refine Erdos634.ChordChartPlanar.mem_interior_carrier_of_dets_pos hD ?_ ?_ ?_
    · have e : det3 (x₀ - (2 * f ^ 2 - 1) ^ 2 / (4 * f ^ 2))
          ((2 * f ^ 2 - 1) / (2 * f * (f ^ 2 - 1)) * apexH f)
          (x₀ - f ^ 2 - f + f + dBG f) (apexH f) (x₀ - f ^ 2 - f + dBG f) (apexH f)
          = apexH f * (2 * f ^ 3 - 2 * f ^ 2 - 2 * f + 1) / (2 * (f ^ 2 - 1)) := by
        unfold det3 dBG; field_simp; ring
      rw [e]; have : 0 < 2 * f ^ 3 - 2 * f ^ 2 - 2 * f + 1 := by nlinarith
      positivity
    · have e : det3 (x₀ - f ^ 2 - f + f) 0 (x₀ - (2 * f ^ 2 - 1) ^ 2 / (4 * f ^ 2))
          ((2 * f ^ 2 - 1) / (2 * f * (f ^ 2 - 1)) * apexH f)
          (x₀ - f ^ 2 - f + dBG f) (apexH f) = apexH f / 2 := by
        unfold det3 dBG; field_simp; ring
      rw [e]; positivity
    · have e : det3 (x₀ - f ^ 2 - f + f) 0 (x₀ - f ^ 2 - f + f + dBG f) (apexH f)
          (x₀ - (2 * f ^ 2 - 1) ^ 2 / (4 * f ^ 2))
          ((2 * f ^ 2 - 1) / (2 * f * (f ^ 2 - 1)) * apexH f)
          = f ^ 2 * apexH f / (2 * (f ^ 2 - 1)) := by
        unfold det3 dBG; field_simp; ring
      rw [e]; positivity
  exact (flushFiller (x₀ - f ^ 2 - f) f hf1).convex.openSegment_closure_interior_subset_interior
    (subset_closure hA) hA'

/-- **The offset filler at `B` carries its interior across the line beyond `A`.** -/
theorem offset_blocks :
    openSegment ℝ (Apt x₀ f) (Apt' x₀ f) ⊆ interior (offsetFiller (x₀ - f ^ 2 - f) f (by linarith)).carrier := by
  have hf1 : 1 < f := by linarith
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : 0 < f ^ 2 - 1 := by nlinarith
  have hh := apexH_pos hf1
  have hD : 0 < det3 (x₀ - f ^ 2 - f + f) 0
      (x₀ - f ^ 2 - f + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)
      (x₀ - f ^ 2 - f + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f) := by
    have : det3 (x₀ - f ^ 2 - f + f) 0
      (x₀ - f ^ 2 - f + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)
      (x₀ - f ^ 2 - f + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f)
        = f * apexH f := by unfold det3; field_simp; ring
    rw [this]; positivity
  have hA : Apt x₀ f ∈ (offsetFiller (x₀ - f ^ 2 - f) f hf1).carrier := by
    unfold offsetFiller
    refine mem_carrier_of_dets hD ?_ ?_ ?_
    · have e : det3 (x₀ + (dBG f / f - f ^ 2)) (hC f)
          (x₀ - f ^ 2 - f + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)
          (x₀ - f ^ 2 - f + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f)
          = f * apexH f * (f ^ 2 - f - 1) / (f ^ 2 - 1) := by
        unfold det3 hC dBG; field_simp; ring
      rw [e]; have : (0:ℝ) ≤ f ^ 2 - f - 1 := by nlinarith
      positivity
    · have e : det3 (x₀ - f ^ 2 - f + f) 0 (x₀ + (dBG f / f - f ^ 2)) (hC f)
          (x₀ - f ^ 2 - f + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f)
          = f ^ 2 * apexH f / (f ^ 2 - 1) := by
        unfold det3 hC dBG; field_simp; ring
      rw [e]; positivity
    · have e : det3 (x₀ - f ^ 2 - f + f) 0
          (x₀ - f ^ 2 - f + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)
          (x₀ + (dBG f / f - f ^ 2)) (hC f) = 0 := by
        unfold det3 hC dBG; field_simp; ring
      rw [e]
  have hA' : Apt' x₀ f ∈ interior (offsetFiller (x₀ - f ^ 2 - f) f hf1).carrier := by
    unfold offsetFiller
    refine Erdos634.ChordChartPlanar.mem_interior_carrier_of_dets_pos hD ?_ ?_ ?_
    · have e : det3 (x₀ - (2 * f ^ 2 - 1) ^ 2 / (4 * f ^ 2))
          ((2 * f ^ 2 - 1) / (2 * f * (f ^ 2 - 1)) * apexH f)
          (x₀ - f ^ 2 - f + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)
          (x₀ - f ^ 2 - f + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f)
          = apexH f * (2 * f ^ 3 - 2 * f ^ 2 - 2 * f + 1) / (2 * (f ^ 2 - 1)) := by
        unfold det3 dBG; field_simp; ring
      rw [e]; have : 0 < 2 * f ^ 3 - 2 * f ^ 2 - 2 * f + 1 := by nlinarith
      positivity
    · have e : det3 (x₀ - f ^ 2 - f + f) 0 (x₀ - (2 * f ^ 2 - 1) ^ 2 / (4 * f ^ 2))
          ((2 * f ^ 2 - 1) / (2 * f * (f ^ 2 - 1)) * apexH f)
          (x₀ - f ^ 2 - f + f + f ^ 2 / (f ^ 2 - 1) * (dBG f - f)) (f ^ 2 / (f ^ 2 - 1) * apexH f)
          = f ^ 2 * apexH f / (2 * (f ^ 2 - 1)) := by
        unfold det3 dBG; field_simp; ring
      rw [e]; positivity
    · have e : det3 (x₀ - f ^ 2 - f + f) 0
          (x₀ - f ^ 2 - f + f + (f ^ 2 - 1) / f ^ 2 * dBG f) ((f ^ 2 - 1) / f ^ 2 * apexH f)
          (x₀ - (2 * f ^ 2 - 1) ^ 2 / (4 * f ^ 2))
          ((2 * f ^ 2 - 1) / (2 * f * (f ^ 2 - 1)) * apexH f) = apexH f / 2 := by
        unfold det3 dBG; field_simp; ring
      rw [e]; positivity
  exact (offsetFiller (x₀ - f ^ 2 - f) f hf1).convex.openSegment_closure_interior_subset_interior
    (subset_closure hA) hA'

end coords

/-- The vertex sets of the two candidates, in the order `{V, K, W}`. -/
theorem bOverMSet_eq (x₀ f : ℝ) : bOverMSet x₀ f = {Vpt x₀, Kpt x₀ f, Opt x₀ f} := by
  unfold bOverMSet; exact congrArg (insert _) (Set.pair_comm _ _)

theorem cSplitSet_eq (x₀ f : ℝ) : cSplitSet x₀ f = {Vpt x₀, Kpt x₀ f, Ppt x₀ f} := rfl

/-- The `c`-tile's vertex set in the order `{V, A, B}`. -/
theorem cSlot_range_eq {f : ℝ} (hf : 1 < f) (x₀ : ℝ) :
    Set.range (cSlotTile (x₀ - f ^ 2) f hf).pts = {Vpt x₀, Apt x₀ f, mkPt (x₀ - f ^ 2) 0} := by
  rw [left_cSlot hf]; exact congrArg (insert _) (Set.pair_comm _ _)

/-- **THE `c`-SLOT RUN KILL.**  In a `CongruentDissection` of the `e = 1` target (`f = n ≥ 3`)
containing the `c`-tile `cSlotTile (x₀ − f²)`, a tile with vertices `V`, `K` and a third vertex
`W` strictly on the uncovered side of the line `V A`, and a tile whose interior contains the open
extension `(A, A')` of that line beyond the apex `A`: **contradiction**.  The run `[K, A]` of
length `b − a` is clamped at `K` by the `V K` edge (type (b)) and at `A` by the interior (type
(a)), so it is partitioned by whole edges, and `b − a ∉ ⟨f, f²−1, f²⟩`. -/
theorem cslot_run_kill {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {x₀ : ℝ} (hx : f ^ 2 ≤ x₀) (hL : x₀ + f ≤ baseLen 1 f)
    {i l m : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts)
    {W : Plane} (hW : Fc f W < cc x₀ f)
    (hl : Set.range (D.tile l).pts = {Vpt x₀, Kpt x₀ f, W})
    (hm : openSegment ℝ (Apt x₀ f) (Apt' x₀ f) ⊆ interior (D.tile m).carrier) : False := by
  classical
  have hf1 : 1 < f := by linarith
  have hX := Xc_pos hf
  have hF : Fc f ≠ 0 := lineF_ne_zero hX.ne'
  have hFV := Fc_V hf x₀
  have hFA := Fc_A hf x₀
  have hFK := Fc_K hf x₀
  have hFA' := Fc_A' hf x₀
  have hKA := K_ne_A hf x₀
  have hVA := V_ne_A hf x₀
  have hKopen := K_mem_open hf x₀
  have hAopen := A_mem_open hf x₀
  -- the `c`-tile's `b`-edge `[V, A]`
  rw [cSlot_range_eq hf1] at hi
  obtain ⟨ki, hki, -⟩ := edge_index_of_range hi
  have hVA_edge : segment ℝ (Vpt x₀) (Apt x₀ f) ⊆ (D.tile i).edge ki := by
    rcases hki with h | h
    · rw [h]
    · rw [h, segment_symm]
  -- the `V K` edge of tile `l`
  obtain ⟨kl, hkl, hklW⟩ := edge_index_of_range hl
  have hVK_edge : (D.tile l).edge kl = segment ℝ (Vpt x₀) (Kpt x₀ f) := by
    rcases hkl with h | h
    · exact h
    · rw [h, segment_symm]
  have hle_l : ∀ y ∈ (D.tile l).carrier, Fc f y ≤ cc x₀ f := by
    refine (D.tile l).carrier_subset_halfplane _ _ ?_
    intro idx
    have hmem : (D.tile l).pts idx ∈ ({Vpt x₀, Kpt x₀ f, W} : Set Plane) := hl ▸ ⟨idx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h <;> rw [h]
    · exact hFV.le
    · exact hFK.le
    · exact hW.le
  have hE_l : ∀ y ∈ (D.tile l).edge kl, Fc f y = cc x₀ f := by
    rw [hVK_edge]; exact fun y hy => segment_subset_level _ _ hFV hFK hy
  -- the wall hypotheses
  have hS : segment ℝ (Kpt x₀ f) (Apt x₀ f) ⊆ {y | Fc f y = cc x₀ f} :=
    segment_subset_level _ _ hFK hFA
  have hKA_sub : segment ℝ (Kpt x₀ f) (Apt x₀ f) ⊆ segment ℝ (Vpt x₀) (Apt x₀ f) :=
    (convex_segment _ _).segment_subset (openSegment_subset_segment ℝ _ _ hKopen)
      (right_mem_segment ℝ _ _)
  have hint : openSegment ℝ (Kpt x₀ f) (Apt x₀ f) ⊆ interior D.target.carrier := by
    rw [htgt]
    exact (baseBetaTarget 1 f one_pos hf1).convex.openSegment_interior_closure_subset_interior
      (K_mem_interior hf x₀ hx hL) (subset_closure (A_mem_target hf x₀ hx hL))
  have hwall : ∀ y ∈ openSegment ℝ (Kpt x₀ f) (Apt x₀ f), ∀ j, y ∉ interior (D.tile j).carrier := by
    intro y hy j
    exact D.edge_point_not_interior (hVA_edge (hKA_sub (openSegment_subset_segment ℝ _ _ hy))) j
  -- clamping at `K` (type (b)) and at `A` (type (a))
  have hP : ∀ e ∈ D.lineChain (Fc f) (cc x₀ f),
      ¬ Straddles ((D.tile e.1).edge e.2) (Vpt x₀) (Kpt x₀ f) (Apt x₀ f) := by
    intro e he
    by_cases hel : e.1 = l
    · by_cases hek : e.2 = kl
      · have heq : e = (l, kl) := Prod.ext hel hek
        rw [heq]
        exact not_straddles_extension (Fc f) hF (cc x₀ f) hKA hFK hFA hFV hKopen
          (by rw [hVK_edge])
      · exfalso
        have hWe : W ∈ (D.tile e.1).edge e.2 := by rw [hel]; exact hklW e.2 hek
        have := D.lineChain_edge_subset he W hWe
        linarith
    · exact not_straddles_of_sameside_edge D.toDissection (Fc f) hF (cc x₀ f) hKA hFK hFA hFV
        hKopen hle_l hE_l (by rw [hVK_edge]) he (fun h => hel (by rw [h]))
  have hm' : openSegment ℝ (Apt' x₀ f) (Apt x₀ f) ⊆ interior (D.tile m).carrier := by
    rw [openSegment_symm]; exact hm
  have hQ : ∀ e ∈ D.lineChain (Fc f) (cc x₀ f),
      ¬ Straddles ((D.tile e.1).edge e.2) (Apt' x₀ f) (Apt x₀ f) (Kpt x₀ f) :=
    fun e _ => not_straddles_of_interior D.toDissection hm' e.1 e.2
  exact run_b_sub_a_dies D hM hn hn3 (Fc f) hF (cc x₀ f) hKA hFV hFA' hKopen hAopen hS hint hwall
    hP hQ (dist_K_A hf x₀)

/-- The filler at `B` as `junction_a_c` delivers it: flush or offset at the virtual junction. -/
def FillerAtB {N : ℕ} (D : CongruentDissection N) (f x₀ : ℝ) (hf : 1 < f) (m : Fin N) : Prop :=
  Set.range (D.tile m).pts = Set.range (flushFiller (x₀ - f ^ 2 - f) f hf).pts ∨
  Set.range (D.tile m).pts = Set.range (offsetFiller (x₀ - f ^ 2 - f) f hf).pts

theorem filler_blocks {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 2 ≤ f) (x₀ : ℝ)
    {m : Fin N} (hm : FillerAtB D f x₀ (by linarith) m) :
    openSegment ℝ (Apt x₀ f) (Apt' x₀ f) ⊆ interior (D.tile m).carrier := by
  have hf1 : 1 < f := by linarith
  rcases hm with h | h
  · have hc : (D.tile m).carrier = (flushFiller (x₀ - f ^ 2 - f) f hf1).carrier := by
      unfold Tri.carrier; rw [h]
    rw [hc]; exact flush_blocks hf x₀
  · have hc : (D.tile m).carrier = (offsetFiller (x₀ - f ^ 2 - f) f hf1).carrier := by
      unfold Tri.carrier; rw [h]
    rw [hc]; exact offset_blocks hf x₀

/-- **`bOverMSet` dies** (the `cSlotTile + GB` branch's overshoot placement). -/
theorem bOverM_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {x₀ : ℝ} (hx : f ^ 2 ≤ x₀) (hL : x₀ + f ≤ baseLen 1 f) {i l m : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts)
    (hl : Set.range (D.tile l).pts = bOverMSet x₀ f)
    (hm : FillerAtB D f x₀ (by linarith) m) : False :=
  cslot_run_kill D hf hn hn3 htgt hM hx hL hi (Fc_O_lt hf x₀) (by rw [hl, bOverMSet_eq])
    (filler_blocks D hf x₀ hm)

/-- **`cSplitSet` dies** (the `cSlotTile + BG` branch's split `γ`-placement). -/
theorem cSplit_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {x₀ : ℝ} (hx : f ^ 2 ≤ x₀) (hL : x₀ + f ≤ baseLen 1 f) {i l m : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts)
    (hl : Set.range (D.tile l).pts = cSplitSet x₀ f)
    (hm : FillerAtB D f x₀ (by linarith) m) : False :=
  cslot_run_kill D hf hn hn3 htgt hM hx hL hi (Fc_P_lt hf x₀) (by rw [hl, cSplitSet_eq])
    (filler_blocks D hf x₀ hm)

/-- **`junction_c_a`, with the two run-killed placements removed.**  With the filler at `B`
present (as `junction_a_c` supplies it) and `f = n ≥ 3`: after `cSlotTile`, the next `a` is `GB`
with the `β`-tile at `V` **the cap `bCapMSet`**, or `BG` with the `γ`-tile **the flat cap
`cCapSet`** or the fan `{3α, 2β}`.  `bOverMSet` and `cSplitSet` are gone. -/
theorem junction_c_a_run {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {x₀ : ℝ} (hx : f ^ 2 ≤ x₀) (hxL : x₀ < baseLen 1 f)
    (hL : x₀ + f ≤ baseLen 1 f)
    {i j m : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts)
    (hm : FillerAtB D f x₀ (by linarith) m)
    {k m' : Fin 3} (hkm : k ≠ m')
    (hk : (D.tile j).pts k = mkPt x₀ 0) (hm' : (D.tile j).pts m' = mkPt (x₀ + f) 0) :
    (Set.range (D.tile j).pts = Set.range (aTileGB x₀ f (by linarith)).pts ∧
      ∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = β ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = β → l' = l) ∧
        Set.range (D.tile l).pts = bCapMSet x₀ f) ∨
    (Set.range (D.tile j).pts = Set.range (aTileBG x₀ f (by linarith)).pts ∧
      ((∃ l : Fin N, l ≠ i ∧ l ≠ j ∧ (D.tile l).localAngle (mkPt x₀ 0) = γ ∧
        (∀ l', (D.tile l').localAngle (mkPt x₀ 0) = γ → l' = l) ∧
        Set.range (D.tile l).pts = cCapSet x₀ f) ∨
       (({n | (D.tile n).localAngle (mkPt x₀ 0) = α} : Finset (Fin N)).card = 3 ∧
        ({n | (D.tile n).localAngle (mkPt x₀ 0) = β} : Finset (Fin N)).card = 2 ∧
        ({n | (D.tile n).localAngle (mkPt x₀ 0) = γ} : Finset (Fin N)).card = 0))) := by
  have hx0 : 0 < x₀ := by nlinarith
  rcases junction_c_a D hf htgt hM hA hx0 hxL hi hkm hk hm' with
    ⟨hj, l, hli, hlj, hl, huniq, hcap | hover⟩ | ⟨hj, ⟨l, hli, hlj, hl, huniq, hcap | hsplit⟩ | hfan⟩
  · exact Or.inl ⟨hj, l, hli, hlj, hl, huniq, hcap⟩
  · exact absurd hover (fun h => bOverM_dies D hf hn hn3 htgt hM hx hL hi h hm)
  · exact Or.inr ⟨hj, Or.inl ⟨l, hli, hlj, hl, huniq, hcap⟩⟩
  · exact absurd hsplit (fun h => cSplit_dies D hf hn hn3 htgt hM hx hL hi h hm)
  · exact Or.inr ⟨hj, Or.inr hfan⟩

/-! ### Non-vacuity of the configuration's hypotheses, `f = 4`, `x₀ = 20` (`N = 47`, prime)

The kill's hypotheses are jointly unsatisfiable by design.  Individually: the `c`-tile
`cSlotTile 4 4` is in the target (`MarchKillsFan.cslot_config_in_target`), the run `[K, A]` has
length `b − a = 11` (`dist_K_A`), `K` is interior to the target (`K_mem_interior`), and the
filler's interior really contains the extension beyond `A` (`flush_blocks`, `offset_blocks`);
the numbers: -/
theorem config_f4 :
    Kpt 20 4 = mkPt (129 / 8) (apexH 4 / 15) ∧
    dist (Kpt 20 4) (Apt 20 4) = 11 ∧
    Kpt 20 4 ∈ interior (baseBetaTarget 1 4 one_pos (by norm_num)).carrier ∧
    (∀ k, (cSlotTile 4 4 (by norm_num)).pts k ∈ (baseBetaTarget 1 4 one_pos (by norm_num)).carrier) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Kpt; exact mkPt_congr (by norm_num) (by norm_num)
  · have := dist_K_A (f := 4) (by norm_num) 20; rw [this]; norm_num
  · exact K_mem_interior (f := 4) (by norm_num) 20 (by norm_num) (by rw [baseLen_one]; norm_num)
  · exact (cslot_config_in_target (f := 4) (by norm_num) (x := 4) (by norm_num)
      (by rw [baseLen_one]; unfold dBG; norm_num)).1

end CSlot

end Erdos634.RunPartition

#print axioms Erdos634.RunPartition.edge_clamped
#print axioms Erdos634.RunPartition.not_straddles_of_interior
#print axioms Erdos634.RunPartition.not_straddles_of_sameside_edge
#print axioms Erdos634.RunPartition.not_straddles_of_outside
#print axioms Erdos634.RunPartition.run_partition
#print axioms Erdos634.RunPartition.run_partition_semigroup
#print axioms Erdos634.RunPartition.run_b_sub_a_dies
#print axioms Erdos634.RunPartition.run_one_dies
#print axioms Erdos634.RunPartition.run_partition_witness
#print axioms Erdos634.RunPartition.CSlot.cslot_run_kill
#print axioms Erdos634.RunPartition.CSlot.bOverM_dies
#print axioms Erdos634.RunPartition.CSlot.cSplit_dies
#print axioms Erdos634.RunPartition.CSlot.junction_c_a_run
#print axioms Erdos634.RunPartition.CSlot.config_f4
