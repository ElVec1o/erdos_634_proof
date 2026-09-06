import Erdos634.CoversGeneral
import Erdos634.SubDissection
import Erdos634.CongruentArea
import Erdos634.Tiling44Bridge

/-!
# `TP_hales` — the packing layer, and G1 discharged by an area/count certificate

Erdős #634, room `tileplace`, HALES mode (2026-09-07).  The question this file answers is whether
the blocked tile-placement atoms need a *placement layer* or only a *certificate*, in the Flyspeck
sense: a finite, exactly-checkable arithmetic fact standing in for a synthetic-geometry argument.

## What is here

**1. `Packing` / `CongruentPacking` — the missing object.**  A `Dissection` carries `covers`;
this is the same data with `covers` replaced by mere containment.  It is the object a *partial*
dissection is (F1's 17-of-23 witness is a `CongruentPacking 17`, not a `Dissection`), and it did
not exist in the corpus — searched 2026-09-07, `code/novelty_check.sh`, no match in `lean/`,
`paper/` or `private/`.

**2. `Packing.covers_iff` — the sharp form of G1 for a fixed instance.**  A packing's tiles cover
its target *if and only if* their areas sum to the target's.  So on a fixed instance nothing
geometric separates a packing from a dissection: one area identity does, and an area identity in
exact coordinates is a determinant sum (`AreaDet.area_identity_of_det`), i.e. a certificate.

**3. `covers_of_volume_finset` and `restrictOfCount` — G1 discharged in `SubDissection`'s own
form.**  `SubDissection.restrict` takes `(⋃ i ∈ S, (D.tile i).carrier) = T.carrier` as a
hypothesis, and its header calls that hypothesis "exactly as unbuilt as before".  It is now built,
from two weaker inputs: each selected tile lies in `T`, and `|S|·|model| = |T|`.  For a
`CongruentDissection` the second input is a **counting** identity, not a geometric one.

**4. Non-vacuity.**  `packing17` and `packing38` are genuine `CongruentPacking`s over `ℤ[√15]`
coordinates, obtained by selecting 17 and 38 of `Tiling44Bridge.dissection`'s 44 tiles;
`packing38_residue` is the residue-6 shape `LocalCriterionBound` (F2) consumes.

## What is NOT here, stated exactly

* This is **not** F1.  F1's 17 tiles are a *maximal* packing of the `(2,3)` `m=1` target
  (`N = 23`, tile `(6,5,9)`, target `(0,0)–(46,0)–(23,10√2)`) that extends to no tiling.  The
  witnesses below are sub-families of an *existing* 44-tiling, so they do extend.  They witness
  that the type is inhabited and that the theorems below are not vacuous; they do not witness F1's
  content.  **F1's exact coordinates were verified on 2026-09-06 and then not persisted anywhere in
  this repository** — the layer is ready to receive them, and recovering them is a data task.
* A certificate is **instance-bound**.  Nothing here reaches a statement uniform in `(e,f)`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TPHales

open Erdos634.Geometry MeasureTheory
open scoped ENNReal

variable {N : ℕ}

/-! ## 1. The packing object -/

/-- **A partial packing of a triangle by triangles.**  `Dissection` with `covers` deleted:
the tiles sit inside the target with pairwise disjoint interiors, but need not fill it. -/
structure Packing (N : ℕ) where
  /-- The triangle being packed. -/
  target : Tri
  /-- The tiles. -/
  tile : Fin N → Tri
  /-- Each tile lies inside the target. -/
  contained : ∀ i, (tile i).carrier ⊆ target.carrier
  /-- Distinct tiles have disjoint interiors. -/
  interiors_disjoint :
    Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)

/-- **A packing by congruent copies of one tile.** -/
structure CongruentPacking (N : ℕ) extends Packing N where
  /-- The tile every piece is a copy of. -/
  model : Tri
  /-- Every piece is congruent to it. -/
  tiles_congruent : ∀ i, (tile i).Congruent model

namespace Packing

/-- The packed area is the sum of the tile areas — disjoint interiors, null frontiers. -/
theorem volume_iUnion (P : Packing N) :
    volume (⋃ i, (P.tile i).carrier) = ∑ i, volume (P.tile i).carrier :=
  Erdos634.ConvexCover.volume_iUnion_eq_sum P.tile P.interiors_disjoint

/-- **The packing bound.**  A packing's tiles have total area at most the target's. -/
theorem volume_sum_le (P : Packing N) :
    ∑ i, volume (P.tile i).carrier ≤ volume P.target.carrier := by
  rw [← P.volume_iUnion]
  exact measure_mono (Set.iUnion_subset P.contained)

/-- **G1 on a fixed instance, sharp.**  A packing covers its target **iff** the tile areas sum to
the target's area.  Left to right is monotonicity of measure; right to left is
`ConvexCover.covers_of_volume`.  So on a fixed instance the whole of covering-equality is one
area identity — and in exact coordinates that identity is a determinant sum. -/
theorem covers_iff (P : Packing N) :
    (⋃ i, (P.tile i).carrier) = P.target.carrier ↔
      ∑ i, volume (P.tile i).carrier = volume P.target.carrier := by
  constructor
  · intro h
    rw [← P.volume_iUnion, h]
  · intro h
    exact Erdos634.ConvexCover.covers_of_volume P.target P.tile P.contained
      P.interiors_disjoint h

/-- **The promotion.**  A packing whose areas sum correctly *is* a dissection. -/
noncomputable def toDissection (P : Packing N)
    (hvol : ∑ i, volume (P.tile i).carrier = volume P.target.carrier) : Dissection N :=
  Erdos634.ConvexCover.ofCertificate P.target P.tile P.contained P.interiors_disjoint hvol

theorem toDissection_target (P : Packing N)
    (hvol : ∑ i, volume (P.tile i).carrier = volume P.target.carrier) :
    (P.toDissection hvol).target = P.target := rfl

theorem toDissection_tile (P : Packing N)
    (hvol : ∑ i, volume (P.tile i).carrier = volume P.target.carrier) (i : Fin N) :
    (P.toDissection hvol).tile i = P.tile i := rfl

/-- **Every sub-family of a dissection is a packing.**  The source of every witness below. -/
def ofDissection {M : ℕ} (D : Dissection N) (emb : Fin M ↪ Fin N) : Packing M where
  target := D.target
  tile := fun j => D.tile (emb j)
  contained := by
    intro j x hx
    rw [← D.covers]
    exact Set.mem_iUnion_of_mem (emb j) hx
  interiors_disjoint := fun j j' hjj' =>
    D.interiors_disjoint (fun h => hjj' (emb.injective h))

end Packing

namespace CongruentPacking

/-- Every tile has the model's area. -/
theorem volume_tile (P : CongruentPacking N) (i : Fin N) :
    volume (P.tile i).carrier = volume P.model.carrier :=
  Erdos634.CongruentArea.volume_congruent (P.tiles_congruent i)

theorem volume_sum (P : CongruentPacking N) :
    ∑ i, volume (P.tile i).carrier = (N : ℝ≥0∞) * volume P.model.carrier := by
  rw [Finset.sum_congr rfl (fun i _ => P.volume_tile i)]
  simp [Finset.card_univ, nsmul_eq_mul]

/-- **The packing inequality.**  `N · |t| ≤ |T|`. -/
theorem card_mul_volume_le (P : CongruentPacking N) :
    (N : ℝ≥0∞) * volume P.model.carrier ≤ volume P.target.carrier := by
  rw [← P.volume_sum]
  exact P.toPacking.volume_sum_le

/-- **A packing of a target of area `M·|t|` has at most `M` tiles.**  The certificate-side
counting bound: no geometry beyond containment and disjointness enters. -/
theorem card_le (P : CongruentPacking N) (M : ℕ)
    (hT : volume P.target.carrier = (M : ℝ≥0∞) * volume P.model.carrier) : N ≤ M := by
  have h := P.card_mul_volume_le
  rw [hT] at h
  have hpos : volume P.model.carrier ≠ 0 := ne_of_gt P.model.volume_pos
  have htop : volume P.model.carrier ≠ ⊤ := P.model.volume_ne_top
  rw [mul_comm (N : ℝ≥0∞), mul_comm (M : ℝ≥0∞)] at h
  have h' : (N : ℝ≥0∞) ≤ (M : ℝ≥0∞) := (ENNReal.mul_le_mul_iff_right hpos htop).mp h
  exact_mod_cast h'

/-- **The residue has area exactly `(M − N)` tiles.**  Stated additively to avoid truncated
subtraction: the packed area plus `(M−N)` tile areas is the target's area.  This is the geometric
form of the `|T \ W|` bookkeeping `LocalCriterionBound` (F2) does combinatorially. -/
theorem residue_volume (P : CongruentPacking N) (M : ℕ)
    (hT : volume P.target.carrier = (M : ℝ≥0∞) * volume P.model.carrier) :
    ∑ i, volume (P.tile i).carrier + ((M - N : ℕ) : ℝ≥0∞) * volume P.model.carrier
      = volume P.target.carrier := by
  have hle : N ≤ M := P.card_le M hT
  rw [P.volume_sum, hT, ← add_mul]
  congr 1
  rw [← Nat.cast_add, Nat.add_sub_cancel' hle]

/-- **The promotion, for congruent packings.**  A congruent packing of a target of area `M·|t|`
that has all `M` tiles is a `CongruentDissection`. -/
noncomputable def toCongruentDissection (P : CongruentPacking N)
    (hT : volume P.target.carrier = (N : ℝ≥0∞) * volume P.model.carrier) :
    CongruentDissection N where
  toDissection := P.toPacking.toDissection (by rw [P.volume_sum, hT])
  model := P.model
  tiles_congruent := P.tiles_congruent

/-- **Every sub-family of a congruent dissection is a congruent packing.** -/
def ofCongruentDissection {M : ℕ} (D : CongruentDissection N) (emb : Fin M ↪ Fin N) :
    CongruentPacking M where
  toPacking := Packing.ofDissection D.toDissection emb
  model := D.model
  tiles_congruent := fun j => D.tiles_congruent (emb j)

theorem ofCongruentDissection_target {M : ℕ} (D : CongruentDissection N) (emb : Fin M ↪ Fin N) :
    (ofCongruentDissection D emb).target = D.target := rfl

theorem ofCongruentDissection_model {M : ℕ} (D : CongruentDissection N) (emb : Fin M ↪ Fin N) :
    (ofCongruentDissection D emb).model = D.model := rfl

end CongruentPacking

/-! ## 2. G1 discharged: `SubDissection`'s covering hypothesis from containment plus a count -/

/-- **Covering-equality for a `Finset`-indexed sub-family, from containment and area.**

`SubDissection.restrict` requires `(⋃ i ∈ S, (D.tile i).carrier) = T.carrier` and its header
records that hypothesis as unbuilt.  Here it is derived from strictly weaker data: each selected
tile lies in `T`, the tiles have disjoint interiors (which a `Dissection` already supplies), and
the selected areas sum to `|T|`. -/
theorem covers_of_volume_finset {N : ℕ} (tile : Fin N → Tri) (S : Finset (Fin N)) (T : Tri)
    (hsub : ∀ i ∈ S, (tile i).carrier ⊆ T.carrier)
    (hdisj : Pairwise fun i j =>
      Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (hvol : ∑ i ∈ S, volume (tile i).carrier = volume T.carrier) :
    (⋃ i ∈ S, (tile i).carrier) = T.carrier := by
  classical
  have hre : (⋃ i ∈ S, (tile i).carrier)
      = ⋃ j : Fin S.card, (tile (S.orderEmbOfFin rfl j)).carrier := by
    apply le_antisymm
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hiS, hxi⟩ := hx
      have hiS' : i ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hiS
      obtain ⟨j, hji⟩ := hiS'
      simp only [Set.mem_iUnion]
      exact ⟨j, hji ▸ hxi⟩
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨j, hxj⟩ := hx
      simp only [Set.mem_iUnion]
      exact ⟨S.orderEmbOfFin rfl j, S.orderEmbOfFin_mem rfl j, hxj⟩
  have hsum : ∑ i ∈ S, volume (tile i).carrier
      = ∑ j : Fin S.card, volume (tile (S.orderEmbOfFin rfl j)).carrier := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
    exact Finset.sum_map _ _ _
  rw [hre]
  exact Erdos634.ConvexCover.covers_of_volume T (fun j => tile (S.orderEmbOfFin rfl j))
    (fun j => hsub _ (S.orderEmbOfFin_mem rfl j))
    (fun j j' h => hdisj (fun x => h ((S.orderEmbOfFin rfl).injective x)))
    (by rw [← hsum, hvol])

/-- **G1, for a congruent dissection, is a counting identity.**

Restrict a `CongruentDissection` to a tile subset `S` and a triangle `T`, given only:
(i) each selected tile lies in `T`, and (ii) `|T| = |S| · |model|`.  No covering hypothesis.
This is the object `thm:farregion`/`cor:farvacuous` and `prop:orientmono`'s inflated-tile
instantiation ask for, with the geometric hypothesis replaced by an arithmetic one. -/
noncomputable def restrictOfCount {N : ℕ} (D : CongruentDissection N) (S : Finset (Fin N))
    (T : Tri) (hsub : ∀ i ∈ S, (D.tile i).carrier ⊆ T.carrier)
    (hcount : volume T.carrier = (S.card : ℝ≥0∞) * volume D.model.carrier) :
    CongruentDissection S.card :=
  Erdos634.SubDissection.restrictCongruent D S T
    (covers_of_volume_finset D.tile S T hsub D.interiors_disjoint (by
      have hc : ∑ i ∈ S, volume (D.tile i).carrier = ∑ _i ∈ S, volume D.model.carrier :=
        Finset.sum_congr rfl (fun i _ =>
          Erdos634.CongruentArea.volume_congruent (D.tiles_congruent i))
      rw [hc, Finset.sum_const, hcount, nsmul_eq_mul]))

theorem restrictOfCount_target {N : ℕ} (D : CongruentDissection N) (S : Finset (Fin N))
    (T : Tri) (hsub : ∀ i ∈ S, (D.tile i).carrier ⊆ T.carrier)
    (hcount : volume T.carrier = (S.card : ℝ≥0∞) * volume D.model.carrier) :
    (restrictOfCount D S T hsub hcount).target = T := rfl

theorem restrictOfCount_model {N : ℕ} (D : CongruentDissection N) (S : Finset (Fin N))
    (T : Tri) (hsub : ∀ i ∈ S, (D.tile i).carrier ⊆ T.carrier)
    (hcount : volume T.carrier = (S.card : ℝ≥0∞) * volume D.model.carrier) :
    (restrictOfCount D S T hsub hcount).model = D.model := rfl

/-! ## 3. Non-vacuity: two genuine congruent packings over `ℤ[√15]`

`Tiling44Bridge.dissection` is the kernel-checked 44-tiling of `(16,16,22)` by `(2,3,4)` tiles,
scaled by 8 into `ℤ[√15]`.  Selecting an initial segment of its tiles gives a packing.

**Honesty note, repeated from the header.**  These are sub-families of an existing tiling, so they
extend to one.  They are here so that §1's theorems are demonstrably non-vacuous, and so that the
`card_le` / `residue_volume` arithmetic runs end to end on a real object.  They are NOT F1. -/

theorem len44 : Tiling44.tiles.length = 44 := Tiling44Bridge.tiles_length_eq_44

/-- The 44-tiling's target has 44 times the model's area. -/
theorem tiling44_volume_target :
    volume Tiling44Bridge.dissection.target.carrier
      = (44 : ℝ≥0∞) * volume Tiling44Bridge.dissection.model.carrier := by
  have h := Erdos634.CongruentArea.congruentDissection_volume_target Tiling44Bridge.dissection
  rw [h]
  congr 1


/-- `Fin k ↪ Fin 44 = Fin Tiling44.tiles.length`, for `k ≤ 44`. -/
def selEmb {k : ℕ} (h : k ≤ Tiling44.tiles.length) : Fin k ↪ Fin Tiling44.tiles.length :=
  ⟨Fin.castLE h, fun a b hab => by simpa [Fin.castLE, Fin.ext_iff] using hab⟩

theorem le17 : 17 ≤ Tiling44.tiles.length := by rw [len44]; norm_num

theorem le38 : 38 ≤ Tiling44.tiles.length := by rw [len44]; norm_num

/-- **A genuine `CongruentPacking 17`** — F1's cardinality, on real `ℤ[√15]` coordinates. -/
noncomputable def packing17 : CongruentPacking 17 :=
  CongruentPacking.ofCongruentDissection Tiling44Bridge.dissection (selEmb le17)

/-- **A genuine `CongruentPacking 38`** — residue `44 − 38 = 6`, the deficiency shape F2 uses. -/
noncomputable def packing38 : CongruentPacking 38 :=
  CongruentPacking.ofCongruentDissection Tiling44Bridge.dissection (selEmb le38)

theorem packing17_target_volume :
    volume packing17.target.carrier = (44 : ℝ≥0∞) * volume packing17.model.carrier :=
  tiling44_volume_target

theorem packing38_target_volume :
    volume packing38.target.carrier = (44 : ℝ≥0∞) * volume packing38.model.carrier :=
  tiling44_volume_target

/-- `card_le` runs on a real object: 17 tiles fit in a 44-tile target. -/
theorem packing17_card_le : (17 : ℕ) ≤ 44 :=
  packing17.card_le 44 packing17_target_volume

/-- `card_le` on the 38-packing. -/
theorem packing38_card_le : (38 : ℕ) ≤ 44 :=
  packing38.card_le 44 packing38_target_volume

/-- **The residue-6 identity, geometrically.**  The 38 packed tiles plus six model areas make the
target's area exactly — the geometric counterpart of `LocalCriterionBound.witness_23`'s
`23 − 17 = 6`. -/
theorem packing38_residue :
    ∑ i, volume (packing38.tile i).carrier + (6 : ℝ≥0∞) * volume packing38.model.carrier
      = volume packing38.target.carrier := by
  have h := packing38.residue_volume 44 packing38_target_volume
  norm_num at h
  exact h

/-- **A `Packing` that is not a `Dissection`, exhibited.**  The 38-packing does not cover its
target: it packs `38·|t|` and the target is `44·|t|`, and `covers_iff` turns that area gap into
the failure of covering.  So `Packing` is strictly weaker than `Dissection` — the object is not a
redundant copy. -/
theorem packing38_not_covering :
    (⋃ i, (packing38.tile i).carrier) ≠ packing38.target.carrier := by
  intro hcov
  have hsum := (packing38.toPacking.covers_iff).mp hcov
  rw [packing38.volume_sum, packing38_target_volume] at hsum
  have hpos : volume packing38.model.carrier ≠ 0 := ne_of_gt packing38.model.volume_pos
  have htop : volume packing38.model.carrier ≠ ⊤ := packing38.model.volume_ne_top
  have : (38 : ℝ≥0∞) = (44 : ℝ≥0∞) := by
    exact (ENNReal.mul_left_inj hpos htop).mp hsum
  norm_num at this

/-! ### `restrictOfCount` is non-vacuous

CLAUDE.md's standing rule: exhibit a witness for every hypothesis.  `restrictOfCount`'s two
hypotheses are jointly satisfiable — `S = univ`, `T` = the dissection's own target.  This is the
*trivial* instance (it returns the 44-tiling itself); it settles satisfiability, and it is not a
claim that a proper sub-triangle of the 44-tiling has been exhibited.  Finding a proper `S` whose
union is a triangle is a coordinate search, and is the next step for a real application. -/

theorem tile_subset_target {N : ℕ} (D : Dissection N) (i : Fin N) :
    (D.tile i).carrier ⊆ D.target.carrier := by
  intro x hx
  rw [← D.covers]
  exact Set.mem_iUnion_of_mem i hx

/-- **The hypotheses of `restrictOfCount` are jointly satisfiable.**  With `S = univ` and `T` the
dissection's own target, both the containment hypothesis and the counting hypothesis hold on the
kernel-checked 44-tiling.  Stated as a proposition rather than built as a term: constructing the
resulting `CongruentDissection` forces the kernel to reduce `Finset.univ.card` over
`Fin Tiling44.tiles.length` inside a 44-piece certificate and times out, which is a cost fact
about the certificate, not a gap in the statement. -/
theorem restrictOfCount_satisfiable :
    (∀ i ∈ (Finset.univ : Finset (Fin Tiling44.tiles.length)),
        (Tiling44Bridge.dissection.tile i).carrier
          ⊆ Tiling44Bridge.dissection.target.carrier) ∧
      volume Tiling44Bridge.dissection.target.carrier
        = ((Finset.univ : Finset (Fin Tiling44.tiles.length)).card : ℝ≥0∞)
          * volume Tiling44Bridge.dissection.model.carrier := by
  refine ⟨fun i _ => tile_subset_target Tiling44Bridge.dissection.toDissection i, ?_⟩
  have h := Erdos634.CongruentArea.congruentDissection_volume_target Tiling44Bridge.dissection
  rw [h, Finset.card_univ, Fintype.card_fin]

end Erdos634.TPHales
