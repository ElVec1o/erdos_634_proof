import Erdos634.RouteOneApproach
import Erdos634.ChordStraddleTotal
import Erdos634.RouteOneBoundaryA
import Erdos634.NormalPosition

/-!
# `hwall` **is** the crossing question at `V`, and nothing more

Erdős #634 — locating Route 1's last residue inside `prop:threecostumes`.

**What this file settles, and why it is the right thing to settle.**  After the chain
`RouteOneApproach` → `RouteOneWallOnly` → `BaseBetaTargetCoord` → `RouteOneBoundaryA` →
`NormalPosition` (all 2026-09-11), Route 1's flank step at `rem:route1uniform` has exactly one
open hypothesis left, the local wall

    hwall : ∃ ρ > 0, ∀ k,
      (∃ q ∈ (D.tile k).carrier, 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      (∀ q ∈ (D.tile k).carrier, 0 ≤ (q - V) 1)

(`RouteOneApproach.EscapeData.ofInterior_plain`, `RouteOneWallOnly.flank_from_wall_only`,
`RouteOneBoundaryA.flank_at_route1uniform`, `NormalPosition.flank_at_route1uniform_of_congruent`),
tagged `OPEN` in the companion as `rem:routeoneopen`.

`CLAUDE.md` records that "the `e = 1` side and the `e ≥ 2` side are the same wall in different
costumes", and `erdos-634-obstructions.tex`'s `prop:threecostumes` *(iii)* says
`conj:advance` "is the crossing question by construction".  That is a statement about the paper's
informal `def:crossQ`:

> let `S` be a maximal run of forced tiles whose far sides lie along a segment `L` of a line, with
> `V` the endpoint of `L` beyond the run's last forced tile.  Must the next tile along `L` lay a
> whole edge on `L` without overrunning `V`, or can it **cross** `L` at `V`?

This file makes that identification a **theorem** rather than a remark, for the `hwall` residue
specifically, by proving `hwall` equivalent to the "no crossing" alternative stated in the corpus's
own geometric vocabulary for crossing, `ChordTraceReal.straddlers` (a tile with a vertex strictly
below and a vertex strictly above a line).

## The result

`wall_iff_no_straddler` : for any dissection, any `V`, any `ρ`,

    (∀ k, upRightNear k → tile k lies weakly above the line y = V 1)
      ↔  (∀ k, upRightNear k → k ∉ straddlers D yHeight (V 1)).

So `hwall`'s conclusion — which *reads* global ("every point of the tile is weakly above `V`") — is
**exactly** the local non-crossing statement for the tiles its antecedent selects, no stronger and
no weaker.  The bridge is `Tri.sign_trichotomy`: a triangle either lies weakly on one side of a line
or straddles it at the vertices, with no third possibility, so for a tile that *does* reach above
the line, "weakly above" and "does not cross" are the same proposition.

`wall_of_no_straddlers` states the consequence in the form `def:crossQ` is phrased in: if **no**
tile of the dissection crosses the horizontal line through `V`, then `hwall` holds — for every `ρ`,
so the existential radius is free.  `flank_at_route1uniform_of_no_crossing` and
`flank_of_no_crossing_of_congruent` push that through to Route 1's flank conclusion at the
base-`β` configuration, in normal position and up to congruence respectively.

## What this means for the /goal, stated flatly

**It is a negative, and it is the headline.**  Route 1's residue is not a weaker, more local
cousin of the crossing question that the session's new machinery (`ChordChartPlanar`'s interior
tests, `BaseBetaTargetCoord`'s explicit coordinates, `EpredWedgeClearance`'s clearance, `MirrorGauge`)
might reach.  It is the crossing question at `V`, in the corpus's own definition of crossing, with
`ρ` free.  By `prop:ninetools` (`PROVED`) nine tool classes provably cannot answer it, and the
common cause recorded there applies verbatim here: each of those tools computes a quantity invariant
under relocating edges, and `hwall` asks *where* the tiles near `V` lie.

Consequently: **closing `hwall` at `e = 1` is exactly as hard as answering the crossing question at
this `V` — no harder, and no easier.**  That is worth knowing precisely, and it is the reason no
attempt to prove `hwall` is made here.  The three machineries above were checked against it and are
*about different data* — the reason is recorded in `RouteOneApproach.lean`'s closing note
(vertex-figure machinery sees only angles at `V`; clearance sees only distances along the base) and
is unchanged by this file.

## Non-vacuity

Every statement below is either an `↔` with no side hypothesis, or an implication whose antecedent
(`no tile straddles the horizontal line at `V``) is exhibited satisfiable by
`no_crossing_nonvacuous`: the one-tile dissection of a triangle by itself, with `V` its bottom
vertex.  What is **not** established — and cannot be, here — is satisfiability of the full
`flank_at_route1uniform` bundle, which still contains `hwall`.  No base-`β` dissection is exhibited.

## Rule 0.5

`code/novelty_check.sh` on "hwall is the crossing question", "local wall is no straddler",
"hwall equivalent to no straddling tile", "wall hypothesis is an instance of def:crossQ",
"no tile straddles the line at V": no corpus matches.  The ingredients are rediscoveries and are
named as such: `Tri.sign_trichotomy` (`ChordTraceReal.lean`), `straddlers` and
`interior_on_line_straddles` (`ChordStraddleTotal.lean`, `ChordInteriorStraddle.lean`) all predate
this file; `ChordDecompositionNoStraddle.lean` already runs the "no straddler ⇒ wall" direction for
a *different* wall notion (no tile interior meets an open chord).  What is new is the identification
of Route 1's `hwall` with that vocabulary, and the two compositions at the base-`β` configuration.

Axiom-clean beyond the standard three; no `sorry`.
-/

open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.RouteOneCrossing

/-! ## 1. The height functional

`straddlers` is stated for a linear functional; the crossing question at `V` is about the
*horizontal* line through `V`, so the functional is the `y`-coordinate. -/

/-- The `y`-coordinate of a point of the plane, as a linear functional. -/
noncomputable def yHeight : Plane →ₗ[ℝ] ℝ where
  toFun p := p 1
  map_add' p q := by simp [PiLp.add_apply]
  map_smul' c p := by simp [PiLp.smul_apply]

@[simp] theorem yHeight_apply (p : Plane) : yHeight p = p 1 := rfl

theorem yHeight_ne_zero : yHeight ≠ 0 := by
  intro h
  have h1 : yHeight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = 1 := by
    simp [yHeight_apply]
  rw [h] at h1
  simp at h1

/-- A vertex of a triangle lies in its carrier. -/
theorem pts_mem_carrier (T : Tri) (a : Fin 3) : T.pts a ∈ T.carrier :=
  subset_convexHull ℝ _ ⟨a, rfl⟩

/-! ## 2. The antecedent: a tile reaching up-and-right of `V`, nearby

This is `hwall`'s antecedent verbatim. -/

/-- **`hwall`'s antecedent.**  Tile `k` has a point strictly up-and-right of `V`, within `ρ`. -/
def UpRightNear {N : ℕ} (D : Dissection N) (V : Plane) (ρ : ℝ) (k : Fin N) : Prop :=
  ∃ q : Plane, q ∈ (D.tile k).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ

/-- **`hwall`'s conclusion.**  Tile `k` lies weakly above the horizontal line through `V`. -/
def WeaklyAbove {N : ℕ} (D : Dissection N) (V : Plane) (k : Fin N) : Prop :=
  ∀ q : Plane, q ∈ (D.tile k).carrier → 0 ≤ (q - V) 1

/-- **The local wall at `V`**, i.e. `hwall`'s body at a fixed radius. -/
def WallAt {N : ℕ} (D : Dissection N) (V : Plane) (ρ : ℝ) : Prop :=
  ∀ k : Fin N, UpRightNear D V ρ k → WeaklyAbove D V k

/-- **`hwall` itself**, with the existential radius. -/
def Wall {N : ℕ} (D : Dissection N) (V : Plane) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ WallAt D V ρ

/-! ## 3. The single triangle lemma

For a triangle that reaches strictly above a horizontal line, "weakly above" and "does not cross"
are the same proposition.  This is where `Tri.sign_trichotomy` does the work: there is no third
alternative for a triangle and a line. -/

/-- **Weakly above ⟺ does not cross, for a triangle that reaches above.**  The hypothesis `hup`
(some point of the carrier is strictly above the line) is exactly what `hwall`'s antecedent
supplies. -/
theorem above_iff_not_straddle (T : Tri) (V : Plane)
    (hup : ∃ q : Plane, q ∈ T.carrier ∧ 0 < (q - V) 1) :
    (∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - V) 1) ↔
      ¬ ((∃ a, yHeight (T.pts a) < V 1) ∧ (∃ b, V 1 < yHeight (T.pts b))) := by
  constructor
  · rintro habove ⟨⟨a, ha⟩, -⟩
    have := habove (T.pts a) (pts_mem_carrier T a)
    rw [PiLp.sub_apply] at this
    simp only [yHeight_apply] at ha
    linarith
  · intro hns q hq
    rcases Tri.sign_trichotomy T yHeight (V 1) with hle | hge | hstr
    · obtain ⟨z, hz, hzpos⟩ := hup
      have := hle z hz
      simp only [yHeight_apply] at this
      rw [PiLp.sub_apply] at hzpos
      linarith
    · have := hge q hq
      simp only [yHeight_apply] at this
      rw [PiLp.sub_apply]
      linarith
    · exact absurd hstr hns

/-! ## 4. The identification

`hwall` is the crossing question at `V`, verbatim. -/

/-- **`hwall` is exactly "no selected tile crosses the horizontal line at `V`".**

The left side is `hwall`'s body at radius `ρ`; the right side says none of the tiles its antecedent
selects is a straddler of the horizontal line through `V`, in the corpus's own definition of
straddling (`ChordTraceReal.straddlers`: a vertex strictly below and a vertex strictly above).
No hypotheses, both directions. -/
theorem wall_iff_no_straddler {N : ℕ} (D : Dissection N) (V : Plane) (ρ : ℝ) :
    WallAt D V ρ ↔ ∀ k : Fin N, UpRightNear D V ρ k → k ∉ straddlers D yHeight (V 1) := by
  classical
  constructor
  · intro hw k hk hmem
    simp only [straddlers, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have habove := hw k hk
    obtain ⟨q, hq, -, hqy, -⟩ := hk
    exact ((above_iff_not_straddle (D.tile k) V ⟨q, hq, hqy⟩).mp habove) hmem
  · intro hw k hk
    have hk' := hk
    obtain ⟨q, hq, -, hqy, -⟩ := hk
    refine (above_iff_not_straddle (D.tile k) V ⟨q, hq, hqy⟩).mpr ?_
    intro hstr
    refine hw k hk' ?_
    simp only [straddlers, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hstr

/-- **No crossing at all ⇒ `hwall`, at every radius.**  This is the form `def:crossQ` is phrased
in: the crossing question answered negatively at the horizontal line through `V` gives the local
wall outright, with the existential radius free (any positive `ρ` works). -/
theorem wallAt_of_no_straddlers {N : ℕ} (D : Dissection N) (V : Plane)
    (h : ∀ k : Fin N, k ∉ straddlers D yHeight (V 1)) (ρ : ℝ) : WallAt D V ρ :=
  (wall_iff_no_straddler D V ρ).mpr (fun k _ => h k)

/-- `hwall` from the crossing question, existential radius supplied. -/
theorem wall_of_no_straddlers {N : ℕ} (D : Dissection N) (V : Plane)
    (h : ∀ k : Fin N, k ∉ straddlers D yHeight (V 1)) : Wall D V :=
  ⟨1, one_pos, wallAt_of_no_straddlers D V h 1⟩

/-- **The converse restriction.**  `hwall` does *not* give "no tile crosses the line at `V`" for
tiles that never reach up-and-right of `V` — and it need not: those tiles are not "the next tile
along `L`".  Stated so that the exact strength of `hwall` is on the record: it constrains precisely
the tiles `def:crossQ` asks about, and no others. -/
theorem wall_constrains_only_selected {N : ℕ} (D : Dissection N) (V : Plane) (ρ : ℝ)
    (hw : WallAt D V ρ) (k : Fin N) (hk : UpRightNear D V ρ k) :
    k ∉ straddlers D yHeight (V 1) :=
  (wall_iff_no_straddler D V ρ).mp hw k hk

/-! ## 5. Non-vacuity of the antecedent

`no_crossing_nonvacuous`: the hypothesis "no tile crosses the horizontal line through `V`" is
satisfiable — in the trivial dissection of a triangle by itself, at any `V` weakly below every
vertex.  This does **not** claim the full Route 1 bundle is satisfiable; it is not. -/

/-- In a dissection whose every tile has all vertices weakly above the line `y = c`, no tile
straddles.  (The witness for `wallAt_of_no_straddlers`' hypothesis being satisfiable.) -/
theorem no_straddlers_of_all_above {N : ℕ} (D : Dissection N) (c : ℝ)
    (h : ∀ (k : Fin N) (a : Fin 3), c ≤ (D.tile k).pts a 1) (k : Fin N) :
    k ∉ straddlers D yHeight c := by
  classical
  intro hmem
  simp only [straddlers, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨⟨a, ha⟩, -⟩ := hmem
  simp only [yHeight_apply] at ha
  exact absurd (h k a) (not_le.mpr ha)

/-- A triangle dissected by itself. -/
def selfDissection (T : Tri) : Dissection 1 where
  target := T
  tile := fun _ => T
  covers := Set.iUnion_const _
  interiors_disjoint := by intro i j hij; exact absurd (Subsingleton.elim i j) hij

/-- **The crossing question's negative answer is satisfiable.**  For any triangle `T`, dissected by
itself, no tile straddles the horizontal line at the level of `T`'s lowest vertex; hence `Wall`
holds there.  So `wallAt_of_no_straddlers` and `flank_at_route1uniform_of_no_crossing` are not
implications from an unsatisfiable hypothesis.

This says nothing about the *full* Route 1 bundle, which also carries the `α`-tile data and the
base-`β` target; that bundle's satisfiability is not established anywhere, and cannot be, since it
is exactly what a proof of `conj:advance` would refute. -/
theorem no_crossing_nonvacuous (T : Tri) :
    ∀ k : Fin 1,
      k ∉ straddlers (selfDissection T) yHeight (min (min (T.pts 0 1) (T.pts 1 1)) (T.pts 2 1)) := by
  refine no_straddlers_of_all_above (selfDissection T) _ ?_
  intro k a
  fin_cases a <;>
    simp only [selfDissection] <;>
    first
      | exact le_trans (min_le_left _ _) (min_le_left _ _)
      | exact le_trans (min_le_left _ _) (min_le_right _ _)
      | exact min_le_right _ _

/-! ## 6. The compositions at the base-`β` configuration

Route 1's flank conclusion at `rem:route1uniform`, from the crossing question answered negatively
instead of from `hwall`.  These are the statements that make the reduction consumable: whoever
answers the crossing question at `V` gets the flank, with nothing else to supply. -/

open Erdos634.CertCoord Erdos634.BaseBetaTargetCoord

/-- **Route 1's flank at `rem:route1uniform`, in normal position, from no crossing at `V`.**
Replaces `RouteOneBoundaryA.flank_at_route1uniform`'s `hwall` by the crossing question's negative
answer at the horizontal line through `V`.  Everything else is unchanged; in particular the
`α`-tile bundle is still assumed and still witnessed only at `Tri` level. -/
theorem flank_at_route1uniform_of_no_crossing {N : ℕ} (D : Dissection N) {e f : ℝ}
    (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f)
    (htgt : D.target = baseBetaTarget e f (by linarith) hef)
    (j : Fin N) (mj : Fin 3)
    (hjseg : openSegment ℝ (mkPt (escapeV e f).1 (escapeV e f).2)
        (mkPt (sideA e f).1 (sideA e f).2)
      ⊆ openSegment ℝ ((D.tile j).pts (mj + 1)) ((D.tile j).pts (mj + 2)))
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier →
      0 ≤ (q - mkPt (escapeV e f).1 (escapeV e f).2) 1)
    (hjleft : ∀ q : Plane, q ∈ (D.tile j).carrier →
      (q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ≤ 0)
    (hcross : ∀ k : Fin N,
      k ∉ straddlers D yHeight ((mkPt (escapeV e f).1 (escapeV e f).2) 1)) :
    ∃ (i : Fin N) (m : Fin 3),
      (D.tile i).pts m = mkPt (escapeV e f).1 (escapeV e f).2 ∧
      (((D.tile i).pts (m + 1) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < ((D.tile i).pts (m + 1) - mkPt (escapeV e f).1 (escapeV e f).2) 0 ∨
        ((D.tile i).pts (m + 2) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < ((D.tile i).pts (m + 2) - mkPt (escapeV e f).1 (escapeV e f).2) 0) :=
  Erdos634.RouteOneBoundaryA.flank_at_route1uniform D he hef hf2 htgt j mj hjseg habovej hjleft
    (wall_of_no_straddlers D (mkPt (escapeV e f).1 (escapeV e f).2) hcross)

/-! ### The congruent-target form

`NormalPosition.flank_at_route1uniform_of_congruent` states `hwall` *through* the congruence's
isometry `g`.  The identification survives the transport: the relevant triangle is
`mapTri (isoAff g) (D.tile k)`, whose vertices are `g` of `D`'s and whose carrier is `g '' `carrier.
So the crossing question is asked of `D`'s tiles **as `g` places them**, which is the geometrically
correct reading — `V` is a point of the model. -/

open Erdos634.DissectionMap Erdos634.Ladder in
/-- **`hwall` through a congruence, from no crossing of the placed tiles.** -/
theorem wall_through_isometry_of_no_crossing {N : ℕ} (D : Dissection N) (g : Plane ≃ᵢ Plane)
    (V : Plane)
    (hcross : ∀ k : Fin N,
      ¬ ((∃ a, yHeight (g ((D.tile k).pts a)) < V 1) ∧
         (∃ b, V 1 < yHeight (g ((D.tile k).pts b))))) (ρ : ℝ) :
    ∀ k : Fin N,
      (∃ q : Plane, q ∈ (D.tile k).carrier ∧
        0 < (g q - V) 0 ∧ 0 < (g q - V) 1 ∧ dist (g q) V < ρ) →
      ∀ q : Plane, q ∈ (D.tile k).carrier → 0 ≤ (g q - V) 1 := by
  intro k hk q hq
  obtain ⟨z, hz, -, hzy, -⟩ := hk
  have hmem : ∀ w : Plane, w ∈ (D.tile k).carrier →
      g w ∈ (mapTri (isoAff g) (D.tile k)).carrier := by
    intro w hw
    rw [mapTri_carrier, isoAff_coe]
    exact ⟨w, hw, rfl⟩
  have hup : ∃ p : Plane, p ∈ (mapTri (isoAff g) (D.tile k)).carrier ∧ 0 < (p - V) 1 :=
    ⟨g z, hmem z hz, hzy⟩
  refine (above_iff_not_straddle (mapTri (isoAff g) (D.tile k)) V hup).mpr ?_
    (g q) (hmem q hq)
  simpa [mapTri, isoAff_coe] using hcross k

open Erdos634.CertCoord Erdos634.BaseBetaTargetCoord in
/-- **Route 1's flank at `rem:route1uniform`, up to congruence, from no crossing at `V`.**
`NormalPosition.flank_at_route1uniform_of_congruent` with `hwall` replaced by the crossing
question's negative answer at the horizontal line through `V`, asked of the tiles as `g` places
them. -/
theorem flank_of_no_crossing_of_congruent {N : ℕ} (D : Dissection N) {e f : ℝ}
    (he : 1 ≤ e) (hef : e < f) (hf2 : 2 ≤ f)
    (g : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3))
    (hg : ∀ k, g (D.target.pts k) = (baseBetaTarget e f (by linarith) hef).pts (σ k))
    (j : Fin N) (mj : Fin 3)
    (hjseg : openSegment ℝ (mkPt (escapeV e f).1 (escapeV e f).2)
        (mkPt (sideA e f).1 (sideA e f).2)
      ⊆ openSegment ℝ (g ((D.tile j).pts (mj + 1))) (g ((D.tile j).pts (mj + 2))))
    (habovej : ∀ q : Plane, q ∈ (D.tile j).carrier →
      0 ≤ (g q - mkPt (escapeV e f).1 (escapeV e f).2) 1)
    (hjleft : ∀ q : Plane, q ∈ (D.tile j).carrier →
      (g q - mkPt (escapeV e f).1 (escapeV e f).2) 0 ≤ 0)
    (hcross : ∀ k : Fin N,
      ¬ ((∃ a, yHeight (g ((D.tile k).pts a)) < (mkPt (escapeV e f).1 (escapeV e f).2) 1) ∧
         (∃ b, (mkPt (escapeV e f).1 (escapeV e f).2) 1 < yHeight (g ((D.tile k).pts b))))) :
    ∃ (i : Fin N) (m : Fin 3),
      g ((D.tile i).pts m) = mkPt (escapeV e f).1 (escapeV e f).2 ∧
      ((g ((D.tile i).pts (m + 1)) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < (g ((D.tile i).pts (m + 1)) - mkPt (escapeV e f).1 (escapeV e f).2) 0 ∨
        (g ((D.tile i).pts (m + 2)) - mkPt (escapeV e f).1 (escapeV e f).2) 1 = 0 ∧
          0 < (g ((D.tile i).pts (m + 2)) - mkPt (escapeV e f).1 (escapeV e f).2) 0) :=
  Erdos634.NormalPosition.flank_at_route1uniform_of_congruent D he hef hf2 g σ hg j mj hjseg
    habovej hjleft
    ⟨1, one_pos, wall_through_isometry_of_no_crossing D g _ hcross 1⟩

/-! ## 7. Axiom audit -/

#print axioms above_iff_not_straddle
#print axioms wall_iff_no_straddler
#print axioms wall_of_no_straddlers
#print axioms no_crossing_nonvacuous
#print axioms flank_at_route1uniform_of_no_crossing
#print axioms wall_through_isometry_of_no_crossing
#print axioms flank_of_no_crossing_of_congruent

end Erdos634.RouteOneCrossing
