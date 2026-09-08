import Erdos634.RouteOneVE
import Erdos634.LocalMarchRun
import Erdos634.LocalMarchRunWitness

/-!
# From an `EscapeData` toward a march step: what composes, and what does not

Written 2026-09-09.  `LocalMarchRun` identified the next gap on route 1 as "no `StepDatum`/`Run` is
produced from a hypothetical base-`β` tiling".  This file works that gap and splits it into three
parts, two of which it closes and one of which it pins.

**1. The flank length is pinned (closed here).**  `RouteOne.escape_data_flank` yields, from an
`EscapeData`, a vertex of the serving tile at `V` with a horizontal rightward neighbour; and
`RouteOne.VE_dichotomy_of_flank` turns exactly that shape into `length = f ∨ f < length`, for a
`CongruentDissection` whose model has sides `{f, f²-1, f²}`.  The two were never composed.
`escape_flank_dichotomy` composes them, and `advance_vector` reads off the surviving branch as
`W = V + f • (1,0)`: the advance step of the march, as a vector identity.

**2. `StepDatum`'s foot is orientation-biased (a real defect, repaired here).**
`LocalMarchRun.StepDatum.hfoot` demands `pts (cn V + 1) = V + w`, but every flank theorem in the
corpus concludes a *disjunction* over the neighbours `m + 1` and `m + 2`, and `Tri` carries no
orientation constraint — `Tri.det` may have either sign, and `Tri.leftDir` branches on it, so
reflected tiles genuinely occur in a `CongruentDissection`.  `no_such_corner` exhibits a concrete
`Tri` (a negatively oriented one) with `pts 0 = V`, `pts 2 = V + w` and **no** corner `c` at all
with `pts c = V` and `pts (c+1) = V + w`: for such a tile the `m+2` branch of the flank cannot be
packaged as a `StepDatum` however the geometry comes out.

`StepDatum'` / `Run'` repair this by carrying a per-step offset `off n ∈ {1,2}`.  Everything
`LocalMarchRun` proves without orientation is reproved here for the repaired object:
`entry_injective'`, `length_le_three_mul'`, `contig'`, `ofStep'`, `no_perpetual_march'`, and
`tile_ne_succ'` — the last with a genuinely new case analysis, since with mixed offsets consecutive
steps can also be excluded because the two hops would return to the same corner.

**3. What is still open, stated exactly.**  Producing a `StepDatum'` from a hypothetical base-`β`
tiling needs, at *every* position of the march and not just at `V`:

* `habove` for the tile serving the tangential approach there.  `RouteOneFlankTransfer.flank_propagates`
  transfers everything else along the wall — `habovei` for the *previous* tile is free, because the
  advance is horizontal so heights relative to `V` and to `E` agree — but `habovei'`, that the *new*
  serving tile keeps weakly above the wall line, is not derivable from the corpus.  It is the
  statement that no tile crosses the wall, and the wall here is a line **interior** to the target
  (`EscapeData.hV`), where nothing forbids a tile from straddling it.
* the exclusion of the overshoot branch `f < length`, which is tile-interior blocking and is not a
  theorem anywhere in `lean/`.

Neither is supplied here, and no theorem below assumes either.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RouteOneStepBridge

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RouteOne

/-! ## 1. The flank length -/

/-- **The escape flank, with its length pinned.**  From an `EscapeData` over a congruent dissection
whose model has sides `{f, f²-1, f²}`, the serving tile has `V` as a vertex and a horizontal
rightward neighbour `W` whose displacement is either exactly `f` — the march advance — or strictly
more than `f`, the overshoot.

This is `RouteOne.escape_data_flank` composed with `RouteOne.VE_dichotomy_of_flank`; both existed,
the composition did not. -/
theorem escape_flank_dichotomy {N : ℕ} (D : CongruentDissection N)
    (E : EscapeData D.toDissection) (f : ℝ) (hf : 2 ≤ f)
    (hmodel : ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
                dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) = {f, f ^ 2 - 1, f ^ 2}) :
    ∃ (k : Fin 3) (W : Plane),
      (D.tile E.i).pts k = E.V ∧
      ((D.tile E.i).pts (k + 1) = W ∨ (D.tile E.i).pts (k + 2) = W) ∧
      (W - E.V) 1 = 0 ∧ 0 < (W - E.V) 0 ∧ ((W - E.V) 0 = f ∨ f < (W - E.V) 0) := by
  obtain ⟨k, hk, hflank⟩ := escape_data_flank D.toDissection E
  rcases hflank with ⟨hy, hx⟩ | ⟨hy, hx⟩
  · exact ⟨k, (D.tile E.i).pts (k + 1), hk, Or.inl rfl, hy, hx,
      VE_dichotomy_of_flank D E.i E.V _ k hk (Or.inl rfl) hy hx f hf hmodel⟩
  · exact ⟨k, (D.tile E.i).pts (k + 2), hk, Or.inr rfl, hy, hx,
      VE_dichotomy_of_flank D E.i E.V _ k hk (Or.inr rfl) hy hx f hf hmodel⟩

/-- **The advance, as a vector identity.**  A horizontal displacement of length exactly `f` is
`f • (1,0)` — the fixed step a `StepDatum` needs. -/
theorem advance_vector {V W : Plane} {f : ℝ} (hy : (W - V) 1 = 0) (hlen : (W - V) 0 = f) :
    W = V + f • mkPt 1 0 := by
  have h0 : W 0 - V 0 = f := by simpa only [PiLp.sub_apply] using hlen
  have h1 : W 1 - V 1 = 0 := by simpa only [PiLp.sub_apply] using hy
  ext i
  fin_cases i
  · show W 0 = V 0 + f * (mkPt 1 0) 0
    rw [mkPt_zero]; linarith
  · show W 1 = V 1 + f * (mkPt 1 0) 1
    rw [mkPt_one]; linarith

/-- **The `a`-branch, assembled.**  If the overshoot branch is excluded at `V`, the serving tile has
`V` as a vertex and its horizontal neighbour is exactly `V + f • (1,0)`.  The hypothesis `hno` is
the tile-interior blocking that is *not* proved anywhere in the corpus — it is carried, not
discharged. -/
theorem escape_flank_advance {N : ℕ} (D : CongruentDissection N)
    (E : EscapeData D.toDissection) (f : ℝ) (hf : 2 ≤ f)
    (hmodel : ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
                dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) = {f, f ^ 2 - 1, f ^ 2})
    (hno : ∀ W : Plane, (W - E.V) 1 = 0 → 0 < (W - E.V) 0 →
      ((D.tile E.i).pts 0 = W ∨ (D.tile E.i).pts 1 = W ∨ (D.tile E.i).pts 2 = W) →
      ¬ f < (W - E.V) 0) :
    ∃ (k : Fin 3) (o : Fin 3), (o = 1 ∨ o = 2) ∧
      (D.tile E.i).pts k = E.V ∧ (D.tile E.i).pts (k + o) = E.V + f • mkPt 1 0 := by
  obtain ⟨k, W, hk, hnb, hy, hx, hlen⟩ := escape_flank_dichotomy D E f hf hmodel
  have hW : (D.tile E.i).pts 0 = W ∨ (D.tile E.i).pts 1 = W ∨ (D.tile E.i).pts 2 = W := by
    rcases hnb with h | h
    · revert h; fin_cases k <;> intro h <;> simp_all
    · revert h; fin_cases k <;> intro h <;> simp_all
  have hf0 : (W - E.V) 0 = f := hlen.resolve_right (hno W hy hx hW)
  have hWeq : W = E.V + f • mkPt 1 0 := advance_vector hy hf0
  rcases hnb with h | h
  · exact ⟨k, 1, Or.inl rfl, hk, by rw [h, hWeq]⟩
  · exact ⟨k, 2, Or.inr rfl, hk, by rw [h, hWeq]⟩

/-! ## 2. `StepDatum` is orientation-biased, and the repair -/

/-- A negatively oriented triangle: `(0,0)`, `(0,1)`, `(1,0)`. -/
noncomputable def revTri : Tri :=
  mkTri 0 0 0 1 1 0 (by norm_num [det3])

theorem revTri_pts : revTri.pts = ![mkPt 0 0, mkPt 0 1, mkPt 1 0] := rfl

/-- **`StepDatum`'s foot cannot be met by a reflected tile.**  `revTri` has `pts 0 = (0,0)` and
`pts 2 = (0,0) + (1,0)`, so the flank's `m + 2` branch holds at it — yet there is *no* corner `c`
with `pts c = (0,0)` and `pts (c + 1) = (0,0) + (1,0)`.  `LocalMarchRun.StepDatum.hfoot`, which
demands exactly that, is therefore unsatisfiable for such a tile whatever the geometry does, and the
`m + 2` branch of every flank theorem in the corpus is stranded. -/
theorem no_such_corner :
    revTri.pts 0 = mkPt 0 0 ∧ revTri.pts 2 = mkPt 0 0 + mkPt 1 0 ∧
      ¬ ∃ c : Fin 3, revTri.pts c = mkPt 0 0 ∧ revTri.pts (c + 1) = mkPt 0 0 + mkPt 1 0 := by
  have hsum : mkPt 0 0 + mkPt (1 : ℝ) 0 = mkPt 1 0 := by
    ext i; fin_cases i <;> simp
  refine ⟨rfl, by rw [revTri_pts]; simpa using hsum.symm, ?_⟩
  rintro ⟨c, hc, hc1⟩
  rw [hsum] at hc1
  fin_cases c
  · have := congrArg (fun p : Plane => p 0) hc1
    simp [revTri_pts] at this
  · have := congrArg (fun p : Plane => p 1) hc
    simp [revTri_pts] at this
  · have := congrArg (fun p : Plane => p 0) hc
    simp [revTri_pts] at this

variable {N : ℕ}

open Erdos634.LocalMarchRun in
/-- **A march run without an orientation bias.**  `LocalMarchRun.Run`, with the far endpoint allowed
to be either neighbour of the corner.  `off n` records which. -/
structure Run' (D : Dissection N) (V₀ w : Plane) (L : ℕ) where
  /-- the tile serving at step `n` -/
  tile : Fin L → Fin N
  /-- the corner of that tile sitting at the step's position -/
  corner : Fin L → Fin 3
  /-- which neighbour of that corner carries the step -/
  off : Fin L → Fin 3
  /-- and it is a neighbour -/
  hoff : ∀ n : Fin L, off n = 1 ∨ off n = 2
  /-- the corner is at the position -/
  head : ∀ n : Fin L, (D.tile (tile n)).pts (corner n) = pos V₀ w (n : ℕ)
  /-- and the chosen neighbour is one step along -/
  foot : ∀ n : Fin L, (D.tile (tile n)).pts (corner n + off n) = pos V₀ w ((n : ℕ) + 1)

variable {D : Dissection N} {V₀ w : Plane} {L : ℕ}

open Erdos634.LocalMarchRun in
/-- **Contiguity, by construction** — as for `Run`, and for the same reason. -/
theorem contig' (R : Run' D V₀ w L) (m n : Fin L) (h : (n : ℕ) = (m : ℕ) + 1) :
    (D.tile (R.tile m)).pts (R.corner m + R.off m) = (D.tile (R.tile n)).pts (R.corner n) := by
  rw [R.foot m, R.head n, h]

open Erdos634.LocalMarchRun in
/-- **Entries are pairwise distinct.** -/
theorem entry_injective' (R : Run' D V₀ w L) (hw : w ≠ 0) :
    Function.Injective (fun n : Fin L => (R.tile n, R.corner n)) := by
  intro m n h
  simp only [Prod.mk.injEq] at h
  have hpos : pos V₀ w (m : ℕ) = pos V₀ w (n : ℕ) := by
    rw [← R.head m, ← R.head n, h.1, h.2]
  exact Fin.ext (pos_injective hw hpos)

/-- **A run is short.** -/
theorem length_le_three_mul' (R : Run' D V₀ w L) (hw : w ≠ 0) : L ≤ 3 * N := by
  have := Fintype.card_le_of_injective _ (entry_injective' R hw)
  simpa [Fintype.card_prod, Nat.mul_comm] using this

/-- **The single-step rule, orientation-agnostic.** -/
structure StepDatum' (D : Dissection N) (w : Plane) where
  /-- the positions the march is defined at -/
  S : Set Plane
  /-- the serving tile -/
  tl : Plane → Fin N
  /-- the corner sitting at the position -/
  cn : Plane → Fin 3
  /-- which neighbour carries the step -/
  of : Plane → Fin 3
  /-- and it is a neighbour -/
  hof : ∀ V ∈ S, of V = 1 ∨ of V = 2
  /-- the corner does sit there -/
  hhead : ∀ V ∈ S, (D.tile (tl V)).pts (cn V) = V
  /-- and the chosen neighbour sits one step along -/
  hfoot : ∀ V ∈ S, (D.tile (tl V)).pts (cn V + of V) = V + w
  /-- the march can be continued -/
  hnext : ∀ V ∈ S, V + w ∈ S

open Erdos634.LocalMarchRun in
theorem StepDatum'.pos_mem (A : StepDatum' D w) {V₀ : Plane} (hV : V₀ ∈ A.S) :
    ∀ n : ℕ, pos V₀ w n ∈ A.S := by
  intro n
  induction n with
  | zero => simpa using hV
  | succ k ih => rw [pos_succ]; exact A.hnext _ ih

open Erdos634.LocalMarchRun in
/-- **The run generated by the step rule.** -/
def ofStep' (A : StepDatum' D w) {V₀ : Plane} (hV : V₀ ∈ A.S) (L : ℕ) : Run' D V₀ w L where
  tile n := A.tl (pos V₀ w (n : ℕ))
  corner n := A.cn (pos V₀ w (n : ℕ))
  off n := A.of (pos V₀ w (n : ℕ))
  hoff n := A.hof _ (A.pos_mem hV _)
  head n := A.hhead _ (A.pos_mem hV _)
  foot n := by rw [A.hfoot _ (A.pos_mem hV _), pos_succ]

/-- **No perpetual march**, for the repaired object. -/
theorem no_perpetual_march' (A : StepDatum' D w) (hw : w ≠ 0) (hne : A.S.Nonempty) : False := by
  obtain ⟨V₀, hV⟩ := hne
  have := length_le_three_mul' (ofStep' A hV (3 * N + 1)) hw
  omega

open Erdos634.LocalMarchRun in
/-- **Distinct tiles at consecutive steps**, with mixed offsets.  Two exclusions now, not one: if
the two hops are `1,1` or `2,2` the shared tile would carry three collinear vertices; if they are
`1,2` or `2,1` the second hop returns to the *first* corner, which would put one vertex at two
distinct positions. -/
theorem tile_ne_succ' (R : Run' D V₀ w L) (hw : w ≠ 0) (m n : Fin L) (h : (n : ℕ) = (m : ℕ) + 1) :
    R.tile m ≠ R.tile n := by
  intro hEq
  set T := D.tile (R.tile m) with hT
  have hshare : T.pts (R.corner m + R.off m) = T.pts (R.corner n) := by
    rw [hT, contig' R m n h, hEq]
  have hcn : R.corner m + R.off m = R.corner n := T.indep.injective hshare
  have h0 : T.pts (R.corner m) = pos V₀ w (m : ℕ) := R.head m
  have h1 : T.pts (R.corner m + R.off m) = pos V₀ w ((m : ℕ) + 1) := R.foot m
  have h2 : T.pts (R.corner m + R.off m + R.off n) = pos V₀ w ((m : ℕ) + 2) := by
    rw [hcn, hT, hEq]
    have := R.foot n
    rw [this, h]
  -- displacements from the base corner
  have e1 : T.pts (R.corner m + R.off m) - T.pts (R.corner m) = w := by
    rw [h0, h1, pos_succ]; abel
  have e2 : T.pts (R.corner m + R.off m + R.off n) - T.pts (R.corner m) = (2 : ℝ) • w := by
    rw [h0, h2, pos_add]
    push_cast
    abel
  rcases R.hoff m with hm1 | hm2 <;> rcases R.hoff n with hn1 | hn2
  -- 1,1 : indices are k, k+1, k+2 — collinear
  · rw [hm1] at e1
    rw [hm1, hn1] at e2
    have hidx : R.corner m + 1 + 1 = R.corner m + 2 := by
      have : ∀ c : Fin 3, c + 1 + 1 = c + 2 := by decide
      exact this _
    rw [hidx] at e2
    have hcross : cross (T.pts (R.corner m + 1) - T.pts (R.corner m))
        (T.pts (R.corner m + 2) - T.pts (R.corner m)) = 0 := by
      rw [e1, e2, cross_smul_right, cross_self, mul_zero]
    rw [T.det_cyclic] at hcross
    exact T.det_ne_zero hcross
  -- 1,2 : k + 1 + 2 = k, so the base corner sits at two positions
  · rw [hm1, hn2] at e2
    have hidx : R.corner m + 1 + 2 = R.corner m := by
      have : ∀ c : Fin 3, c + 1 + 2 = c := by decide
      exact this _
    rw [hidx, sub_self] at e2
    have : w = 0 := by
      have h2w : (2 : ℝ) • w = 0 := e2.symm
      rcases smul_eq_zero.mp h2w with h | h
      · norm_num at h
      · exact h
    exact hw this
  -- 2,1 : k + 2 + 1 = k, likewise
  · rw [hm2, hn1] at e2
    have hidx : R.corner m + 2 + 1 = R.corner m := by
      have : ∀ c : Fin 3, c + 2 + 1 = c := by decide
      exact this _
    rw [hidx, sub_self] at e2
    have : w = 0 := by
      have h2w : (2 : ℝ) • w = 0 := e2.symm
      rcases smul_eq_zero.mp h2w with h | h
      · norm_num at h
      · exact h
    exact hw this
  -- 2,2 : indices are k, k+2, k+1 — collinear again, with the cross product reversed
  · rw [hm2] at e1
    rw [hm2, hn2] at e2
    have hidx : R.corner m + 2 + 2 = R.corner m + 1 := by
      have : ∀ c : Fin 3, c + 2 + 2 = c + 1 := by decide
      exact this _
    rw [hidx] at e2
    have hcross : cross (T.pts (R.corner m + 1) - T.pts (R.corner m))
        (T.pts (R.corner m + 2) - T.pts (R.corner m)) = 0 := by
      rw [e1, e2, cross_smul_left, cross_self, mul_zero]
    rw [T.det_cyclic] at hcross
    exact T.det_ne_zero hcross

/-! ## The repaired object is inhabited

Project rule: no conditional without a witness.  `Run'` generalises `Run`, and
`LocalMarchRunWitness.baseRun` — four `a`-edges along the base of the kernel-verified 44-tile
dissection of `(16,16,22)` — is a real `Run`, hence a real `Run'`.  So `entry_injective'`,
`contig'`, `tile_ne_succ'` and `length_le_three_mul'` are about an inhabited structure.

What is *not* inhabited by anything in the corpus is `StepDatum'`: its `hnext` field makes the
domain closed under advancing, and `no_perpetual_march'` proves no such datum exists.  That is the
theorem, not a defect — but it means `march_from_wall`'s hypotheses are jointly unsatisfiable by
design, and its content lies entirely in `hstep` being the *only* thing a tiling must supply. -/

/-- Every `Run` is a `Run'`, with all offsets `1`. -/
def Run'.ofRun (R : Erdos634.LocalMarchRun.Run D V₀ w L) : Run' D V₀ w L where
  tile := R.tile
  corner := R.corner
  off _ := 1
  hoff _ := Or.inl rfl
  head := R.head
  foot n := by simpa using R.foot n

/-- **`Run'` is inhabited by a real run in a kernel-verified dissection.** -/
theorem witness_run' :
    Nonempty (Run' Erdos634.LocalMarchRunWitness.D (mkPt 0 0) (mkPt 16 0) 4) :=
  ⟨Run'.ofRun Erdos634.LocalMarchRunWitness.baseRun⟩

/-! ## 3. The gap that remains, stated as an implication

Everything above is orientation and length bookkeeping.  The two facts that a hypothetical base-`β`
tiling must still supply, and that nothing in `lean/` supplies, are named in `march_from_wall`'s
hypotheses `hstep`: at *every* position of the march there must be a serving tile with a corner
there and a horizontal `a`-neighbour.  Unfolding `RouteOneFlankTransfer.flank_propagates`, that
needs `habove` for the new serving tile (no tile crosses the wall) and the exclusion of the
overshoot branch.  Given it, the march is impossible — which is route 1's conclusion. -/

/-- **Given a uniform step, the escape dies.**  If the march's advance can be taken at every
position of a nonempty set closed under advancing, `no_perpetual_march'` fires.  The hypotheses are
precisely `StepDatum'`'s; they are *not* discharged here, and by design: `hstep` is exactly the
uniform-in-`n` obligation that `RouteOneThroughEdge`'s header records as untouched. -/
theorem march_from_wall (S : Set Plane) (hne : S.Nonempty) (hw : w ≠ 0)
    (tl : Plane → Fin N) (cn of : Plane → Fin 3)
    (hof : ∀ V ∈ S, of V = 1 ∨ of V = 2)
    (hhead : ∀ V ∈ S, (D.tile (tl V)).pts (cn V) = V)
    (hfoot : ∀ V ∈ S, (D.tile (tl V)).pts (cn V + of V) = V + w)
    (hnext : ∀ V ∈ S, V + w ∈ S) : False :=
  no_perpetual_march'
    { S := S, tl := tl, cn := cn, of := of, hof := hof, hhead := hhead, hfoot := hfoot,
      hnext := hnext } hw hne

end Erdos634.RouteOneStepBridge
