import Erdos634.StraightEdgeSums

/-!
# BentWallCoupling.lean — a bent interior wall couples its two sides, and the coupling is empty

## The question this file answers

`StraightEdgeSums` proves that a **straight** interior edge *decouples*: the fans on its two
sides are each exactly `π` (`HasStraightEdgeSums`, `straight_sums_to_two_pi`), with no term
relating one side to the other.  The 2026-09-10 cross-strip investigation read this as "a straight
shared edge transmits nothing", and asked whether some *non-straight* interior wall might instead
carry a genuine cross-term — a relation between the two sides that could serve as the
frame-absolute base case the reach-4 residue needs.

Two things have to be separated before that question can be answered, and conflating them is the
trap:

* **oblique** = the wall's direction is not the base direction;
* **bent** = the wall's edge chain turns at the vertex, so no straight line through the vertex is
  edge-free there.

**Obliqueness is irrelevant, by construction.**  Nothing in `StraightEdgeSums` refers to a
coordinate axis or a slope: `half_ball_area`, `harea_of_covering`,
`below_angle_sum_of_covering` and `Tri.carrier_subset_halfplane_affine` are all stated for an
*arbitrary* affine functional `g : Plane →ᵃ[ℝ] ℝ` with `g.linear ≠ 0`.  The decoupling is
direction-blind.  In particular the corpus's own oblique interior wall — the **mismatch inner apex
ray** of `thm:pierce` / `thm:align` / `thm:ray` — decouples exactly like the base line.  Indeed
`thm:pierce`(i) *derives* its `(1,1,1)` T-junction figure from the one-sided `π`-sum across a
straight `c`-edge: the mismatch ray is a **consumer** of the decoupling, not a counterexample to
it.  ("Mismatch" there names a disagreement between the two sides' *edge decompositions* —
`{a^{f-e}, c^{f-e}}` against `b^f` — which is combinatorial, not angular.)

**Bending is the real alternative, and it is strictly weaker.**  At a vertex where the chain turns
by a nonzero angle, the two sides are wedges of `θ` and `2π − θ` rather than `π` and `π`.  There is
now formally a shared quantity `θ` occurring in both — a cross-term.  `BentCoupling` below is
exactly that relation.  The two theorems that settle the matter:

* `bent_of_interior_total` — `BentCoupling` follows from the **interior clause of `HasAngleSums`
  alone** (`Dissection.hasAngleSums`, a theorem since 2026-08-16), for *every* interior vertex,
  bent or not, together with nothing but a partition of the tiles by side.  So the cross-term is
  not new information: it is the `2π` total, rewritten.
* `bent_underdetermined` — for *every* `θ` the pair `(θ, 2π − θ)` satisfies `BentCoupling`.  So the
  relation pins neither side.

Against `straight_implies_bent` and `bent_not_implies_straight` this gives the sharp comparison:

>  straight `⟹` bent, strictly.  A straight wall pins each side **absolutely** (`= π`); a bent wall
>  pins only the **sum**, which was already known.  A bend therefore carries strictly *less*
>  information than a straight edge, not more.

## Consequence for the `/goal`

The route "find an oblique/bent interior wall whose vertex figure genuinely couples its two sides,
and read a frame-absolute fact off the cross-term" is closed:

* the *oblique* half is void (the decoupling is direction-blind);
* the *bent* half has a real cross-term, but it is the interior `2π` total and therefore
  location-blind — the turning angle is a relation between two edges **at one vertex**, unchanged
  by relocating that vertex, which is precisely the failure mode `prop:ninetools`' closing
  paragraph names for all nine tool classes;
* and reading the *signed* turn to break that blindness lands in `MirrorGauge`: a signed turning
  angle is mirror-odd, so any criterion built from it is mirror-symmetrisable and falls under
  `mirror_invariant_forces_mixed`, exactly as the 2026-09-10 lateral-drift quantity `(S/2)·Σ εₖ`
  did.

So this reduces to the already-dead **local-angular vertex-census** class (2026-09-09), with the
reduction now proved rather than asserted.  Concretely, the admissible values of `θ` at a tiling
vertex are the `ℕ`-combinations of `α` and `β` that `lem:census` already enumerates, and the
census was already found not to exclude the flip (`π − 2β = 3α > 0`, admissible, published as the
`{3α, 2β}` figure).

Nothing here moves a Rule-0 label.
-/

namespace Erdos634.Geometry

/-- **The coupling a bent interior wall imposes.**  At a vertex where the wall's edge chain turns,
the two sides are wedges summing to the full angle — `θ` on one side, `2π − θ` on the other.  This
is the *entire* relation between the two sides; unlike `HasStraightEdgeSums` it does not fix
either one. -/
def BentCoupling (left right : Plane → ℝ) (V : Set Plane) : Prop :=
  ∀ v ∈ V, left v + right v = 2 * Real.pi

/-- **A straight wall satisfies the bent coupling.**  This is `straight_sums_to_two_pi`, restated:
the straight case is a special case, `θ = π`. -/
theorem straight_implies_bent (above below : Plane → ℝ) (E : Set Plane)
    (h : HasStraightEdgeSums above below E) : BentCoupling above below E :=
  fun v hv => straight_sums_to_two_pi above below E h hv

/-- **The converse fails**, and by an explicit witness: a `2π/3 | 4π/3` bend is coupled but not
straight.  So the implication `straight ⟹ bent` is strict, and the bent hypothesis is genuinely
weaker.  (Rule 2: this also exhibits a satisfying assignment, so `BentCoupling` is not vacuous.) -/
theorem bent_not_implies_straight :
    ∃ (left right : Plane → ℝ) (V : Set Plane),
      BentCoupling left right V ∧ ¬ HasStraightEdgeSums left right V := by
  classical
  refine ⟨fun _ => 2 * Real.pi / 3, fun _ => 4 * Real.pi / 3, Set.univ, ?_, ?_⟩
  · intro v _; ring
  · intro h
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have := (h (0 : Plane) (Set.mem_univ _)).1
    have h3 : 2 * Real.pi / 3 = Real.pi := this
    apply hpi
    linarith

/-- **The coupling determines neither side.**  For every value `θ` there is a bent-coupled pair
whose left wedge is `θ`.  Hence no criterion that reads only the pair `(left v, right v)` at a bent
vertex can pin an absolute value on either side — which is exactly what a frame-absolute base case
would have to do. -/
theorem bent_underdetermined (θ : ℝ) (V : Set Plane) :
    ∃ left right : Plane → ℝ,
      BentCoupling left right V ∧ (∀ v, left v = θ) := by
  refine ⟨fun _ => θ, fun _ => 2 * Real.pi - θ, ?_, fun _ => rfl⟩
  intro v _; ring

/-- **The cross-term is the interior total, nothing more.**  Given any partition of the tiles into
a side `L` and its complement, the interior clause of `HasAngleSums` — a *theorem* since
`Dissection.hasAngleSums` — already yields `BentCoupling` at every interior vertex.  So a bent
wall's two-sided relation is not an extra geometric input: it is `2π`, rewritten.

The hypothesis `hint` is `HasAngleSums`'s first clause, taken as given rather than re-derived, so
that this file states the *implication* and does not silently re-prove `hasAngleSums`. -/
theorem bent_of_interior_total {N : ℕ} (D : Dissection N) (angleAt : Plane → Fin N → ℝ)
    (hint : ∀ v ∈ interior D.target.carrier, ∑ i, angleAt v i = 2 * Real.pi)
    (L : Finset (Fin N)) :
    BentCoupling (fun v => ∑ i ∈ L, angleAt v i) (fun v => ∑ i ∈ Lᶜ, angleAt v i)
      (interior D.target.carrier) := by
  intro v hv
  simpa using (Finset.sum_add_sum_compl L (fun i => angleAt v i)).trans (hint v hv)

/-- **The same statement with the partition hypothesis made explicit as a side-assignment.**  If
every tile is assigned to one of the two sides of the wall, the two side-sums are coupled — again
from the interior total alone. -/
theorem bent_of_side_assignment {N : ℕ} (D : Dissection N) (angleAt : Plane → Fin N → ℝ)
    (hint : ∀ v ∈ interior D.target.carrier, ∑ i, angleAt v i = 2 * Real.pi)
    (side : Fin N → Bool) :
    BentCoupling
      (fun v => ∑ i ∈ (Finset.univ.filter (fun i => side i = true)), angleAt v i)
      (fun v => ∑ i ∈ (Finset.univ.filter (fun i => side i = true))ᶜ, angleAt v i)
      (interior D.target.carrier) :=
  bent_of_interior_total D angleAt hint (Finset.univ.filter (fun i => side i = true))

/-- **Rule 2 control: the interior-total hypothesis is satisfiable.**  The zero angle function on
`N = 0` tiles has an empty interior sum, so the hypothesis of `bent_of_interior_total` is not
`False`; and the conclusion is then the true statement `0 + 0 = 2π` only where the interior is
empty.  Stated with a genuine witness instead: at any `N`, an angle function that is constantly
`2π/N` at interior points satisfies `hint`. -/
theorem interior_total_satisfiable {N : ℕ} (D : Dissection N) (hN : 0 < N) :
    ∃ angleAt : Plane → Fin N → ℝ,
      ∀ v ∈ interior D.target.carrier, ∑ i, angleAt v i = 2 * Real.pi := by
  refine ⟨fun _ _ => 2 * Real.pi / N, fun v _ => ?_⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

/-- **The sharp comparison, in one statement.**  A straight wall fixes each side at `π`; a bent
wall fixes only the sum, and every `θ` is available.  Formally: `HasStraightEdgeSums` implies
`BentCoupling` and additionally pins both sides, while `BentCoupling` alone pins neither. -/
theorem straight_strictly_stronger (above below : Plane → ℝ) (E : Set Plane)
    (h : HasStraightEdgeSums above below E) :
    BentCoupling above below E ∧ (∀ v ∈ E, above v = Real.pi ∧ below v = Real.pi) :=
  ⟨straight_implies_bent above below E h, h⟩

end Erdos634.Geometry
