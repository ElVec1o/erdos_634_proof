-- SecondEdge.lean — the angular bookkeeping behind `thm:secondc`: the second edge of an equal side,
-- counted from the apex, is a `c`.
--
-- `ApexRigidity.lean` supplies the metric half (the apex identities, the exact covering of the first
-- chord, and `2γ = π + α`). This file supplies the combinatorial half, which the companion carries as
-- prose: given the angular order at the first junction `J`, the tile standing against the *descending*
-- side presents `α`, and an `α` cannot lay an `a`-edge — so the side edge below `J` is `b` or `c`, and
-- since an equal side carries no `b`, it is a `c`.
--
-- SCOPE. What is NOT proved here is that the vertex figure at `J` is one of the two straight figures
-- (that is `lem:anglecalc`, already in the corpus), nor that `T₁` presents `β` and the tile below its
-- `a`-edge presents `β` or `γ` (that is the metric input, `ApexRigidity`). Those enter as hypotheses.
-- What IS proved is that they force the last position to be an `α`, by exhausting every angular order.
--
-- Per the project rule the corpus was surveyed first: `Walls13.lean` already defines `Edge`, `Angle`,
-- `opposite`, `flanks` and proves `alpha_cannot_lay_a`; this file imports them rather than restating.

import Erdos634.Walls13

namespace Erdos634.SecondEdge

open Erdos634.Walls13

/-- All six orderings of the straight figure `{α,β,γ}`. -/
def ordersABG : List (List Angle) :=
  [[.alpha, .beta, .gamma], [.alpha, .gamma, .beta], [.beta, .alpha, .gamma],
   [.beta, .gamma, .alpha], [.gamma, .alpha, .beta], [.gamma, .beta, .alpha]]

/-- All ten distinct orderings of the straight figure `{3α,2β}`. -/
def ordersAAABB : List (List Angle) :=
  [[.beta, .beta, .alpha, .alpha, .alpha], [.beta, .alpha, .beta, .alpha, .alpha],
   [.beta, .alpha, .alpha, .beta, .alpha], [.beta, .alpha, .alpha, .alpha, .beta],
   [.alpha, .beta, .beta, .alpha, .alpha], [.alpha, .beta, .alpha, .beta, .alpha],
   [.alpha, .beta, .alpha, .alpha, .beta], [.alpha, .alpha, .beta, .beta, .alpha],
   [.alpha, .alpha, .beta, .alpha, .beta], [.alpha, .alpha, .alpha, .beta, .beta]]

/-- The lists really are orderings of the two straight figures: the angle counts are right. -/
theorem orders_have_right_counts :
    ordersABG.all (fun L => L.count Angle.alpha == 1 && L.count Angle.beta == 1
        && L.count Angle.gamma == 1) = true
  ∧ ordersAAABB.all (fun L => L.count Angle.alpha == 3 && L.count Angle.beta == 2
        && L.count Angle.gamma == 0) = true := by
  constructor <;> decide

/-- The admissible angular orders at the first junction: the apex `c`-tile stands first and presents
`β`; the tile below its `a`-edge stands second and presents `β` or `γ` — never `α`, by
`Walls13.alpha_cannot_lay_a`, since that tile lays an `a`-edge. -/
def admissible (L : List Angle) : Bool :=
  (L.head? == some Angle.beta) && ((L[1]? == some Angle.beta) || (L[1]? == some Angle.gamma))

/-- **Every admissible order ends in `α`.**  Exhaustive over all sixteen orderings of the two straight
figures.  This is the step the companion's proof of `thm:secondc` performs in prose. -/
theorem admissible_ends_alpha :
    ((ordersABG ++ ordersAAABB).filter admissible).all
      (fun L => L.getLast? == some Angle.alpha) = true := by
  decide

/-- Exactly two orders are admissible, one in each figure — so the statement above is not vacuous. -/
theorem admissible_exactly_two :
    (ordersABG ++ ordersAAABB).filter admissible
      = [[.beta, .gamma, .alpha], [.beta, .beta, .alpha, .alpha, .alpha]] := by
  decide

/-- **An `α` at a boundary point lays `b` or `c`.**  Restating `Walls13.alpha_cannot_lay_a` in the
positive form the side argument consumes. -/
theorem alpha_lays_b_or_c {E : Edge}
    (hlay : E = (flanks Angle.alpha).1 ∨ E = (flanks Angle.alpha).2) :
    E = Edge.b ∨ E = Edge.c := by
  rcases hlay with h | h
  · left; simpa [flanks] using h
  · right; simpa [flanks] using h

/-- **The second edge of an equal side is a `c`.**  The tile against the descending side presents `α`
(`admissible_ends_alpha`), so it lays `b` or `c` there; an equal side carries no `b`
(`lem:sidenob`), hence `c`. -/
theorem second_edge_is_c {E : Edge}
    (hlay : E = (flanks Angle.alpha).1 ∨ E = (flanks Angle.alpha).2)
    (hnob : E ≠ Edge.b) : E = Edge.c := by
  rcases alpha_lays_b_or_c hlay with h | h
  · exact absurd h hnob
  · exact h

/-- **The count consequence.**  With the apex edge and the edge below the first junction both `c`,
an equal side carries at least two `c`-edges. -/
theorem n_c_ge_two {n_c p e f : ℕ} (hside : n_c + p * e = f) (h2 : 2 ≤ n_c) : p * e + 2 ≤ f := by
  omega


/-! ## An `a`-edge on the side forces a T-junction

The last tile in angular order stands against the descending side and lays the next side edge on one
of its flanks, with `b` excluded because an equal side carries none. Reading that off for each order
shows an `a` is possible only when the *second* tile — the one sharing the chord ray with the
`c`-tile above — presents `α`. Its flanks are then `b` and `c`, both longer than `a = |JW|`, so the
point `W` falls strictly inside its edge. -/

/-- `b` is the one edge an equal side never carries. -/
def notB : Edge → Bool
  | .b => false
  | _  => true

/-- The edges an angle can lay on an equal side: its flanks, with `b` removed. -/
def sideEdges (A : Angle) : List Edge := [(flanks A).1, (flanks A).2].filter notB

/-- An `α` standing against the side can only lay a `c` there. -/
theorem sideEdges_alpha : sideEdges Angle.alpha = [Edge.c] := by decide

/-- `β` can lay `a` or `c`; `γ` can lay only `a`. -/
theorem sideEdges_beta_gamma :
    sideEdges Angle.beta = [Edge.a, Edge.c] ∧ sideEdges Angle.gamma = [Edge.a] := by
  constructor <;> decide

private def isA : Edge → Bool
  | .a => true
  | _  => false

/-- An order permits an `a`-edge below the junction exactly when its last tile can lay one. -/
def permitsA (L : List Angle) : Bool :=
  match L.getLast? with
  | some A => (sideEdges A).any isA
  | none   => false

/-- The `c`-tile above the junction stands first and presents `β` (Proposition `prop:selfsim`). -/
def headBeta (L : List Angle) : Bool := L.head? == some Angle.beta

/-- **Every order permitting an `a` below the junction has `α` in second place.**  Exhaustive over
all sixteen orderings of the two straight figures.  This is the table in the proof of
`thm:aforcesT`. -/
theorem permitsA_forces_alpha :
    ((ordersABG ++ ordersAAABB).filter (fun L => headBeta L && permitsA L)).all
      (fun L => L[1]? == some Angle.alpha) = true := by
  decide

/-- Exactly two orders permit an `a`, and both have `α` second — so the theorem is not vacuous. -/
theorem permitsA_exactly_two :
    (ordersABG ++ ordersAAABB).filter (fun L => headBeta L && permitsA L)
      = [[.beta, .alpha, .gamma], [.beta, .alpha, .alpha, .alpha, .beta]] := by
  decide

/-- **The T-junction.**  The second tile presents `α`, so the edge it lays along the chord ray is a
`b` or a `c`; with `a < b < c` — the hypothesis `e² + ef < f²` of `thm:aforcesT` — that edge is
strictly longer than `a = |JW|`, so `W` lies strictly inside it. -/
theorem chord_edge_longer_than_a {E : Edge} {len : Edge → ℕ}
    (hlay : E = (flanks Angle.alpha).1 ∨ E = (flanks Angle.alpha).2)
    (hab : len Edge.a < len Edge.b) (hbc : len Edge.b < len Edge.c) :
    len Edge.a < len E := by
  rcases alpha_lays_b_or_c hlay with h | h <;> subst h <;> omega


/-! ## The vertex at `P`, corrected

The published form of `cor:noTP` claimed no tile has `P` interior to an edge. That is false: the middle
apex tile `T₂` lays `b` on one of the rays it shares with `T₁`, `T₃` and `c` on the other, so exactly
one of `P`, `P'` carries a T-junction. The conclusion survives because `T₂` occupies the *only*
straight slot. The two ingredients are formalized here: a tile presenting `α` at one vertex presents
`β` and `γ` at the others (so `T₂` cannot present `α` at `P`), and the angle budget admits at most one
straight angle beside a `γ`. -/

/-- The angle with a given ordered pair of flanks, when there is one. -/
def angleOfFlanks : Edge → Edge → Option Angle
  | .b, .c => some .alpha
  | .c, .b => some .alpha
  | .a, .c => some .beta
  | .c, .a => some .beta
  | .a, .b => some .gamma
  | .b, .a => some .gamma
  | _, _   => none

/-- `angleOfFlanks` inverts `flanks`. -/
theorem angleOfFlanks_flanks (A : Angle) :
    angleOfFlanks (flanks A).1 (flanks A).2 = some A := by
  cases A <;> decide

/-- **A tile presenting `α` at one vertex presents `β` and `γ` at the other two.**  The side opposite
`α` is `a`, and the other two vertices have flank pairs `{b,a}` and `{c,a}`.

This is what excludes `T₂` presenting `α` at `P`: it would then present `γ` at the apex, contradicting
the apex figure `3α`. -/
theorem other_angles_of_alpha :
    angleOfFlanks (flanks Angle.alpha).1 (opposite Angle.alpha) = some Angle.gamma
  ∧ angleOfFlanks (flanks Angle.alpha).2 (opposite Angle.alpha) = some Angle.beta := by
  constructor <;> decide

/-- No tile presents the same angle at two of its vertices: the three flank pairs are distinct. -/
theorem angles_pairwise_distinct :
    angleOfFlanks Edge.b Edge.c ≠ angleOfFlanks Edge.b Edge.a
  ∧ angleOfFlanks Edge.b Edge.c ≠ angleOfFlanks Edge.c Edge.a
  ∧ angleOfFlanks Edge.b Edge.a ≠ angleOfFlanks Edge.c Edge.a := by
  refine ⟨by decide, by decide, by decide⟩

/-- **At most one straight angle sits beside a `γ`.**  Two `γ`'s and a straight angle total
`2π + α > 2π`; a `γ` and two straight angles total `γ + 2π > 2π`.  So in either configuration at `P`
no further tile can have `P` interior to an edge. -/
theorem at_most_one_straight {al be ga : ℝ} (hal : 0 < al) (hbe : 0 < be)
    (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be) :
    2 * Real.pi < ga + ga + Real.pi ∧ 2 * Real.pi < ga + Real.pi + Real.pi := by
  subst hga
  rw [← hsum]
  constructor <;> linarith

/-- The residual angle at `P` is strictly less than `π` in both configurations: `π − α` when `T₂`
presents `γ`, and `π − γ` when `T₂` is the straight tile. -/
theorem residuals_lt_pi {al be ga : ℝ} (hal : 0 < al) (hbe : 0 < be)
    (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be) :
    2 * Real.pi - (ga + ga) < Real.pi ∧ 2 * Real.pi - (ga + Real.pi) < Real.pi := by
  subst hga
  rw [← hsum]
  constructor <;> linarith


/-- **The `α`-filler cannot stand next to the apex `c`-tile.**  It would lay a `b` or a `c` along that
tile's `a`-ray, both longer than `|JP| = a`, putting `P` interior to its edge and contributing `π`
there; but `P` already carries `γ` from the apex tile and at least `γ` from the middle apex tile,
whose chord trace ends at `P`.  The total is `2γ + π = 2π + α > 2π`.

This is the angle-count form of `thm:lastjunction`, and it shows the enumeration in `thm:ptwodead`
ranges over placements of a tile that cannot be present. -/
theorem filler_excluded {al be ga : ℝ} (hal : 0 < al) (hbe : 0 < be)
    (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be) :
    2 * Real.pi < ga + ga + Real.pi :=
  (at_most_one_straight hal hbe hsum hga).1


/-! ## The budget at `P`, assembled

`cor:noTP` rests on two facts: `T₁` presents `γ` at `P`, and `T₂` either presents `γ` there or has `P`
interior to an edge (contributing `π`). Its conclusion is that no *further* tile can contribute a
straight angle, so the tile below `T₁`'s `a`-edge has a vertex at `P`. That conclusion is an
inequality on the remainder, and it is proved here in both branches at once.

The geometric inputs — that `T₁` presents `γ`, and that `T₂`'s chord trace ends at `P` so that `T₂`
lands in one of the two cases — are hypotheses, in the `ChordInterface` style. -/

/-- **The remainder at `P` is strictly less than `π`, in both branches.**  With `T₁` at `γ` and `T₂`
at `γ` the remainder is `π − α`; with `T₂` straight it is `π − γ`. Neither admits a further straight
angle, so every other tile at `P` has a vertex there. -/
theorem noTP_budget {al be ga t2 rest : ℝ} (hal : 0 < al) (hbe : 0 < be)
    (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be)
    (ht2 : t2 = ga ∨ t2 = Real.pi) (htot : ga + t2 + rest = 2 * Real.pi) :
    rest < Real.pi := by
  subst hga
  rcases ht2 with h | h <;> subst h <;> rw [← hsum] at htot ⊢ <;> linarith

/-- The two branch values of the remainder, for the record: `π − α` and `π − γ`. -/
theorem noTP_remainders {al be ga : ℝ} (hsum : 3 * al + 2 * be = Real.pi) (hga : ga = 2 * al + be) :
    2 * Real.pi - (ga + ga) = Real.pi - al ∧ 2 * Real.pi - (ga + Real.pi) = Real.pi - ga := by
  subst hga
  rw [← hsum]
  constructor <;> ring

/-- **`T₂` cannot present `α` at `P`.**  Its edge towards the apex ends at `P`, at distance `b`, so
that edge is its `b`; an `α` there would put its other flank `c` opposite, making the tile's angle at
the apex the one opposite `c`, namely `γ` — contradicting the apex figure `3α`.  The flank-pair
bookkeeping is `other_angles_of_alpha`. -/
theorem T2_not_alpha_at_P :
    angleOfFlanks (flanks Angle.alpha).1 (opposite Angle.alpha) ≠ some Angle.alpha := by decide

end Erdos634.SecondEdge
