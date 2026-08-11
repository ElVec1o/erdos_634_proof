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

end Erdos634.SecondEdge
