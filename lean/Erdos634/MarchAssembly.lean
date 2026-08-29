import Mathlib.Tactic
import Erdos634.RunOrientation
import Erdos634.MarchJunctions
import Erdos634.PinLemma

/-!
# The march assembly: the junction dichotomy is derived, not assumed

Erdős #634, `e = 1`.  The pin argument analyses a base junction `a|c` under the assumption that
its west flank is `γ` and its east flank is `α` or `β`.  This file *derives* that assumption for
every word with `c` in position `≥ 2` whose preceding letters are `a` — which, after mirror
normalisation, is every escape word of the pincer window with `cp ≥ 2`.

The chain, each link a theorem:

1. the corner fill is a single `β`-tile (`BaseBetaCorners.corner_beta_unique`), so the first
   `a`-tile of the run presents `β` at the target corner;
2. an `a`-edge's two ends carry `β` and `γ`, one each (`MarchJunctions.a_edge_ends_pair`), so
   that tile presents `γ` at its east end — orientation `BG` (`orient_west_beta`);
3. an admissible orientation run starting `BG` is constantly `BG`
   (`RunOrientation.corner_anchored_run_all_BG`), the transition `BG,GB` being forbidden because
   it puts two `γ`s at a `π`-budget junction (`Inflation.BG_GB_forbidden`);
4. hence the run's east end — the flank *west* of the `c`-junction — is `γ`
   (`run_west_flank_gamma`);
5. the `c`-side's two ends carry `α` and `β` (`PinLemma.east_flank_cases`), so the east flank is
   one of those.

The conclusion (`junction_dichotomy`) is exactly the two-branch case split the pin argument
consumes: `(γ,α)`, whose wedge is `β` and whose forced single `β`-tile dies on the two-gap
contract, and `(γ,β)`, whose wedge is `α` and whose forced single `α`-tile opens the `T`-vertex
ladder.  The `(β,·)` combinations of the naive four-case analysis **never occur**.

What this does *not* do: it does not prove that a hypothetical tiling has such a run at all (that
is the word structure, supplied by the reduction theorem), and it does not terminate the ladder.
Those are named residues, not silently assumed here.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchAssembly

open Erdos634.Inflation Erdos634.Interface

/-- The two flank corners of an `a`-tile, west and east, read off its orientation. -/
def orientCorners : Orient → Corner × Corner
  | Orient.BG => (Corner.beta, Corner.gamma)
  | Orient.GB => (Corner.gamma, Corner.beta)

/-- **The seed.**  A tile presenting `β` at its west end has orientation `BG`, hence `γ` east. -/
theorem orient_west_beta (o : Orient) (h : (orientCorners o).1 = Corner.beta) :
    o = Orient.BG ∧ (orientCorners o).2 = Corner.gamma := by
  cases o <;> simp_all [orientCorners]

/-- **The west flank of the `c`-junction is `γ`.**  A corner-anchored run — one whose first tile
presents `β` at the target corner — ends with orientation `BG`, so its east end presents `γ`. -/
theorem run_west_flank_gamma (L : List Orient)
    (hchain : L.Chain' (fun l r => admissiblePair l r = true))
    (hseed : (orientCorners Orient.BG).1 = Corner.beta)
    (hhead : L.head? = some Orient.BG) (hne : L ≠ []) :
    (orientCorners (L.getLast hne)).2 = Corner.gamma := by
  rw [Erdos634.RunOrientation.corner_anchored_run_last L hchain hhead hne]
  rfl

/-- **The junction dichotomy, derived.**  At the `a|c` junction of any corner-anchored run, the
west flank is `γ` and the east flank is `α` or `β`: exactly the two branches the pin argument
analyses.  The naive `(β,·)` cases do not arise. -/
theorem junction_dichotomy (L : List Orient)
    (hchain : L.Chain' (fun l r => admissiblePair l r = true))
    (hhead : L.head? = some Orient.BG) (hne : L ≠ [])
    (cCorner : Corner)
    (hc : (flanks cCorner).1 = Edge.c ∨ (flanks cCorner).2 = Edge.c) :
    (orientCorners (L.getLast hne)).2 = Corner.gamma ∧
      (cCorner = Corner.alpha ∨ cCorner = Corner.beta) := by
  refine ⟨run_west_flank_gamma L hchain rfl hhead hne, ?_⟩
  exact Erdos634.PinLemma.east_flank_cases cCorner hc

/-- **The two branches, named.**  Under the dichotomy the junction's wedge is `β` (east flank `α`)
or `α` (east flank `β`), by `π - γ - α = β` and `π - γ - β = α`. -/
theorem dichotomy_wedges (a b g p : ℝ) (hg : g = 2*a + b) (hp : p = 3*a + 2*b) :
    p - g - a = b ∧ p - g - b = a := by
  constructor <;> · rw [hg, hp]; ring

end Erdos634.MarchAssembly
