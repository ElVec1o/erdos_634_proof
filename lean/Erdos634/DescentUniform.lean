import Erdos634.A2BranchRow3
import Erdos634.ApexRigidity
import Erdos634.SecondEdge

/-!
# The descent step is uniform, so `foot_inj` is not a hypothesis

`A2BranchRow3.row_three_dies` carried four descent hypotheses.  One of them, `foot_inj`, is
discharged here, because the project already proves that a descent step is the *same at every
level*.

## What is already proved, and where

`prop:selfsim` ("The descent is self-similar") fixes one descent step exactly, and both of its
metric identities are formalized, generally in `(e, f)`:

* `ApexRigidity.apex_drop_eq` — the drops agree, `b·cos(α/2) = c·cos(3α/2)`, so the far vertex
  lands *on* the next chord rather than above or below it;
* `ApexRigidity.apex_edge_eq` — the horizontal offset is **exactly `a`**:
  `c·sin(3α/2) − b·sin(α/2) = a`, i.e. `f²·(e N₀/2f³) − (f²−e²)·(e/2f) = ef`.

`SecondEdge.selfsim_uniform` then records that the drop from the `k`-th junction to the
`(k+1)`-st does not depend on `k`.  Together: the descent is a translation repeated, with
horizontal step exactly `a`.

Checked numerically at `e = 1`, `f = 3 … 8`: offset `= a` and the two drops agree, to `1e-9`.

## What that gives, and what it does not

A descent with a constant nonzero step sends `i` to `x₀ + i·d`, which is injective — so the
`f + 1` endpoints of the south cover reach `f + 1` **distinct** base slots without that being
assumed.  `row_three_dies_of_uniform` therefore needs only `foot_lt` and `foot_isA`: that the
images land in the base word and are `a`-junctions.

**Not established here:** that the row-3 south-cover descent *is* the descent `prop:selfsim`
governs.  `prop:selfsim` is about junctions along an equal side; the row-3 feet descend through
strips, whose step is `lem:ladder`(i) (`OrderForcing.descent_ident`, also formalized).  Both
descents are uniform, and the skeleton below is stated for *any* uniform step, so it applies to
whichever governs — but identifying which one governs the row-3 feet is open, and is now the
whole of the remaining gap.
-/

namespace Erdos634.DescentUniform

open Finset

/-- **A constant descent step is injective.**  `i ↦ x₀ + i·d` with `d ≥ 1`. -/
theorem progression_inj (x₀ d : ℕ) (hd : 1 ≤ d) (s : Finset ℕ) :
    Set.InjOn (fun i => x₀ + i * d) s := by
  intro i _ j _ h
  simp only at h
  have : i * d = j * d := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

/-- **`prop:selfsim`'s step, in the form the descent uses.**  The horizontal offset between
consecutive junctions is `a = ef`, independent of the level — `ApexRigidity.apex_edge_eq`
supplies the value and `SecondEdge.selfsim_uniform` its independence of the level. -/
theorem step_is_a (e f : ℝ) (hf : f ≠ 0) :
    f ^ 2 * (e * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 3)) - (f ^ 2 - e ^ 2) * (e / (2 * f)) = e * f :=
  Erdos634.ApexRigidity.apex_edge_eq e f hf

/-- **The drops agree**, so the descent lands on the next chord: `ApexRigidity.apex_drop_eq`. -/
theorem drops_agree (e f : ℝ) (hf : f ≠ 0) :
    (f ^ 2 - e ^ 2) * (Real.sqrt (4 * f ^ 2 - e ^ 2) / (2 * f))
      = f ^ 2 * (Real.sqrt (4 * f ^ 2 - e ^ 2) * (f ^ 2 - e ^ 2) / (2 * f ^ 3)) :=
  Erdos634.ApexRigidity.apex_drop_eq e f hf

/-- **`prop:a2branch` at row 3, with `foot_inj` discharged.**

The descent has a constant step `d ≥ 1`, so it is injective and the `f + 1` endpoints of the
south cover land on `f + 1` distinct base slots.  Only two hypotheses remain, and both are about
*where* the images land, not about the descent's shape: they lie in the base word (`foot_lt`)
and are `a`-junctions (`foot_isA`). -/
theorem row_three_dies_of_uniform (f : ℕ) (isA : ℕ → Prop) [DecidablePred isA]
    (base_count : ((range (f + 2)).filter isA).card = f)
    (x₀ d : ℕ) (hd : 1 ≤ d)
    (foot_lt : ∀ i ∈ range (f + 1), x₀ + i * d < f + 2)
    (foot_isA : ∀ i ∈ range (f + 1), isA (x₀ + i * d)) :
    False :=
  Erdos634.A2BranchRow3.row_three_dies f isA base_count (fun i => x₀ + i * d)
    (progression_inj x₀ d hd _) foot_lt foot_isA

end Erdos634.DescentUniform
