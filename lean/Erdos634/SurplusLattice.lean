/-
SurplusLattice.lean — the surplus lattice of line mismatches in base-`β` tilings (Erdős #634).
No imports, no axioms: kernel-checked with the core toolchain only (`omega`, `decide`).

Along any maximal straight segment of a tiling by the base-`β` tile
`(a,b,c) = (ef, f²−e², f²)`, both sides are partitioned into whole tile edges of equal total
length, so the multiset surplus `(dP,dQ,dR)` (a-, b-, c-count differences) satisfies
`a·dP + b·dQ + c·dR = 0`.  The surplus lattice theorem (A13.1) states that the solution set is
exactly the rank-2 lattice
    Λ = ℤ·R_c ⊕ ℤ·R_b2,   R_c = (f, 0, −e),   R_b2 = (f−e, −f, f−e).
`R_c` encodes the relation `e·c = f·a` and `R_b2` the relation `f·b = (f−e)(a+c)`; these are the
only primitive mismatches a segment can carry.  Consequences: a `b`-count mismatch needs at least
`f` surplus `b`-edges on a side, and a pure `a/c` mismatch needs `f` surplus `a`-edges against `e`
surplus `c`-edges — the quantitative inputs of the corner-block induction.

This file kernel-checks the theorem for the family members currently under attack or settled:
`(e,f) = (1,2)` (`N = 11m²`: the member with kernel-verified tilings at `m = 2,3`),
`(2,3)`, `(1,3)`, and the frontier thick members `(5,6)` (`N = 83`), `(4,7)` (`N = 131`).
The statement is uniform; the general `(e,f)` proof (three lines: reduce mod `f`, use
`gcd(e,f) = 1` twice) is in the research notes, and each instance below is that proof with the
Bézout data inlined, discharged by `omega`.  Membership of the two generators, and the identities
`R_b3 = f·R_b2 − (f−e)·R_c` and (for `e = 1` only) `R_b1 = −R_b2 − (f−1)·R_c`, are checked as
well; the impossibility of `j·b = p·a` with `0 < j < f` at `e ≥ 2` — the `e = 1`/`e ≥ 2`
mismatch dichotomy — is checked for `(2,3)` and `(5,6)`.
-/

namespace Erdos634.SurplusLattice

/-! ## (e,f) = (1,2): tile (2,3,4) -/

/-- A13.1 at `(e,f) = (1,2)`: every length-balanced surplus decomposes over
`R_c = (2,0,−1)`, `R_b2 = (1,−2,1)`. -/
theorem lattice_12 (dP dQ dR : Int) (h : 2*dP + 3*dQ + 4*dR = 0) :
    ∃ k s : Int, dP = 2*k + s ∧ dQ = -2*s ∧ dR = -k + s := by
  obtain ⟨t, ht⟩ : ∃ t, dQ = 2*t := ⟨dQ/2, by omega⟩
  exact ⟨-t - dR, -t, by omega, by omega, by omega⟩

/-- Converse: the lattice lies in the length-zero plane (both generators balance). -/
theorem lattice_12_conv (k s : Int) :
    2*(2*k + s) + 3*(-2*s) + 4*(-k + s) = 0 := by omega

/-! ## (e,f) = (1,3): tile (3,8,9) -/

theorem lattice_13 (dP dQ dR : Int) (h : 3*dP + 8*dQ + 9*dR = 0) :
    ∃ k s : Int, dP = 3*k + 2*s ∧ dQ = -3*s ∧ dR = -k + 2*s := by
  obtain ⟨t, ht⟩ : ∃ t, dQ = 3*t := ⟨dQ/3, by omega⟩
  exact ⟨-2*t - dR, -t, by omega, by omega, by omega⟩

theorem lattice_13_conv (k s : Int) :
    3*(3*k + 2*s) + 8*(-3*s) + 9*(-k + 2*s) = 0 := by omega

/-! ## (e,f) = (2,3): tile (6,5,9) -/

theorem lattice_23 (dP dQ dR : Int) (h : 6*dP + 5*dQ + 9*dR = 0) :
    ∃ k s : Int, dP = 3*k + s ∧ dQ = -3*s ∧ dR = -2*k + s := by
  obtain ⟨t, ht⟩ : ∃ t, dQ = 3*t := ⟨dQ/3, by omega⟩
  refine ⟨(dP + t)/3 , -t, by omega, by omega, by omega⟩

theorem lattice_23_conv (k s : Int) :
    6*(3*k + s) + 5*(-3*s) + 9*(-2*k + s) = 0 := by omega

/-! ## (e,f) = (5,6): tile (30,11,36) — the frontier member N = 83 -/

theorem lattice_56 (dP dQ dR : Int) (h : 30*dP + 11*dQ + 36*dR = 0) :
    ∃ k s : Int, dP = 6*k + s ∧ dQ = -6*s ∧ dR = -5*k + s := by
  obtain ⟨t, ht⟩ : ∃ t, dQ = 6*t := ⟨dQ/6, by omega⟩
  refine ⟨(dP + t)/6, -t, by omega, by omega, by omega⟩

theorem lattice_56_conv (k s : Int) :
    30*(6*k + s) + 11*(-6*s) + 36*(-5*k + s) = 0 := by omega

/-! ## (e,f) = (4,7): tile (28,33,49) — the frontier member N = 131 -/

theorem lattice_47 (dP dQ dR : Int) (h : 28*dP + 33*dQ + 49*dR = 0) :
    ∃ k s : Int, dP = 7*k + 3*s ∧ dQ = -7*s ∧ dR = -4*k + 3*s := by
  obtain ⟨t, ht⟩ : ∃ t, dQ = 7*t := ⟨dQ/7, by omega⟩
  refine ⟨(dP + 3*t)/7, -t, by omega, by omega, by omega⟩

theorem lattice_47_conv (k s : Int) :
    28*(7*k + 3*s) + 33*(-7*s) + 49*(-4*k + 3*s) = 0 := by omega

/-! ## The species identities and the e=1 / e≥2 dichotomy -/

/-- `R_b3 = f·R_b2 − (f−e)·R_c` at `(1,2)`: the b-vs-c-only mismatch `f²·b = (f²−e²)·c`
(`4·3 = 3·4`) is not primitive. -/
theorem rb3_composite_12 :
    (0 : Int) = 2*1 - 1*2 ∧ (-4 : Int) = 2*(-2) - 1*0 ∧ (3 : Int) = 2*1 - 1*(-1) := by
  refine ⟨by omega, by omega, by omega⟩

/-- `e = 1` species: `(f²−1)·a = f·b` holds at `(1,2)` (`3·2 = 2·3`). -/
theorem rb1_exists_12 : (2*2 - 1*1)*2 = 2*3 := by decide

/-- Dichotomy at `(2,3)`: no relation `j·b = p·a` with `0 < j < 3` — indeed `3 ∣ j` always
(`5j = 6p ⟹ 6 ∣ 5j ⟹ 6 ∣ j` since `gcd(5,6)=1`; a fortiori `3 ∣ j`). -/
theorem no_short_ba_23 (j p : Int) (h : 5*j = 6*p) : (3 : Int) ∣ j := by
  obtain ⟨t, ht⟩ : ∃ t, j = 6*t := ⟨j/6, by omega⟩
  exact ⟨2*t, by omega⟩

/-- Dichotomy at `(5,6)`: `11j = 30p ⟹ 30 ∣ j`; a fortiori `6 ∣ j` — no b-vs-a-only mismatch
below `f` surplus b-edges. -/
theorem no_short_ba_56 (j p : Int) (h : 11*j = 30*p) : (6 : Int) ∣ j := by
  obtain ⟨t, ht⟩ : ∃ t, j = 30*t := ⟨j/30, by omega⟩
  exact ⟨5*t, by omega⟩

end Erdos634.SurplusLattice
