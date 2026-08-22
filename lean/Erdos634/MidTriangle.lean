/-
MidTriangle.lean — arithmetic core of the middle-triangle exclusion S4′ (Erdős #634, base-β).
No imports, no axioms: kernel-checked with the core toolchain only (`omega`).

The corner-block architecture reduces the base-β no-go at `m = 1` to the impossibility of a tiling
of the middle triangle `T_mid` with sides `(f·b, f·b, e·b)`, apex angle `α`, base angles `α+β`,
where `(a,b,c) = (ef, f²−e², f²)` and the slant sides are partitioned into whole `b`-edges.
The proof of that impossibility (S4′, research notes 2026-07-25) rests on three arithmetic facts,
kernel-checked here:

1.  `corner_decomp_alphabeta` / `corner_decomp_apex`: writing `β = (π−3α)/2`, `γ = (π+α)/2`,
    a decomposition `p·α + q·β + r·γ` of the corner angle forces
    `α·(coefficient) + π·(coefficient) = 0`; with `α/π` irrational both coefficients vanish,
    giving the two linear systems solved UNIQUELY here: the base corner `α+β` admits only
    `(p,q,r) = (1,1,0)` (one α-tile and one β-tile), the apex `α` only `(1,0,0)`.

2.  `base_walk_forced_*`: the base of `T_mid` (length `e·b`) admits exactly one edge partition:
    `e` whole `b`-edges. (General proof: mod `f` the walk equation forces `f ∣ Q−e`, and
    `Q ≤ e < e+f` forces `Q = e`, hence `P = R = 0`. Instantiated per family member, `omega`.)

3.  `b_ne_a_and_c_*`: `b ∉ {a, c}` — the β-tile's flanking edges can never supply a `b`-edge.
    (General proof: `a = b` needs `e² ≡ 0 (mod f)`, impossible for `gcd(e,f) = 1`, `f ≥ 2`.)

Together: at a base corner of `T_mid` both rays start with `b`-edges owned by the two corner
tiles; the β-tile is flanked by `a` and `c` only — contradiction. Checked for the members
`(e,f) = (1,2), (2,3), (5,6) [N=83], (4,7) [N=131]`.
-/

namespace Erdos634.MidTriangle

/-- Base-corner decomposition: `q + r = 1` and `2p − 3q + r = −1` (the `π`- and `α`-coefficients
of `p·α + q·β + r·γ = α + β`) force `(p,q,r) = (1,1,0)`: one α-tile and one β-tile, nothing else. -/
theorem corner_decomp_alphabeta (p q r : Int)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h1 : q + r = 1) (h2 : 2*p - 3*q + r = -1) :
    p = 1 ∧ q = 1 ∧ r = 0 := by
  refine ⟨by omega, by omega, by omega⟩

/-- Apex decomposition: `q + r = 0` and `2p − 3q + r = 2` force `(p,q,r) = (1,0,0)`:
the apex of `T_mid` holds exactly one tile, by its α-angle, flanked by its `b`- and `c`-edges. -/
theorem corner_decomp_apex (p q r : Int)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h1 : q + r = 0) (h2 : 2*p - 3*q + r = 2) :
    p = 1 ∧ q = 0 ∧ r = 0 := by
  refine ⟨by omega, by omega, by omega⟩

/-! ## The forced base walk of `T_mid`: length `e·b` partitions only as `b^e` -/

/-- `(e,f) = (1,2)`: length `1·3 = 3`; only walk `(0,1,0)`. -/
theorem base_walk_forced_12 (P Q R : Int)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (h : 2*P + 3*Q + 4*R = 3) :
    P = 0 ∧ Q = 1 ∧ R = 0 := by
  refine ⟨by omega, by omega, by omega⟩

/-- `(e,f) = (2,3)`: length `2·5 = 10`; walks of `(6,5,9)`: `10 = 5·2` only
(`6P + 9R = 10` and `6P + 5 + 9R = 10` are impossible). -/
theorem base_walk_forced_23 (P Q R : Int)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (h : 6*P + 5*Q + 9*R = 10) :
    P = 0 ∧ Q = 2 ∧ R = 0 := by
  refine ⟨by omega, by omega, by omega⟩

/-- `(e,f) = (5,6)` (the frontier member `N = 83`): length `5·11 = 55`; only `b^5`. -/
theorem base_walk_forced_56 (P Q R : Int)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (h : 30*P + 11*Q + 36*R = 55) :
    P = 0 ∧ Q = 5 ∧ R = 0 := by
  refine ⟨by omega, by omega, by omega⟩

/-- `(e,f) = (4,7)` (the frontier member `N = 131`): length `4·33 = 132`; only `b^4`
(note `132 = 28 + 33 + 71·?`… checked exhaustively by `omega`). -/
theorem base_walk_forced_47 (P Q R : Int)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (h : 28*P + 33*Q + 49*R = 132) :
    P = 0 ∧ Q = 4 ∧ R = 0 := by
  refine ⟨by omega, by omega, by omega⟩

/-! ## `b ∉ {a, c}`: the β-tile cannot supply a `b`-edge -/

theorem b_ne_a_and_c_12 : (3 : Int) ≠ 2 ∧ (3 : Int) ≠ 4 := ⟨by omega, by omega⟩
theorem b_ne_a_and_c_23 : (5 : Int) ≠ 6 ∧ (5 : Int) ≠ 9 := ⟨by omega, by omega⟩
theorem b_ne_a_and_c_56 : (11 : Int) ≠ 30 ∧ (11 : Int) ≠ 36 := ⟨by omega, by omega⟩
theorem b_ne_a_and_c_47 : (33 : Int) ≠ 28 ∧ (33 : Int) ≠ 49 := ⟨by omega, by omega⟩

end Erdos634.MidTriangle
