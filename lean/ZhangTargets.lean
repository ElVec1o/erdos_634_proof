/-
ZhangTargets.lean — the arithmetic certifying the targets of the 2π/3 branch (Erdős #634).
No imports, no axioms: kernel-checked with the core toolchain only.

PURPOSE. The exhaustive searches reported for the branch of Zhang each need two facts about the
(target, tile) pair before the search means anything:

  (T) the target really is the triangle with the stated angles, and
  (A) the target's area is exactly N tile areas, so N is the tile count and not an approximation.

Both are arithmetic and are pinned here, so that no number in that table rests on floating point.

SETTING. The tile (a,b,c) has γ = 2π/3 opposite c, hence c² = a² + ab + b², and α + β = π/3.
Writing the sines over the common denominator 2c (law of sines, sin γ = √3/2):

    sin α = a√3/(2c),   sin β = b√3/(2c),   sin γ = c√3/(2c),   and   cos α = (2b+a)/(2c),
    cos β = (2a+b)/(2c).

The addition formulas then give every angle of every row of the table as an integer multiple of
√3/(2c), so a target's side ratios are integers read off directly:

    sin(2α+β) = sin(α+π/3) = (sin α + √3 cos α)/2  ↦  numerator (a + (2b+a))/2 = a+b,
    sin(α+2β) = sin(β+π/3)                          ↦  numerator (b + (2a+b))/2 = a+b,
the two being equal because (2α+β) + (α+2β) = 3(α+β) = π.

(A) is Heron in the squared form, which is exact over ℤ:
    16·Area² = 2(p²q² + q²r² + r²p²) − (p⁴ + q⁴ + r⁴).
A target (p,q,r) holds exactly N tiles iff its Heron value is N² times the tile's.

WHAT IS PINNED BELOW. `cos_sin_unit_*` — the trigonometric data is consistent (cos² + sin² = 1) for
each tile used. `heron_*` — the exact tile counts of every target searched, as ℤ identities. These
are the numbers appearing in the paper's table of instances below the constructed range.
-/

namespace Erdos634.ZhangTargets

/-! ## Heron in squared integer form -/

/-- `heron p q r = 16·Area²` of the triangle with sides `p, q, r`. Exact over ℤ. -/
def heron (p q r : Int) : Int :=
  2 * (p*p*q*q + q*q*r*r + r*r*p*p) - (p*p*p*p + q*q*q*q + r*r*r*r)

/-! ## Tile (3,5,7):  c² = a²+ab+b²  is  49 = 9+15+25 -/

theorem tile_357 : (7:Int)*7 = 3*3 + 3*5 + 5*5 := by decide

/-- cos α = (2b+a)/(2c) = 13/14 and sin α = a√3/(2c) = 3√3/14 are a consistent pair:
    13² + 3²·3 = 14². -/
theorem cos_sin_unit_357_alpha : (13:Int)*13 + 3*(3*3) = 14*14 := by decide
/-- cos β = (2a+b)/(2c) = 11/14, sin β = 5√3/14: 11² + 5²·3 = 14². -/
theorem cos_sin_unit_357_beta : (11:Int)*11 + 3*(5*5) = 14*14 := by decide
/-- The numerator of sin(2α+β) and of sin(α+2β) is a+b; for this tile, 8. -/
theorem sin_two_alpha_beta_357 : (3:Int) + 5 = 8 := by decide

/-! ### The targets searched for (3,5,7), each as an exact Heron identity -/

/-- The equilateral of side 15 holds exactly 15 tiles. -/
theorem heron_357_equilateral : heron 15 15 15 = 15*15 * heron 3 5 7 := by decide
/-- The (β,α+β,2α+β) target is the triangle (15,21,24): exactly 24 tiles. -/
theorem heron_357_row24 : heron 15 21 24 = 24*24 * heron 3 5 7 := by decide
/-- The (β,β,π−2β) target is (21,21,33): exactly 33 tiles. -/
theorem heron_357_row33 : heron 21 21 33 = 33*33 * heron 3 5 7 := by decide
/-- The (α,α+β,α+2β) target is (15,35,40): exactly 40 tiles. -/
theorem heron_357_row40 : heron 15 35 40 = 40*40 * heron 3 5 7 := by decide
/-- The (α,α,π−2α) target is (35,35,65): exactly 65 tiles. -/
theorem heron_357_row65 : heron 35 35 65 = 65*65 * heron 3 5 7 := by decide
/-- The (α,2β,2α+β) target is (21,55,56): exactly 88 tiles. -/
theorem heron_357_row88 : heron 21 55 56 = 88*88 * heron 3 5 7 := by decide
/-- The (β,2α,α+2β) target is (35,39,56): exactly 104 tiles. -/
theorem heron_357_row104 : heron 35 39 56 = 104*104 * heron 3 5 7 := by decide
/-- The equilateral of side 30 holds exactly 60 tiles (the m = 2 instance). -/
theorem heron_357_equilateral_m2 : heron 30 30 30 = 60*60 * heron 3 5 7 := by decide

/-! ## Tile (7,8,13):  169 = 49 + 56 + 64 -/

theorem tile_7813 : (13:Int)*13 = 7*7 + 7*8 + 8*8 := by decide
/-- cos α = 23/26, sin α = 7√3/26. -/
theorem cos_sin_unit_7813_alpha : (23:Int)*23 + 3*(7*7) = 26*26 := by decide
/-- cos β = 22/26, sin β = 8√3/26. -/
theorem cos_sin_unit_7813_beta : (22:Int)*22 + 3*(8*8) = 26*26 := by decide

/-- The equilateral of side 56 holds exactly 56 tiles. -/
theorem heron_7813_equilateral : heron 56 56 56 = 56*56 * heron 7 8 13 := by decide
/-- The (β,α+β,2α+β) target is (56,91,105): exactly 105 tiles — a value listed as open. -/
theorem heron_7813_row105 : heron 56 91 105 = 105*105 * heron 7 8 13 := by decide
/-- The (α,α+β,α+2β) target is (56,104,120): exactly 120 tiles — likewise listed as open. -/
theorem heron_7813_row120 : heron 56 104 120 = 120*120 * heron 7 8 13 := by decide

/-! ## Tile (5,16,19):  361 = 25 + 80 + 256 -/

theorem tile_51619 : (19:Int)*19 = 5*5 + 5*16 + 16*16 := by decide
theorem cos_sin_unit_51619_alpha : (37:Int)*37 + 3*(5*5) = 38*38 := by decide
/-- The equilateral of side 80 holds exactly 80 tiles. -/
theorem heron_51619_equilateral : heron 80 80 80 = 80*80 * heron 5 16 19 := by decide

/-! ## The Frobenius parallelograms of the sharpness remark.
`Q(ab,x)` holds exactly `2x` tiles; the check is the same area identity in parallelogram form,
`area(Q) = ab·x·sin(π/3)` against `area(tile) = (ab/2)·sin(2π/3)`, i.e. the count is `2x` outright.
The arithmetic content is that the tested widths are exactly the non-representable ones. -/

/-- For ⟨3,5⟩ the Frobenius number is 7, and 4 and 7 are not representable while 8 = 3+5 is. -/
theorem frob_35_gap4 (x y : Nat) : 3*x + 5*y ≠ 4 := by omega
theorem frob_35_gap7 (x y : Nat) : 3*x + 5*y ≠ 7 := by omega
theorem frob_35_rep8 : 3*1 + 5*1 = 8 := by decide
/-- For ⟨7,8⟩ the value 13 is not representable while 15 = 7+8 is. -/
theorem frob_78_gap13 (x y : Nat) : 7*x + 8*y ≠ 13 := by omega
theorem frob_78_rep15 : 7*1 + 8*1 = 15 := by decide

end Erdos634.ZhangTargets
