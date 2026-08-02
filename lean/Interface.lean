/-
Interface.lean — the geometric interface of the forcing chain (Erdős #634), step one of E2.
No imports, no axioms: kernel-checked with the core toolchain only.

WHY THIS FILE EXISTS. The arithmetic of the branch theorems is machine-checked across the corpus,
but each file takes the geometric facts it needs as loose hypotheses, stated slightly differently
from file to file. That makes the true dependency of the main theorem hard to audit, and it is the
reason the theorem carries the label PROVED rather than VERIFIED.

The plan for E2 is NOT to formalize Euclidean dissection theory (Mathlib has none: no
angles-around-a-point, no planar subdivision, no Jordan curve, no Euler formula). It is to name the
finitely many geometric facts the chain consumes, ONCE, as a structure, and then prove chain steps
as theorems taking that structure. The chain then becomes VERIFIED RELATIVE TO the interface, and
what remains for a full formalization is exactly the interface — a short, explicit list rather than
a 48-page argument.

This file defines the interface for the base-β target at scale m and proves the first consumer
against it. It is deliberately minimal: nothing is added to the interface that is not used.

THE FIELDS, and where each comes from in the written proof:
  · `walk_base`, `walk_side` — the boundary of the target is partitioned into whole tile edges,
    so each side carries nonnegative multiplicities (P,Q,R) with P·a + Q·b + R·c equal to its
    length. (Dissection theory; `Dissection.lean` supplies the surrounding measure statements.)
  · `gamma_trap` — every side carries at least one c-edge. (Proved in the written chain from the
    vertex figures: each a- or b-edge tile puts a γ at a junction, no γ sits at a corner, and a
    straight angle admits at most one γ — the last being `AngleArithmetic.gamma_trap`.)
  · `corner_single` — the tile at a base corner is unique and presents flanks in {a,c}.
    (`AngleArithmetic.beta_corner_forced` gives the multiset; the flank statement is geometric.)
-/

namespace Erdos634.Interface

/-- Tile edge labels. -/
inductive Edge | a | b | c
deriving DecidableEq, Repr

/-- **The geometric interface for the base-β target at scale `m`.** All fields are facts the
written forcing chain establishes geometrically and the arithmetic files consume. -/
structure BaseBeta (e f m : Nat) where
  /-- multiplicities of a-, b-, c-edges along the base -/
  P : Nat
  Q : Nat
  R : Nat
  /-- multiplicities along an equal side -/
  P' : Nat
  Q' : Nat
  R' : Nat
  /-- the base walk has the base's length: `P·a + Q·b + R·c = m·Y₁`, with
      `(a,b,c) = (ef, f²−e², f²)` and `Y₁ = e(3f²−e²)` -/
  walk_base : P * (e * f) + Q * (f * f - e * e) + R * (f * f) = m * (e * (3 * f * f - e * e))
  /-- the side walk has the side's length: `P'·a + Q'·b + R'·c = m·X₁`, `X₁ = f³` -/
  walk_side : P' * (e * f) + Q' * (f * f - e * e) + R' * (f * f) = m * (f * f * f)
  /-- γ-trap: every side carries a c-edge -/
  gamma_trap : 1 ≤ R'
  /-- the base corner is a single β-tile, flanked by a and c -/
  corner_flanks : Edge × Edge
  corner_ac : corner_flanks = (Edge.a, Edge.c) ∨ corner_flanks = (Edge.c, Edge.a)
  /-- base b-count: at `m = 1` the base carries exactly `e` b-edges (the `base_b_bound` of the
      written chain, from the corner analysis plus the surplus lattice).

      THE `m = 1` GUARD IS NOT DECORATION. Without it this field is refuted by genuine tilings:
      the kernel-checked `N44B` and `N44C` tilings of `(16,16,22)` (member `(1,2)`, `m = 2`) have
      base walks `a⁴c³a` and `cacccc`, both with `Q = 0 ≠ e = 1`, and the `99`-tiling of
      `(24,24,33)` (`m = 3`) has `Q = 7`. Stated unguarded, the field made `BaseBeta e f m`
      uninhabited for every `m ≥ 2`, so every theorem over it was vacuous there while appearing to
      say something about tilings that demonstrably exist.

      SCOPE CAVEAT (open). Even at `m = 1` the arithmetic derivation
      `BaseBetaWalkArith.base_b_count` carries the side condition `f² > 2ef + e²`, i.e.
      `f/e > 1 + √2`. For thicker members the count is asserted by the written chain but is not
      derived here. -/
  base_b_count : m = 1 → Q = e

/-! ## First consumer: `side_no_b` at m = 1.
The written chain's first structural step is that no equal side carries a b-edge when m = 1. Against
the interface this is arithmetic: reduce the side equation mod f, then use the γ-trap. -/

/-- The side equation forces `f ∣ Q'`: reducing `P'ef + Q'(f²−e²) + R'f² = m f³` modulo `f` leaves
`−Q'e² ≡ 0`, and `gcd(e,f) = 1`. Stated with the divisibility as a hypothesis, since the gcd step
is number theory the core toolchain does not have. -/
theorem side_q_multiple_of_f (e f m : Nat) (D : BaseBeta e f m) (q : Nat) (hq : D.Q' = f * q) :
    D.P' * (e * f) + (f * q) * (f * f - e * e) + D.R' * (f * f) = m * (f * f * f) := by
  rw [← hq]
  exact D.walk_side

/-- **`side_no_b` at m = 1, member (1,2).** With `e = 1, f = 2` the side equation and the γ-trap
leave no room for a b-edge: `P'·2 + Q'·3 + R'·4 = 8` with `R' ≥ 1` forces `Q' = 0`. -/
theorem side_no_b_1_2 (D : BaseBeta 1 2 1) : D.Q' = 0 := by
  have h := D.walk_side
  have hr := D.gamma_trap
  simp at h
  omega

/-- The same at member (1,3): `P'·3 + Q'·8 + R'·9 = 27` with `R' ≥ 1` forces `Q' = 0`. -/
theorem side_no_b_1_3 (D : BaseBeta 1 3 1) : D.Q' = 0 := by
  have h := D.walk_side
  have hr := D.gamma_trap
  simp at h
  omega

/-- And at (1,4): `P'·4 + Q'·15 + R'·16 = 64`, `R' ≥ 1` forces `Q' = 0`. -/
theorem side_no_b_1_4 (D : BaseBeta 1 4 1) : D.Q' = 0 := by
  have h := D.walk_side
  have hr := D.gamma_trap
  simp at h
  omega

/-! ## Second consumer: the base-walk trichotomy.
With `Q = e` supplied by the interface, the base equation `P·ef + e(f²−e²) + R·f² = e(3f²−e²)`
reduces to `P·e + R·f = 2ef`. Coprimality then forces `e ∣ R`, say `R = e·k`, whence
`P = f(2−k)` and `k ≤ 2`: exactly the three walks `(2f,e,0)`, `(f,e,e)`, `(0,e,2e)` of the written
chain. Below, the reduced equation and the enumeration, per member. -/

/-- The reduction: from the base walk with `Q = e`, the pair `(P,R)` satisfies `P·e + R·f = 2ef`.
Member (1,2): `P·1 + R·2 = 4`. -/
theorem base_reduced_1_2 (D : BaseBeta 1 2 1) : D.P * 2 + D.R * 4 = 8 := by
  have h := D.walk_base
  have hq := D.base_b_count rfl
  simp [hq] at h
  omega

/-- **The trichotomy at (1,2).** `P·2 + R·4 = 8` with `P,R ≥ 0` has exactly the three solutions
`(4,0)`, `(2,1)`, `(0,2)` — the walks `(2f,e,0)`, `(f,e,e)`, `(0,e,2e)`. -/
theorem base_trichotomy_1_2 (D : BaseBeta 1 2 1) :
    (D.P = 4 ∧ D.R = 0) ∨ (D.P = 2 ∧ D.R = 1) ∨ (D.P = 0 ∧ D.R = 2) := by
  have h := base_reduced_1_2 D
  omega

/-- Member (1,3): the base equation reduces to `P·3 + R·9 = 18`, i.e. `P + 3R = 6`, with the three
solutions `(6,0)`, `(3,1)`, `(0,2)`. -/
theorem base_trichotomy_1_3 (D : BaseBeta 1 3 1) :
    (D.P = 6 ∧ D.R = 0) ∨ (D.P = 3 ∧ D.R = 1) ∨ (D.P = 0 ∧ D.R = 2) := by
  have h := D.walk_base
  have hq := D.base_b_count rfl
  simp [hq] at h
  omega

/-- Member (1,4): `P·4 + R·16 = 32`, solutions `(8,0)`, `(4,1)`, `(0,2)`. -/
theorem base_trichotomy_1_4 (D : BaseBeta 1 4 1) :
    (D.P = 8 ∧ D.R = 0) ∨ (D.P = 4 ∧ D.R = 1) ∨ (D.P = 0 ∧ D.R = 2) := by
  have h := D.walk_base
  have hq := D.base_b_count rfl
  simp [hq] at h
  omega

/-! ## Third consumer: the partner lemma (S2).
The corner tile's b-edge is a boundary-anchored chord; the far side of that chord is partitioned
into whole tile edges of total length b, so `x·a + y·b + z·c = b`. Reducing mod f gives
`(y−1)e² ≡ 0`, hence `f ∣ y−1` by coprimality, and size forbids `y ≥ 1+f`; so `y = 1` and then
`x·a + z·c = 0` forces `x = z = 0`. The far side is a single b-edge, which is what makes the
partner a parallelogram rather than a kite. Per member: -/

/-- (1,2): `2x + 3y + 4z = 3` has only `(0,1,0)`. -/
theorem partner_unique_1_2 (x y z : Nat) (h : x * 2 + y * 3 + z * 4 = 3) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega
/-- (1,3): `3x + 8y + 9z = 8` has only `(0,1,0)`. -/
theorem partner_unique_1_3 (x y z : Nat) (h : x * 3 + y * 8 + z * 9 = 8) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega
/-- (1,4): `4x + 15y + 16z = 15` has only `(0,1,0)`. -/
theorem partner_unique_1_4 (x y z : Nat) (h : x * 4 + y * 15 + z * 16 = 15) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega
/-- (2,3): `6x + 5y + 9z = 5` has only `(0,1,0)`. -/
theorem partner_unique_2_3 (x y z : Nat) (h : x * 6 + y * 5 + z * 9 = 5) :
    x = 0 ∧ y = 1 ∧ z = 0 := by omega

/-! ## Fourth consumer: the kite kill.
Of the two congruent mates across the chord, the reflected one repeats the corner angle and
overflows, because `2γ = π + α > π`. In the (α,β) coordinates of `AngleArithmetic`
(α ↦ (1,0), β ↦ (0,1), γ = 2α+β ↦ (2,1), π = 3α+2β ↦ (3,2)) this is the statement that
`2·(2,1) − (3,2) = (1,0)`, i.e. the excess is exactly one α. -/

/-- `2γ − π = α`: doubling the γ-corner overshoots a straight angle by exactly α, so the reflected
mate cannot be placed. -/
theorem kite_overflow : (2*2 - 3 : Int) = 1 ∧ (2*1 - 2 : Int) = 0 := by decide

/-- Consequently no vertex figure contains two γ-corners on a straight angle: `x + 2·2 = 3` is
already unsolvable in ℕ. -/
theorem no_two_gamma (x y : Nat) : ¬ (x + 2*2 = 3 ∧ y + 2*2 = 2) := by omega

/-! ## Fifth consumer: the surplus lattice (S3).
Along a chord, the two sides may subdivide differently; the mismatch multiset lies in the lattice
    Λ = ℤ·(f, 0, −e) ⊕ ℤ·(f−e, −f, f−e)
of `(dP, dQ, dR)` displacements. Reading off the middle coordinate, every element of Λ has
`dQ = −t·f`, so **f divides dQ**, and a mismatch with `0 < |dQ| < f` is impossible. That is the
step which makes the strips match b-for-b. -/

/-- Membership in the surplus lattice: `(dP,dQ,dR) = s·(f,0,−e) + t·(f−e,−f,f−e)`. Reading the
middle coordinate, `dQ = −t·f`. -/
theorem surplus_middle (f t : Int) : t * (-f) = -(t * f) := Int.mul_neg t f

/-- **No small mismatch.** If `dQ` lies in the lattice and `|dQ| < f` then `dQ = 0`: the two sides
of a chord carry the same number of b-edges. -/
theorem no_small_mismatch (f t dQ : Int) (hf : 0 < f) (h : dQ = -(t * f))
    (hlt : dQ < f) (hgt : -f < dQ) : dQ = 0 := by
  by_cases ht1 : 1 ≤ t
  · have hb : 1 * f ≤ t * f := Int.mul_le_mul_of_nonneg_right ht1 (Int.le_of_lt hf)
    omega
  · by_cases ht2 : t ≤ -1
    · have hb : t * f ≤ (-1) * f := Int.mul_le_mul_of_nonneg_right ht2 (Int.le_of_lt hf)
      omega
    · have ht0 : t = 0 := by omega
      subst ht0
      omega

/-! ## Sixth consumer: the T_mid kill.
At a corner of angle α+β the vertex figure is one α-corner and one β-corner
(`AngleArithmetic.alpha_beta_corner`). Labelling the tile's corners and their two adjacent sides,
an α-corner is flanked by b and c, a β-corner by a and c, a γ-corner by a and b. The T_mid
configuration requires both rays at such a corner to present b; the β-tile has no b-flank at all,
so it cannot. -/

/-- Tile corners. -/
inductive Corner | alpha | beta | gamma
deriving DecidableEq, Repr

/-- The two sides adjacent to a corner: the two not opposite it. -/
def flanks : Corner → Edge × Edge
  | Corner.alpha => (Edge.b, Edge.c)
  | Corner.beta  => (Edge.a, Edge.c)
  | Corner.gamma => (Edge.a, Edge.b)

/-- **The T_mid kill.** A β-corner presents a and c, never b. So at an α+β corner, where the figure
is exactly one α- and one β-corner, the two rays cannot both be b. -/
theorem beta_has_no_b_flank : (flanks Corner.beta).1 ≠ Edge.b ∧ (flanks Corner.beta).2 ≠ Edge.b := by
  decide

/-- Each corner's flank pair omits exactly the side opposite it, so the three flank pairs are
distinct and no corner presents its own opposite side. -/
theorem flanks_omit_opposite :
    (flanks Corner.alpha).1 ≠ Edge.a ∧ (flanks Corner.alpha).2 ≠ Edge.a ∧
    (flanks Corner.beta).1 ≠ Edge.b ∧ (flanks Corner.beta).2 ≠ Edge.b ∧
    (flanks Corner.gamma).1 ≠ Edge.c ∧ (flanks Corner.gamma).2 ≠ Edge.c := by decide

/-! ## Seventh consumer: the pentagon.
The pentagon lemma's arithmetic is `Pentagon.no_partition` and `Pentagon.stub_lt_a_and_b`: the
interval `(0, min(a,b))` is a gap of the numerical semigroup `⟨a,b,c⟩`, and the stub `e² mod b`
lies in it. The interface field it needs is that the stub is nonzero, which is `b ∤ e²`, i.e.
coprimality; recorded here as the field consumed rather than reproved. -/

/-- The pentagon consumer, in interface form: a positive stub shorter than both a and b admits no
whole-edge partition. (The two bounds are `Pentagon.stub_lt_a_and_b`; the non-partition is
`Pentagon.no_partition`.) -/
theorem pentagon_consumer (a b s x y z : Nat) (hs : 0 < s) (ha : s < a) (hb : s < b)
    (h : x * a + y * b + z * (a + b) = s) : False := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    rcases Nat.eq_zero_or_pos y with hy | hy
    · subst hy
      rcases Nat.eq_zero_or_pos z with hz | hz
      · subst hz; omega
      · have : a + b ≤ z * (a + b) := Nat.le_mul_of_pos_left _ hz
        omega
    · have : b ≤ y * b := Nat.le_mul_of_pos_left _ hy
      omega
  · have : a ≤ x * a := Nat.le_mul_of_pos_left _ hx
    omega

/-! ## The bridge to the geometry, stated precisely.
`Dissection.lean` isolates the geometric facts it cannot yet derive as named predicates rather than
axioms. The one this interface needs for `walk_base` and `walk_side` is exactly `HasEdgeChains`:
that a subset of the target's frontier is a union of whole tile edges. Given it, a side of the
target is such a union, the multiset of edge labels along it gives `(P,Q,R)`, and the walk equation
is then just additivity of length — the content below. The remaining three fields (`gamma_trap`,
`corner_ac`, `base_b_count`) are consequences of the vertex-figure classification, which needs
`HasAngleSums`, the predicate `Dissection.lean` records as the sharpest gap (Mathlib has no
angles-around-a-point statement and no machinery to build one). So the geometric debt of the four
chain steps formalized here is: `HasEdgeChains` + `HasAngleSums`, and nothing else. -/

/-- Given the edge labels along a side, the walk equation is additivity of length: if a side of
length `L` is the union of `P` a-edges, `Q` b-edges and `R` c-edges then `P·a + Q·b + R·c = L`.
Stated as the identity it is, so that the geometric content sits entirely in the hypothesis that
such a decomposition exists. -/
theorem walk_from_chain (a b c L P Q R : Nat) (h : P * a + Q * b + R * c = L) :
    P * a + Q * b + R * c = L := h

/-! ## What this buys, stated exactly.
`side_no_b_*` is now a theorem whose only inputs are the interface fields, so the step is VERIFIED
relative to `BaseBeta`. The remaining work for E2 is to construct a `BaseBeta` from a `Dissection`
— i.e. to prove `walk_base`, `walk_side`, `gamma_trap`, `corner_ac` and `base_b_count` from the
geometry. Those five are the entire geometric debt of the two steps formalized here (`side_no_b`
and the base-walk trichotomy); the rest of the chain adds its own fields, each listed here as it is
consumed. -/

end Erdos634.Interface
