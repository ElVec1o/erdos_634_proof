-- Inflation.lean — the inflated tile's boundary at (1,3), and what forces it.
--
-- The base-β tile is a rep-tile: expansion by f is tiled by f² copies (companion `rem:blockbreaks`).
-- At m = 1 the west corner block IS that inflation, and its far side is the whole equal side, so
-- "is the inflation rigid?" and "is p = 0 on the west side?" are the same question. This file carries
-- the combinatorial half at (1,3), tile (3,8,9), inflated to (9,24,27).
--
-- Each corner of the inflated triangle takes a single tile (companion), and that tile's two edges
-- there are the flanks of the corner angle. Hence each side begins and ends with a prescribed edge,
-- and the middle is a word over {3,8,9} of known sum. The three lemmas below settle those middles.
--
-- SCOPE. That each corner takes one tile, and that the corner tile's edges lie along the two sides,
-- is geometric input and is NOT proved here; it is the hypothesis these arithmetic facts are applied
-- under. Per the project rule the corpus was surveyed first: `ChordDecomp` and `SecondEdge` carry
-- chord and vertex arithmetic, neither carries inflation side words.

import Mathlib.Tactic

namespace Erdos634.Inflation

/-- The three side lengths of the tile at `(1,3)`. -/
def isSide (x : ℕ) : Prop := x = 3 ∨ x = 8 ∨ x = 9

/-- Every tile side is at least `3`. -/
theorem three_le_of_isSide {x : ℕ} (h : isSide x) : 3 ≤ x := by
  rcases h with h | h | h <;> omega

/-- A word of tile sides has sum `0` or at least `3`; there is nothing in between. -/
theorem sum_zero_or_three {w : List ℕ} (h : ∀ x ∈ w, isSide x) : w.sum = 0 ∨ 3 ≤ w.sum := by
  match w with
  | [] => left; simp
  | x :: t =>
      right
      have := three_le_of_isSide (h x (by simp))
      simp only [List.sum_cons]
      omega

/-- A word of tile sides summing to `3` is a single `a`-edge.  This is the middle of the inflated
`a`-side, whose ends are `a`-edges: `3 + 3 + 3 = 9`. -/
theorem middle_three (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 3) : w = [3] := by
  match w with
  | [] => simp at hs
  | [x] => simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs; simp [hs]
  | x :: y :: t =>
      have hx := three_le_of_isSide (h x (by simp))
      have hy := three_le_of_isSide (h y (by simp))
      simp only [List.sum_cons] at hs
      omega

/-- A word of tile sides summing to `8` is a single `b`-edge.  This is the middle of the inflated
`b`-side: `8 + 8 + 8 = 24`, and no other composition exists. -/
theorem middle_eight (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 8) : w = [8] := by
  match w with
  | [] => simp at hs
  | [x] => simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs; simp [hs]
  | x :: y :: t =>
      exfalso
      have hx := h x (by simp)
      have hy := h y (by simp)
      have ht := sum_zero_or_three (w := t) (fun z hz => h z (by simp [hz]))
      simp only [List.sum_cons] at hs
      rcases hx with h'|h'|h' <;> rcases hy with h''|h''|h'' <;>
        rw [h', h''] at hs <;> omega

/-- A word of tile sides summing to `9` is `[9]` or `[3,3,3]`.  This is the middle of the inflated
`c`-side, whose ends are `c`-edges: `9 + 9 + 9 = 27` and `9 + 3 + 3 + 3 + 9 = 27`.  **Two words
survive, and this is exactly the rigidity question.** -/
theorem middle_nine (w : List ℕ) (h : ∀ x ∈ w, isSide x) (hs : w.sum = 9) :
    w = [9] ∨ w = [3, 3, 3] := by
  match w with
  | [] => simp at hs
  | [x] => simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs; exact Or.inl (by simp [hs])
  | [x, y] =>
      exfalso
      rcases h x (by simp) with h'|h'|h' <;> rcases h y (by simp) with h''|h''|h'' <;>
        simp only [List.sum_cons, List.sum_nil, h', h''] at hs <;> omega
  | [x, y, z] =>
      right
      have hx := h x (by simp); have hy := h y (by simp); have hz := h z (by simp)
      simp only [List.sum_cons, List.sum_nil] at hs
      rcases hx with h'|h'|h' <;> rcases hy with h''|h''|h'' <;> rcases hz with h'''|h'''|h''' <;>
        simp_all <;> omega
  | x :: y :: z :: u :: t =>
      exfalso
      have hx := three_le_of_isSide (h x (by simp))
      have hy := three_le_of_isSide (h y (by simp))
      have hz := three_le_of_isSide (h z (by simp))
      have hu := three_le_of_isSide (h u (by simp))
      simp only [List.sum_cons] at hs
      omega

/-- **The two inflated `c`-side words at `(1,3)`.**  Both have length `27`; the first is the standard
subdivision, the second is the `p=1` side word `c a a a c`. -/
theorem c_side_words : ([9, 9, 9] : List ℕ).sum = 27 ∧ ([9, 3, 3, 3, 9] : List ℕ).sum = 27 := by
  constructor <;> decide

/-- The inflated `a`- and `b`-sides are rigid: `9 = 3+3+3` and `24 = 8+8+8` are their only
compositions with the prescribed end edges. -/
theorem a_b_sides_rigid : ([3, 3, 3] : List ℕ).sum = 9 ∧ ([8, 8, 8] : List ℕ).sum = 24 := by
  constructor <;> decide


/-! ## The same forcing at `(3,7)`

Tile `(21,40,49)` inflated to `(147,280,343)`, `49` copies. The residual lengths after removing the
two prescribed end edges are `105`, `200`, `245`. The first two have unique compositions; the third
has exactly two, and they are `p = 0` and `p = 1` on the equal side. -/

/-- The inflated `a`-side is rigid at `(3,7)`: `105 = 5·21` and nothing else. -/
theorem residual_105 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 105) :
    x = 5 ∧ y = 0 ∧ z = 0 := by
  have hy : y ≤ 2 := by omega
  have hz : z ≤ 2 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- The inflated `b`-side is rigid at `(3,7)`: `200 = 5·40` and nothing else. -/
theorem residual_200 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 200) :
    x = 0 ∧ y = 5 ∧ z = 0 := by
  have hy : y ≤ 5 := by omega
  have hz : z ≤ 4 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- **The inflated `c`-side at `(3,7)` has exactly two compositions**, `5·49` and `7·21 + 2·49`.
Adding the two end `c`-edges gives the whole-side profiles `(0 a, 7 c)` and `(7 a, 4 c)` --- that is,
`p = 0` and `p = 1`. This is the crux, posed on `49` tiles instead of `138`. -/
theorem residual_245 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 245) :
    (x = 0 ∧ y = 0 ∧ z = 5) ∨ (x = 7 ∧ y = 0 ∧ z = 2) := by
  have hy : y ≤ 6 := by omega
  have hz : z ≤ 5 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- Both survivors have the right length, and the whole-side profiles are `p=0` and `p=1`. -/
theorem c_side_profiles_37 :
    49 + (49 * 5) + 49 = 343 ∧ 49 + (21 * 7 + 49 * 2) + 49 = 343 := by
  constructor <;> decide

/-- The inflation is `35%` of the target at `(3,7)`: `49` tiles against `N = 138`. -/
theorem inflation_smaller_37 : 49 < 138 := by decide


/-! ## The γ-corner hypothesis is not needed

Only the `α`- and `β`-corners need be single, and both are: two tiles at the `α`-corner already exceed
`α`, and the `β`-corner would need `β/α` integral, which fails at both members. The `γ`-corner may
split as `{α,α,β}` for all we know, and it does not matter:

* the `c`-side joins the `α`- and `β`-vertices, so **both** its end edges are `c` unconditionally;
* the `a`-side has its `β`-end forced to `a`, and the residual has a unique composition;
* the `b`-side has its `α`-end forced to `b`, and likewise.

So the side words are determined without any assumption at the `γ`-corner. -/

/-- The inflated `a`-side at `(3,7)`, with only its `β`-end known: residual `126` is `6·21`. -/
theorem residual_126 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 126) :
    x = 6 ∧ y = 0 ∧ z = 0 := by
  have hy : y ≤ 3 := by omega
  have hz : z ≤ 2 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- The inflated `b`-side at `(3,7)`, with only its `α`-end known: residual `240` is `6·40`. -/
theorem residual_240 (x y z : ℕ) (h : 21 * x + 40 * y + 49 * z = 240) :
    x = 0 ∧ y = 6 ∧ z = 0 := by
  have hy : y ≤ 6 := by omega
  have hz : z ≤ 4 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- The same at `(1,3)`: residuals `6` and `16` over `{3,8,9}` are `2·3` and `2·8`. -/
theorem residual_13_sides (x y z : ℕ) :
    (3 * x + 8 * y + 9 * z = 6 → x = 2 ∧ y = 0 ∧ z = 0)
  ∧ (3 * x + 8 * y + 9 * z = 16 → x = 0 ∧ y = 2 ∧ z = 0) := by
  constructor <;> intro h <;> [skip; skip] <;>
    (have hy : y ≤ 2 := by omega
     have hz : z ≤ 1 := by omega
     interval_cases y <;> interval_cases z <;> omega)


/-! ## The last hypothesis dissolves

`prop:inflbdy` needed the `β`-corner to be single, which required `β/α ∉ ℤ`. That holds at every
member, and not by computation: `β = kα` together with `3α + 2β = π` forces `α(3+2k) = π`, so
`α/π = 1/(3+2k)` would be rational, contradicting the irrationality of `α/π` (Niven, via
`sin(α/2) = e/(2f)`). -/

/-- **`β` is never an integer multiple of `α`.**  Otherwise `α/π` would be rational. -/
theorem beta_not_nat_multiple {al be : ℝ} (hal : 0 < al)
    (hsum : 3 * al + 2 * be = Real.pi) (hirr : Irrational (al / Real.pi)) (k : ℕ) :
    be ≠ k * al := by
  intro h
  subst h
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hval : al / Real.pi = 1 / (3 + 2 * k) := by
    have h3 : al * (3 + 2 * (k : ℝ)) = Real.pi := by linarith
    have hne : (3 : ℝ) + 2 * k ≠ 0 := by positivity
    field_simp
    linarith [h3]
  exact hirr ⟨1 / (3 + 2 * (k : ℚ)), by push_cast [hval]; norm_num⟩

/-- Consequently the `β`-corner of the inflated triangle is met by a single tile at every member,
and `prop:inflbdy` carries no hypothesis at all. -/
theorem beta_corner_single {al be : ℝ} (hal : 0 < al)
    (hsum : 3 * al + 2 * be = Real.pi) (hirr : Irrational (al / Real.pi)) :
    ∀ k : ℕ, be ≠ k * al := fun k => beta_not_nat_multiple hal hsum hirr k


/-! ## The same at `(2,5)`

Tile `(10,21,25)` inflated to `(50,105,125)`, `25` copies. Residuals `40`, `84`, `75`. The first two
are unique; the third has two compositions, which are `p = 0` and `p = 1`. -/

/-- The inflated `a`-side at `(2,5)`: residual `40` is `4·10`. -/
theorem residual_40 (x y z : ℕ) (h : 10 * x + 21 * y + 25 * z = 40) :
    x = 4 ∧ y = 0 ∧ z = 0 := by
  have hy : y ≤ 1 := by omega
  have hz : z ≤ 1 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- The inflated `b`-side at `(2,5)`: residual `84` is `4·21`. -/
theorem residual_84 (x y z : ℕ) (h : 10 * x + 21 * y + 25 * z = 84) :
    x = 0 ∧ y = 4 ∧ z = 0 := by
  have hy : y ≤ 4 := by omega
  have hz : z ≤ 3 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- **The inflated `c`-side at `(2,5)` has exactly two compositions**, `3·25` and `5·10 + 1·25`.
With the two end `c`-edges these are the whole-side profiles `(0a,5c)` and `(5a,3c)`, i.e. `p = 0` and
`p = 1`. -/
theorem residual_75 (x y z : ℕ) (h : 10 * x + 21 * y + 25 * z = 75) :
    (x = 0 ∧ y = 0 ∧ z = 3) ∨ (x = 5 ∧ y = 0 ∧ z = 1) := by
  have hy : y ≤ 3 := by omega
  have hz : z ≤ 3 := by omega
  interval_cases y <;> interval_cases z <;> omega

/-- The three members where the two-word dichotomy has been computed, with their `p=1` `c`-side
profiles: `(1,3)` gives `(3,0,2)`, `(2,5)` gives `(5,0,3)`, `(3,7)` gives `(7,0,4)`. Each has total
`f³`. -/
theorem p1_profiles_total :
    3 * 3 + 2 * 9 = 27 ∧ 5 * 10 + 3 * 25 = 125 ∧ 7 * 21 + 4 * 49 = 343 := by
  refine ⟨by decide, by decide, by decide⟩


/-! ## A parity obstruction for `e`, `f` of opposite parity

Under the extra hypothesis that the dissection is edge-to-edge, every interior edge is shared by two
tiles, so `3f² − (boundary edge count)` is even. The standard boundary has `3f` edges; the `p = 1`
boundary has `f + f + (f + (f−e)) = 4f − e`. The second count changes the parity exactly when `e` and
`f` differ in parity.

This does not prove `thm:inflrigid`: edge-to-edge is an extra hypothesis the main paper does not
assume, and the obstruction is silent when `e` and `f` are both odd, which includes `(1,3)` and
`(3,7)`. It is recorded because it is free and because it explains why the even-`e` members were the
cheap ones for the search. -/

/-! **The criterion.**  `3f² − (4f − e)` has the parity of `f + e`, since `3f² ≡ f² ≡ f` and
`4f ≡ 0` mod 2. So the `p=1` boundary fails the edge-parity test exactly when `e` and `f` differ in
parity; with `gcd(e,f) = 1` that is exactly the case where one of them is even. The instances below
record the four members computed. -/

/-- **The parity obstruction, stated generally.**  Under edge-to-edge the `3f²` edge-slots split as
`2·(interior edges) + (boundary edges)`, and the `p=1` boundary has `B + e = 4f`.  Together these force
`e ≡ f (mod 2)`.  Contrapositive: if `e` and `f` differ in parity, no edge-to-edge dissection of the
inflated tile can carry the `p=1` boundary.

This replaces three earlier numeral-level facts (`3·25 − 18` odd, etc.).  Those were closed arithmetic
on literals and would have passed even if the boundary count `B` had been derived wrongly; the content
is in the two hypotheses, so the two hypotheses are what the statement must quantify over. -/
theorem parity_forces_same_parity (e f I B : ℕ)
    (hslots : 3 * f ^ 2 = 2 * I + B) (hbdy : B + e = 4 * f) :
    e % 2 = f % 2 := by
  have hsq : f ^ 2 % 2 = f % 2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one f with h | h <;> rw [h] <;> rfl
  omega

/-- The instances, now *derived* from the general statement rather than asserted:
at `(2,5)` and `(4,9)` the parities differ, so the hypothesis set is contradictory. -/
theorem parity_kills_25 (I B : ℕ) (hs : 3 * 5 ^ 2 = 2 * I + B) (hb : B + 2 = 4 * 5) : False := by
  have := parity_forces_same_parity 2 5 I B hs hb; omega

theorem parity_kills_49 (I B : ℕ) (hs : 3 * 9 ^ 2 = 2 * I + B) (hb : B + 4 = 4 * 9) : False := by
  have := parity_forces_same_parity 4 9 I B hs hb; omega

/-- At `(1,3)` and `(3,7)` the parities agree, so the obstruction is silent: the hypotheses are
satisfiable.  Witnesses exhibited, so the silence is a fact and not an absence of effort. -/
theorem parity_silent_witnesses :
    (3 * 3 ^ 2 = 2 * 8 + 11 ∧ 11 + 1 = 4 * 3) ∧ (3 * 7 ^ 2 = 2 * 61 + 25 ∧ 25 + 3 = 4 * 7) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-! ## The `p=1` word needs two `c`-edges

`prop:inflbdy` forces both end letters of the `c`-side to be `c`-edges, and the `p=1` word has
`f + (f-e) ≥ 2` letters, so those are two distinct positions. Its `c`-count is `f - e`, whence
`f - e ≥ 2`. At `e = f-1` the count is `1`, so no such word exists: the inflation is rigid on that
whole family with no search. -/

/-- **The combinatorial content of `cor:twoc`.**  A word that begins and ends with the same letter
`x` — the geometry gives exactly this: the `c`-side joins the `α`- and `β`-vertices and neither can
present an `a`, so the first and last letters are both `c` — contains that letter at least twice.

Stated as a structural decomposition `x :: (M ++ [x])` rather than as hypotheses on `head?`/`getLast?`,
because that is precisely what the two corner tiles supply: a first letter, a last letter, and an
unconstrained middle. -/
theorem two_of_sandwich {α : Type*} [DecidableEq α] (x : α) (M : List α) :
    2 ≤ (x :: (M ++ [x])).count x := by
  simp [List.count_cons, List.count_append]

/-- Hence the `p=1` word's `c`-count, which is `f − e`, is at least two.  The earlier
`p1_requires_two_c` was vacuous — in `ℕ`, `2 ≤ f − e` under `e < f` *is* `e + 2 ≤ f`, so hypothesis and
conclusion coincided.  Here the bound is *derived* from the word's shape. -/
theorem p1_c_count_ge_two {α : Type*} [DecidableEq α] (x : α) (M : List α) (e f : ℕ)
    (hcount : (x :: (M ++ [x])).count x = f - e) : 2 ≤ f - e := by
  rw [← hcount]; exact two_of_sandwich x M

/-- **The family exclusion.**  At `e = f − 1` the `c`-count is `1`, contradicting the bound, so no
`p=1` word exists and the inflation is rigid there — uniformly in `f`, with no search. -/
theorem no_p1_word_at_e_pred {α : Type*} [DecidableEq α] (x : α) (M : List α) (f : ℕ) (hf : 2 ≤ f)
    (hcount : (x :: (M ++ [x])).count x = f - (f - 1)) : False := by
  have h := p1_c_count_ge_two x M (f - 1) f hcount
  omega


/-! ## S3: the first `c|a` junction of the `k=2` word

For the `k=2` family (`e = f-2`, `f` odd) the `c`-side word is forced to `c a^f c` (`cor:twoc` plus the
`c`-count).  Put the `β`-vertex at the origin.  The corner tile `Z` lays that first `c` and has `β` at
the corner, so at the far end `J₁` it presents `α` — the ends of a `c`-edge carry the angles adjacent
to `c`, namely `α` and `β`.  The first `a`-tile `Y₁` lays an `a`-edge, whose ends carry the angles
adjacent to `a`, namely `β` and `γ`.

`BaseBetaE1.vertex_pi` says a straight figure is `(3α,2β)` or `(α,β,γ)`.  Removing `Z`'s `α` and `Y₁`'s
angle leaves the residue that further tiles at `J₁` must supply.  The enumeration below is exhaustive.

The count is **three**, not two.  An earlier statement of this rung claimed "at most two completions";
that was a guess and it is false. -/

/-- A straight figure written as `(#α, #β, #γ)`. -/
abbrev Fig := ℕ × ℕ × ℕ

/-- The two straight figures (`BaseBetaE1.vertex_pi`). -/
def straightFigs : List Fig := [(1, 1, 1), (3, 2, 0)]

/-- `Y₁` presents `β` (`true`) or `γ` (`false`). -/
def admissible (F : Fig) (yBeta : Bool) : Bool :=
  1 ≤ F.1 && (if yBeta then 1 ≤ F.2.1 else 1 ≤ F.2.2)

/-- The residue at `J₁` after removing `Z`'s `α` and `Y₁`'s angle. -/
def residue (F : Fig) (yBeta : Bool) : Fig :=
  if yBeta then (F.1 - 1, F.2.1 - 1, F.2.2) else (F.1 - 1, F.2.1, F.2.2 - 1)

/-- **Exactly three completions.**  Over both straight figures and both angles `Y₁` may present, three
pairs are admissible. -/
theorem junction_three :
    ((straightFigs.flatMap (fun F => [(F, true), (F, false)])).filter
      (fun p => admissible p.1 p.2)).length = 3 := by decide

/-- The three, with their residues: `{α,β,γ}` with `Y₁ = β` leaves one `γ`; `{α,β,γ}` with `Y₁ = γ`
leaves one `β`; `{3α,2β}` with `Y₁ = β` leaves `2α + β`.  So `J₁` carries 3, 3 and 5 tiles. -/
theorem junction_residues :
    ((straightFigs.flatMap (fun F => [(F, true), (F, false)])).filter
      (fun p => admissible p.1 p.2)).map (fun p => residue p.1 p.2)
      = [(0, 0, 1), (0, 1, 0), (2, 1, 0)] := by decide


/-! ## S4: consecutive `a|a` junctions constrain each other

A tile laying an `a`-edge on the boundary has, at that edge's two ends, the two angles adjacent to
side `a` — namely `β` and `γ`. So one tile presents `β` at one end and `γ` at the other; never `β` at
both. Record its orientation by which end carries `β`.

A junction between two consecutive `a`-tiles receives the right end of the left tile and the left end
of the right tile. The straight figure `{3α,2β}` carries no `γ` (`BaseBetaE1.vertex_pi`), so it demands
that *both* contributions be `β`.

The consequence is that the `{3α,2β}` junctions cannot be adjacent: a shared tile would have to carry
`β` at both ends of its own `a`-edge. This is the first constraint in this development that couples one
junction to the next, and it is what rung S4 asked for. -/

/-- Which end of a boundary `a`-tile's `a`-edge carries `β`. -/
inductive Orient | BG | GB
  deriving DecidableEq, Repr

open Orient

/-- The angle a tile contributes at the junction on its **right**. -/
def rightAngle : Orient → Bool
  | BG => false   -- γ
  | GB => true    -- β

/-- The angle a tile contributes at the junction on its **left**. -/
def leftAngle : Orient → Bool
  | BG => true    -- β
  | GB => false   -- γ

/-- A junction carries `{3α,2β}` exactly when both incident contributions are `β`; any `γ` forces the
figure `{α,β,γ}` instead. -/
def isAAB (l r : Orient) : Bool := rightAngle l && leftAngle r

/-- Sanity: exactly one of the four orientation pairs admits `{3α,2β}`. -/
theorem isAAB_unique :
    ([(BG,BG),(BG,GB),(GB,BG),(GB,GB)].filter (fun p => isAAB p.1 p.2)).length = 1 := by decide

/-- **S4.**  No two adjacent junctions along the `a`-run both carry `{3α,2β}`: the tile they share
would need `β` at both ends of its `a`-edge. -/
theorem no_two_adjacent_AAB (t₁ t₂ t₃ : Orient) : ¬(isAAB t₁ t₂ ∧ isAAB t₂ t₃) := by
  cases t₁ <;> cases t₂ <;> cases t₃ <;> simp [isAAB, rightAngle, leftAngle]

/-- Equivalently, the `{3α,2β}` junctions form an independent set: along `f` tiles there are `f-1`
junctions and at most `⌈(f-1)/2⌉` of them can carry that figure. -/
theorem AAB_forces_alternation (t₁ t₂ t₃ : Orient) (h : isAAB t₁ t₂ = true) :
    isAAB t₂ t₃ = false := by
  cases t₁ <;> cases t₂ <;> cases t₃ <;> simp_all [isAAB, rightAngle, leftAngle]


/-! ## The east half of `hyp:walls` at `e = 1`

The base of the target at `m = 1` accounts as an identity in `(e,f)`:
`e(3f² − e²) = f·a + e·b + e·c`, the three terms being the west foot, the middle, and the east foot.
The west corner block is the tile scaled by `f` and carries `f²` tiles; the east block is the tile
scaled by `e` and carries `e²`.

At `e = 1` the east block is therefore a **single tile**, and the east half of the hypothesis has no
content beyond `lem:ccorner` — a base corner tile laying `c` lays `a` on the side. -/

/-- The base identity: west foot `f·a`, middle `e·b`, east foot `e·c` sum to the base `e(3f²−e²)`. -/
theorem base_accounts (e f : ℕ) :
    f * (e * f) + e * (f * f - e * e) + e * (f * f) = e * (3 * f * f - e * e) ∨ f < e := by
  rcases lt_or_ge f e with h | h
  · right; exact h
  · left
    have h2 : e * e ≤ f * f := Nat.mul_le_mul h h
    have h3 : e * e ≤ 3 * f * f := le_trans h2 (by nlinarith)
    zify [h2, h3]; ring

-- NOTE: "at `e = 1` the east block is a single tile" is *not* stated as a theorem here. Its
-- arithmetic content is `1² = 1`, which is vacuous; its real content is geometric — that the block is
-- the tile scaled by `e`, which is `rem:blockbreaks`, and that a corner tile laying `c` lays `a` on
-- the side, which is `lem:ccorner`. Neither is available in this file. Recording `1 * 1 = 1` under a
-- geometric name would be a façade of the kind the 2026-08-12 audit removed.

/-- The east block is strictly smaller than the west whenever `e < f`. -/
theorem east_smaller (e f : ℕ) (h : e < f) : e * e < f * f :=
  Nat.mul_lt_mul_of_lt_of_le h (le_of_lt h) (Nat.pos_of_ne_zero (by rintro rfl; omega))


/-! ## S5: the orientation sequence is monotone, and the branching collapses to linear

S4 asked which adjacent pairs admit the figure `{3α,2β}`. The sharper question is which admit **any**
straight figure. Writing `right(BG) = γ`, `right(GB) = β`, `left(BG) = β`, `left(GB) = γ`, a junction
between consecutive `a`-tiles receives `right` of the left tile and `left` of the right tile:

| pair | contributions | figure |
|---|---|---|
| `BG,BG` | `γ, β` | `{α,β,γ}` |
| `BG,GB` | `γ, γ` | **none** — no straight figure carries two `γ`s |
| `GB,BG` | `β, β` | `{3α,2β}` |
| `GB,GB` | `β, γ` | `{α,β,γ}` |

So a `BG` is never followed by a `GB`. The orientation sequence along the run is therefore
`GB^j BG^{f-j}` for a single `j`, and the `{3α,2β}` junctions — the `GB,BG` transitions — number **at
most one**. Rung S3 left three completions per junction, so `3^{f-1}` patterns a priori; this leaves
`f+1`, one per `j`. -/

/-- A junction is admissible when its two contributions are not both `γ`. -/
def admissiblePair (l r : Orient) : Bool := rightAngle l || leftAngle r

/-- **The forbidden transition.**  `BG` then `GB` puts two `γ`s at their shared junction. -/
theorem BG_GB_forbidden : admissiblePair BG GB = false := by decide

/-- The other three pairs are admissible, so the constraint is not vacuous. -/
theorem others_admissible :
    admissiblePair BG BG = true ∧ admissiblePair GB BG = true ∧ admissiblePair GB GB = true := by
  decide

/-- `{3α,2β}` occurs exactly at a `GB,BG` transition. -/
theorem AAB_iff_transition (l r : Orient) : isAAB l r = true ↔ l = GB ∧ r = BG := by
  cases l <;> cases r <;> simp [isAAB, rightAngle, leftAngle]

/-- **S5.**  Along a run whose every adjacent pair is admissible, the orientations are a block of `GB`
followed by a block of `BG`.  The branching is linear in the run length, not exponential. -/
theorem orient_monotone :
    ∀ L : List Orient, L.Chain' (fun l r => admissiblePair l r = true) →
      ∃ j k, L = List.replicate j GB ++ List.replicate k BG := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, 0, rfl⟩
  | cons x t ih =>
    intro h
    cases t with
    | nil => cases x
             · exact ⟨0, 1, rfl⟩
             · exact ⟨1, 0, rfl⟩
    | cons y t' =>
      obtain ⟨hxy, hrest⟩ : admissiblePair x y = true ∧ (y :: t').Chain' (fun l r => admissiblePair l r = true) := by
        cases h with | cons_cons hh ht => exact ⟨hh, ht⟩
      obtain ⟨j, k, hjk⟩ := ih hrest
      cases x with
      | BG =>
        -- `BG` forces the next to be `BG`, so the tail has no `GB` block
        have hy : y = BG := by
          cases y
          · rfl
          · simp [admissiblePair, rightAngle, leftAngle] at hxy
        subst hy
        cases j with
        | zero =>
          refine ⟨0, k + 1, ?_⟩
          simp only [List.replicate_zero, List.nil_append] at hjk ⊢
          rw [List.replicate_succ]
          exact congrArg (BG :: ·) hjk
        | succ n => simp [List.replicate_succ] at hjk
      | GB =>
        refine ⟨j + 1, k, ?_⟩
        rw [List.replicate_succ, List.cons_append]
        exact congrArg (GB :: ·) hjk


/-! ## The general scale `k`: the `a`-side is rigid, and the `β`-corner dichotomy

`prop:inflbdy` is stated at scale `f`, and its proof reads the `a`-side residual off a numeral.
The statement is really uniform in the scale, and this section proves the uniform version.

Let `Δ_k` be the tile inflated by `k`, `1 ≤ k ≤ f`, tiled by `k²` copies.  Its three sides are
`k·a` (opposite `α`), `k·b` (opposite `β`) and `k·c` (opposite `γ`); side `a` joins the `β`- and
`γ`-corners, so it is one of the two sides at the `β`-corner, the other being the `c`-side.

*  `a_unsplittable` — `a` is not a sum of two or more tile edges.  This is the companion of
   `BaseBetaCorners.b_unsplittable`, and it is what makes the `α`-corner chord rigid: the `α`-corner
   of an inflation is met by a **single** tile (`corner_apex_unique`-style: `x + 2z = 1`, `y + z = 0`
   force `(1,0,0)`), whose `a`-edge is a chord with both ends on the boundary.

*  `a_side_no_b` — **the `a`-side of a scale-`k` inflation carries no `b`-edge, for every `k ≤ f`.**
   Length alone does not give this: `f·b ≤ k·e·f` is satisfiable whenever `a/b` is below the golden
   ratio (`GoldenForm`), i.e. on the close pairs.  The proof is a two-step descent.  Reduction mod
   `f` gives `f ∣ n_b`, say `n_b = f·s`; dividing the length identity by `f` and reducing mod `e`
   gives `e ∣ s·f + n_c`, say `s·f + n_c = e·t`; eliminating `n_c` leaves the linear relation

       n_a + t·f = k + s·e.

   Now `n_c ≥ 0` forces `e·t ≥ s·f > s·e`, hence `t > s`; and `n_a ≥ 0` with `k ≤ f` forces
   `t·f ≤ f + s·e`, hence `(s+1)·f ≤ f + s·e`, i.e. `f ≤ e`.  Contradiction unless `s = 0`.
   The hypothesis `k ≤ f` is used exactly once, in the second bound.

*  `a_side_words` — consequently the `a`-side word is `a^{k−qf} c^{qe}`; `a_side_rigid` — for
   `k < f` the only word is `a^k`; `a_side_all_c` — the sole alternative in the range is `k = f`
   with the side equal to `c^e`.

**The `β`-corner dichotomy this yields.**  The `β`-corner of `Δ_k` is met by a single tile
(`BaseBetaCorners.corner_beta_unique`) whose two edges there are the flanks `{a, c}`.  Since the
`a`-side is monochromatic, the corner tile lays on it whichever letter that side carries:

* `k < f`: the `a`-side is `a^k`, so the corner tile lays `a` there and `c` on the `c`-side — the
  standard orientation, with no hypothesis at all.  This is the missing half of `prop:inflbdy`'s
  claim that both end letters of the `c`-side are `c`, which that proof asserted from the flanks
  alone and which does not follow from the flanks alone.
* `k = f`: the second word `c^e` is combinatorially admissible, and there the corner tile lays `c`
  on the `a`-side and `a` on the `c`-side.  The corner block is then the *transverse* one, with
  `c`-feet, and `a_side_all_c` computes its footprint `n_c · c = k · a`: **its scale is `k·e/f`,
  which in the range `k ≤ f` is `e`.**  That is the arithmetic reason `hyp:walls` couples the two
  scales `f` and `e` rather than being a statement about `f` alone.

The transverse branch is not excluded by any of the above.  At `e = 1` it dies by a corner count:
the whole `a`-side is then a single `c`-edge, so the corner tile's `α` sits **at** the `γ`-corner of
`Δ_f`, leaving `γ − α = α + β`, which admits exactly one `α` and one `β` (`fill_alpha_beta`); but the
`b`-partner across the corner tile's chord — forced to be the direct partner, since the reflected one
would repeat `γ` at a straight junction and `2γ > π` — presents `γ` there, and `γ > α + β`.  For
`e ≥ 2` the branch is excluded only by search; see the note below.
-/

theorem a_unsplittable (e f b na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = e * f) :
    na = 1 ∧ nb = 0 ∧ nc = 0 := by
  have hf2 : 2 ≤ f := by omega
  have hbpos : 0 < b := by
    have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
    omega
  have hef0 : 0 < e * f := Nat.mul_pos (by omega) (by omega)
  have hlt : e * f < f ^ 2 := by nlinarith
  have hnc : nc = 0 := by
    by_contra h
    have : 1 * f ^ 2 ≤ nc * f ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  subst hnc
  have hna1 : na ≤ 1 := by
    by_contra h
    have : 2 * (e * f) ≤ na * (e * f) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hsum : nb * b + na * (e * f) = e * f := by omega
  have hnb : nb = 0 := by
    rcases Nat.lt_or_ge nb 1 with h | h
    · omega
    · exfalso
      have hbf : nb * b + nb * e ^ 2 = nb * f ^ 2 := by rw [← Nat.mul_add, hb]
      have h1 : f ∣ nb * b := by
        interval_cases na
        · exact ⟨e, by rw [mul_comm f e]; omega⟩
        · exact ⟨0, by omega⟩
      have hdvd : f ∣ nb * e ^ 2 :=
        (Nat.dvd_add_right h1).mp (by rw [hbf]; exact ⟨nb * f, by ring⟩)
      have hfnb : f ∣ nb :=
        Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right 2 hcop.symm) hdvd
      have hge : f ≤ nb := Nat.le_of_dvd (by omega) hfnb
      have h1' : f * b ≤ nb * b := Nat.mul_le_mul_right _ hge
      have h2 : f * b + f * e ^ 2 = f * f ^ 2 := by rw [← Nat.mul_add, hb]
      interval_cases na <;> nlinarith [h1', h2, sq_nonneg (f - e)]
  subst hnb
  refine ⟨?_, rfl, rfl⟩
  interval_cases na <;> omega

theorem f_dvd_nb (e f b nb : ℕ) (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (hz : (f : ℤ) ∣ (nb : ℤ) * (b : ℤ)) : f ∣ nb := by
  have hbz : (b : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hb
  have hz2 : (f : ℤ) ∣ (nb : ℤ) * (e : ℤ) ^ 2 := by
    have hrw : (nb : ℤ) * (e : ℤ) ^ 2 = (nb : ℤ) * (f : ℤ) ^ 2 - (nb : ℤ) * (b : ℤ) := by
      linear_combination (nb : ℤ) * hbz
    rw [hrw]; exact dvd_sub ⟨(nb : ℤ) * f, by ring⟩ hz
  have hnat : f ∣ nb * e ^ 2 := by exact_mod_cast hz2
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right 2 hcop.symm) hnat

theorem a_side_no_b (e f b k na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hk : k ≤ f)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = k * (e * f)) :
    nb = 0 := by
  have hbz : (b : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hb
  have hcast : (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * b + (nc : ℤ) * (f : ℤ) ^ 2
      = (k : ℤ) * ((e : ℤ) * f) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) heq
  have hfnb : f ∣ nb :=
    f_dvd_nb e f b nb hcop hb ⟨(k : ℤ) * e - na * e - nc * f, by linear_combination hcast⟩
  obtain ⟨s, hs⟩ := hfnb
  subst hs
  have hfz : ((f : ℤ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hez0 : ((e : ℤ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : (na : ℤ) * e + (s : ℤ) * b + (nc : ℤ) * f = (k : ℤ) * e := by
    refine mul_left_cancel₀ hfz ?_
    push_cast at hcast ⊢; linear_combination hcast
  -- e ∣ f * (s*f + nc), hence e ∣ s*f + nc
  have hdz : (e : ℤ) ∣ (f : ℤ) * ((s : ℤ) * f + nc) :=
    ⟨(s : ℤ) * e + k - na, by linear_combination h2 - (s : ℤ) * hbz⟩
  have hdn : e ∣ f * (s * f + nc) := by exact_mod_cast hdz
  obtain ⟨t, ht⟩ := Nat.Coprime.dvd_of_dvd_mul_left hcop hdn
  have htz : (s : ℤ) * f + nc = (e : ℤ) * t := by exact_mod_cast ht
  have h4 : (na : ℤ) + (t : ℤ) * f = (k : ℤ) + (s : ℤ) * e := by
    refine mul_left_cancel₀ hez0 ?_
    linear_combination h2 - (s : ℤ) * hbz - (f : ℤ) * htz
  by_contra hcon
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exact absurd (by simp [h]) hcon
    · exact h
  have hsz : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs1
  have hez : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
  have hefz : (e : ℤ) < f := by exact_mod_cast hef
  have hkz : (k : ℤ) ≤ f := by exact_mod_cast hk
  have hnaz : (0 : ℤ) ≤ (na : ℤ) := Int.natCast_nonneg na
  have hncz : (0 : ℤ) ≤ (nc : ℤ) := Int.natCast_nonneg nc
  have hts : (s : ℤ) < (t : ℤ) := by nlinarith
  nlinarith [hts, h4, hnaz, hkz, hsz, hefz]

theorem a_side_words (e f k na nc : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (heq : na * (e * f) + nc * f ^ 2 = k * (e * f)) :
    ∃ q, na + q * f = k ∧ nc = q * e := by
  have h2 : na * e + nc * f = k * e := by
    have hz : (f : ℤ) * ((na : ℤ) * e + (nc : ℤ) * f) = (f : ℤ) * ((k : ℤ) * e) := by
      have hc : (na : ℤ) * ((e : ℤ) * f) + (nc : ℤ) * (f : ℤ) ^ 2 = (k : ℤ) * ((e : ℤ) * f) := by
        exact_mod_cast heq
      linear_combination hc
    exact_mod_cast mul_left_cancel₀ (Nat.cast_ne_zero.mpr (show f ≠ 0 by omega)) hz
  have hnak : na ≤ k := Nat.le_of_mul_le_mul_right (by omega : na * e ≤ k * e) (by omega)
  have hsub : (k - na) * e = nc * f := by rw [Nat.sub_mul]; omega
  obtain ⟨q, hq⟩ :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop.symm (⟨nc, by rw [hsub, Nat.mul_comm]⟩ : f ∣ (k - na) * e)
  refine ⟨q, by rw [Nat.mul_comm]; omega, ?_⟩
  refine Nat.eq_of_mul_eq_mul_right (show 0 < f by omega) ?_
  rw [← hsub, hq]; ring

theorem a_side_rigid (e f k na nc : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hkf : k < f) (heq : na * (e * f) + nc * f ^ 2 = k * (e * f)) :
    na = k ∧ nc = 0 := by
  obtain ⟨q, h1, h2⟩ := a_side_words e f k na nc he hef hcop heq
  have hq : q = 0 := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exact h
    · exact absurd h1 (by have : f ≤ q * f := Nat.le_mul_of_pos_left f h; omega)
  subst hq; omega

theorem a_side_all_c (e f k na nc : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hk : k ≤ f) (hk0 : 0 < k) (hna : na = 0)
    (heq : na * (e * f) + nc * f ^ 2 = k * (e * f)) :
    k = f ∧ nc = e ∧ nc * f = k * e := by
  obtain ⟨q, h1, h2⟩ := a_side_words e f k na nc he hef hcop heq
  subst hna
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; omega
    · exact h
  have hqle : q ≤ 1 := Nat.le_of_mul_le_mul_right (by omega : q * f ≤ 1 * f) (by omega)
  have : q = 1 := by omega
  subst this
  refine ⟨by omega, by omega, ?_⟩
  have hkf : k = f := by omega
  have hnce : nc = e := by omega
  rw [hkf, hnce]; exact Nat.mul_comm e f

/-! ### Scope of the transverse branch

`a_side_all_c` says the branch exists as arithmetic; whether it is geometrically realizable is a
separate question, and it was **not** covered by the searches behind `thm:inflrigid`, which fixed the
`a`-side to `a^f` throughout (`code/engine/gen_inflation.py` hard-codes the word `f 0 0`).  Running
the same engine with the `a`-side set to `c^e`, over every admissible `c`-side word, returns
`EXHAUSTED_NO_TILING` on all 61 instances over the thirteen members

    (1,3) (2,3) (1,4) (3,4) (1,5) (2,5) (3,5) (4,5) (1,6) (5,6) (1,7) (3,7) (5,7)

with the standard boundary returning `FOUND_TILING` as the negative control in every case.  That is
computer assistance, not a proof, and it is recorded here so the gap in `prop:inflbdy`'s proof is not
silently inherited. -/


/-! ## The `B`-side and the `c`-side carry no extra `b`-edge below scale `f`

`a_side_no_b` settled the `a`-side.  The other two sides of `Δ_k` had been settled only for
`b`-multiplicity `s ≤ 1`; the case `s ≥ 2` — length-feasible only when `f² + f ≤ 2e²`, i.e.
`f/e < √2`, strictly inside the close pairs — was verified numerically and left open.  It is not
open: the same two-step descent (mod `f`, then mod `e`, then non-negativity) kills **every**
`s ≥ 1` on both sides at once, for every member and every `k < f`, with no size hypothesis.

*  `b_side_rigid` — **the `B`-side of a scale-`k` inflation, `k < f`, is `b^k` exactly.**
   One line each way: reducing the length identity `n_a·a + n_b·b + n_c·c = k·b` mod `f` gives
   `f ∣ (k − n_b)·e²`, hence `f ∣ k − n_b`; and `n_b·b ≤ k·b` gives `n_b ≤ k < f`, so `n_b = k`
   and the `a`- and `c`-counts vanish.  No close-pair hypothesis: this holds for all members.

*  `c_side_no_b` — **the `c`-side of a scale-`k` inflation, `k < f`, carries no `b`-edge.**
   Mod `f` gives `f ∣ n_b`, say `n_b = s·f`; dividing by `f` and reducing mod `e` gives
   `e ∣ s·f + n_c − k`, say `= e·t`; eliminating `n_c` leaves the linear relation

       n_a + t·f = s·e.

   For `s ≥ 1` and `k ≤ f − 1`:  `e·t = s·f + n_c − k ≥ (s−1)·f + 1`, so `t ≥ 1`; and
   `t·f ≤ s·e < s·f` forces `t ≤ s − 1`, whence
   `(s−1)·f + 1 ≤ e·t ≤ e·(s−1) ≤ (f−1)·(s−1)` — i.e. `s ≤ 0`.  Contradiction.
   The hypothesis `k ≤ f − 1` is used exactly once, in the first bound.

*  `c_side_words_scale` — with the `b`-count dead the `c`-side words are `(n_a, n_c) = (q·f, k − q·e)`:
   exactly the `p = 0` versus `p ≥ 1` dichotomy of `thm:inflrigid`, which these lemmas do **not**
   decide and are not meant to.

**Sharpness.**  Both statements fail at `k = f`, and the failures are exhibited below:
the `c`-side admits `(e, f, 0)` — the `ScaleBreak` word, killed at `k = f` only by the `γ`-trap
(`SideNoB.side_no_b_uncond`, which is precisely the `k = f` case) — and the `B`-side admits
`(f−e, 0, f−e)`.  So `k < f` is the exact range, and together with `SideNoB` the whole tower
`k ≤ f` is covered: the boundary of every sub-scale inflation is `b`-free on the `a`- and
`c`-sides and exactly `b^k` on the `B`-side.

Verified exhaustively before proving: all 541 members with `f ≤ 42`, every `k < f`, full naive
enumeration of every word (29 426 side checks, zero violations, both `k = f` witnesses found at
all 541 members), and the residue-parametrized form on all 48 677 pairs with `f ≤ 400`
(`code/side_words_scale_k.py`). -/

/-- **The `B`-side is `b^k` exactly, for every `k < f`.**  The two ingredients are the mod-`f`
residue `f ∣ k − n_b` and the inventory `n_b ≤ k`; coprimality does the rest.  This closes the
`s ≥ 2` case on the `B`-side for **all** members, not only the close pairs. -/
theorem b_side_rigid (e f b k na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hk : k < f)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = k * b) :
    na = 0 ∧ nb = k ∧ nc = 0 := by
  have hbpos : 0 < b := by
    have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
    omega
  -- inventory: n_b ≤ k
  have hmul : nb * b ≤ k * b := by omega
  have hnbk : nb ≤ k := Nat.le_of_mul_le_mul_right hmul hbpos
  -- the residue: f ∣ (k − n_b)
  have hdb : na * (e * f) + nc * f ^ 2 = (k - nb) * b := by
    have h1 : (k - nb) * b + nb * b = k * b := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hnbk]
    omega
  have hfd : f ∣ (k - nb) := by
    have h1 : f ∣ (k - nb) * b := by
      rw [← hdb]; exact Nat.dvd_add ⟨na * e, by ring⟩ ⟨nc * f, by ring⟩
    have hsum : (k - nb) * b + (k - nb) * e ^ 2 = (k - nb) * f ^ 2 := by
      rw [← Nat.mul_add, hb]
    have h2 : f ∣ (k - nb) * e ^ 2 := by
      have h3 : f ∣ (k - nb) * f ^ 2 := ⟨(k - nb) * f, by ring⟩
      have h4 : (k - nb) * e ^ 2 = (k - nb) * f ^ 2 - (k - nb) * b := by omega
      rw [h4]; exact Nat.dvd_sub h3 h1
    exact (Nat.Coprime.pow_right 2 hcop.symm).dvd_of_dvd_mul_right h2
  -- k − n_b < f and f ∣ (k − n_b) force n_b = k, then the other counts vanish
  have hnb : nb = k := by
    rcases hfd with ⟨j, hj⟩
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp only [Nat.mul_zero] at hj; omega
    · exfalso; have : f ≤ f * j := Nat.le_mul_of_pos_right f h; omega
  subst hnb
  have hef0 : 0 < e * f := Nat.mul_pos (by omega) (by omega)
  have hf2 : 0 < f ^ 2 := pow_pos (by omega : 0 < f) 2
  constructor
  · by_contra h
    have : 1 * (e * f) ≤ na * (e * f) := Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨rfl, ?_⟩
  by_contra h
  have : 1 * f ^ 2 ≤ nc * f ^ 2 := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The `c`-side of a scale-`k` inflation, `k < f`, carries no `b`-edge** — every `s ≥ 1` at
once, all members, no size or close-pair hypothesis.  The `s ≥ 2` case had been open exactly on
`f/e < √2`; the descent does not see the threshold. -/
theorem c_side_no_b (e f b k na nb nc : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hk : k < f)
    (heq : na * (e * f) + nb * b + nc * f ^ 2 = k * f ^ 2) :
    nb = 0 := by
  have hbz : (b : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hb
  have hcast : (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * b + (nc : ℤ) * (f : ℤ) ^ 2
      = (k : ℤ) * (f : ℤ) ^ 2 := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) heq
  -- step 1, mod f:  f ∣ n_b
  have hfnb : f ∣ nb :=
    f_dvd_nb e f b nb hcop hb ⟨(k : ℤ) * f - na * e - nc * f, by linear_combination hcast⟩
  obtain ⟨s, hs⟩ := hfnb
  subst hs
  by_contra hcon
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exact absurd (by simp [h]) hcon
    · exact h
  have hfz : ((f : ℤ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hez0 : ((e : ℤ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- divide the identity by f
  have h2 : (na : ℤ) * e + (s : ℤ) * b + (nc : ℤ) * f = (k : ℤ) * f := by
    refine mul_left_cancel₀ hfz ?_
    push_cast at hcast ⊢; linear_combination hcast
  -- step 2, mod e:  e ∣ s·f + n_c − k, extracted in ℕ (the quantity is nonnegative since s ≥ 1)
  have hkle : k ≤ s * f + nc := by
    have : f ≤ s * f := Nat.le_mul_of_pos_left f hs1
    omega
  have hcastq : (((s * f + nc - k : ℕ)) : ℤ) = ((s : ℤ) * f + nc) - k := by
    push_cast [Nat.cast_sub hkle]; ring
  have hdz : (e : ℤ) ∣ (f : ℤ) * (((s : ℤ) * f + nc) - k) :=
    ⟨(s : ℤ) * e - na, by linear_combination h2 - (s : ℤ) * hbz⟩
  have hdn : e ∣ f * (s * f + nc - k) := by
    rw [← hcastq] at hdz
    exact_mod_cast hdz
  obtain ⟨t, ht⟩ := Nat.Coprime.dvd_of_dvd_mul_left hcop hdn
  have htz : ((s : ℤ) * f + nc) - k = (e : ℤ) * t := by
    have h3 : ((s * f + nc - k : ℕ) : ℤ) = ((e : ℤ)) * t := by exact_mod_cast ht
    rw [← hcastq]; exact h3
  -- the linear relation:  n_a + t·f = s·e
  have h4 : (na : ℤ) + (t : ℤ) * f = (s : ℤ) * e := by
    refine mul_left_cancel₀ hez0 ?_
    linear_combination h2 - (s : ℤ) * hbz - (f : ℤ) * htz
  -- non-negativity closes: t ≤ s−1 against e·t ≥ (s−1)·f + 1
  have hsz : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs1
  have hez : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
  have hefz : (e : ℤ) < f := by exact_mod_cast hef
  have hkz : (k : ℤ) < f := by exact_mod_cast hk
  have hnaz : (0 : ℤ) ≤ (na : ℤ) := Int.natCast_nonneg na
  have hncz : (0 : ℤ) ≤ (nc : ℤ) := Int.natCast_nonneg nc
  -- t < s:  t·f ≤ s·e < s·f
  have htf : (t : ℤ) * f ≤ (s : ℤ) * e := by linarith
  have h9 : (s : ℤ) * e < (s : ℤ) * f := mul_lt_mul_of_pos_left hefz (by linarith)
  have hts : (t : ℤ) < s := lt_of_mul_lt_mul_right (by linarith) (by linarith : (0 : ℤ) ≤ (f : ℤ))
  -- e·t ≤ (f−1)(s−1) against e·t ≥ s·f − f + 1
  have h5a : (e : ℤ) * t ≤ (e : ℤ) * (s - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h5b : (e : ℤ) * (s - 1) ≤ ((f : ℤ) - 1) * (s - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h6 : (s : ℤ) * f - f + 1 ≤ (e : ℤ) * t := by linarith
  have hexp : ((f : ℤ) - 1) * ((s : ℤ) - 1) = (f : ℤ) * s - f - s + 1 := by ring
  have hcomm : (s : ℤ) * f = (f : ℤ) * s := by ring
  linarith

/-- With the `b`-count dead, the `c`-side words are `(q·f, 0, k − q·e)` — the crux dichotomy in
its exact arithmetic form, the companion of `a_side_words`. -/
theorem c_side_words_scale (e f k na nc : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (heq : na * (e * f) + nc * f ^ 2 = k * f ^ 2) :
    ∃ q, na = q * f ∧ q * e + nc = k := by
  have hf0 : 0 < f := by omega
  have h2 : na * e + nc * f = k * f := by
    have hz : (f : ℤ) * ((na : ℤ) * e + (nc : ℤ) * f) = (f : ℤ) * ((k : ℤ) * f) := by
      have hc : (na : ℤ) * ((e : ℤ) * f) + (nc : ℤ) * (f : ℤ) ^ 2 = (k : ℤ) * (f : ℤ) ^ 2 := by
        exact_mod_cast heq
      linear_combination hc
    exact_mod_cast mul_left_cancel₀ (Nat.cast_ne_zero.mpr (show f ≠ 0 by omega)) hz
  have hfna : f ∣ na := by
    have h3 : f ∣ na * e := by
      have hk : f ∣ k * f := ⟨k, Nat.mul_comm k f⟩
      have hc : f ∣ nc * f := ⟨nc, Nat.mul_comm nc f⟩
      have h5 : na * e = k * f - nc * f := by omega
      rw [h5]; exact Nat.dvd_sub hk hc
    exact (Nat.coprime_comm.mp hcop).dvd_of_dvd_mul_right h3
  obtain ⟨q, hq⟩ := hfna
  refine ⟨q, by rw [hq, Nat.mul_comm], ?_⟩
  refine Nat.eq_of_mul_eq_mul_left hf0 ?_
  calc f * (q * e + nc) = (f * q) * e + nc * f := by ring
    _ = k * f := by rw [← hq]; exact h2
    _ = f * k := by ring

/-- **Sharpness at `k = f`, the `c`-side:** the word `(e, f, 0)` — `e` `a`-edges and `f` `b`-edges
— decomposes the length `f·c`.  This is the `ScaleBreak` word; only the `γ`-trap kills it
(`SideNoB.side_no_b_uncond`), so `k < f` in `c_side_no_b` is exact. -/
theorem c_side_b_word_at_f (e f b : ℕ) (hef : e ≤ f) (hb : b + e ^ 2 = f ^ 2) :
    e * (e * f) + f * b + 0 * f ^ 2 = f * f ^ 2 := by
  have hz : (b : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hb
  have : (e : ℤ) * ((e : ℤ) * f) + (f : ℤ) * b + 0 * (f : ℤ) ^ 2 = (f : ℤ) * (f : ℤ) ^ 2 := by
    linear_combination (f : ℤ) * hz
  exact_mod_cast this

/-- **Sharpness at `k = f`, the `B`-side:** the word `(f−e, 0, f−e)` — `f−e` `a`-edges and `f−e`
`c`-edges, no `b` at all — decomposes the length `f·b`, so `k < f` in `b_side_rigid` is exact.
Arithmetic sharpness only: the word (the `j = 0` member of
`RogueMirror.base_side_wall_family`'s family) is **not** geometrically realizable —
`RogueMirror.wall_base_reading` (2026-08-15) forces the wall-scale base to `b^f` via the
`c`-side's `γ`-trap and the `α`-corner flank coupling, so the whole tower `k ≤ f` now reads
`b^k` on the `B`-side. -/
theorem b_side_alt_word_at_f (e f b : ℕ) (hef : e ≤ f) (hb : b + e ^ 2 = f ^ 2) :
    (f - e) * (e * f) + 0 * b + (f - e) * f ^ 2 = f * b := by
  have hz : (b : ℤ) + (e : ℤ) ^ 2 = (f : ℤ) ^ 2 := by exact_mod_cast hb
  have hz2 : ((f - e : ℕ) : ℤ) = (f : ℤ) - e := by
    push_cast [Nat.cast_sub hef]; ring
  have : ((f - e : ℕ) : ℤ) * ((e : ℤ) * f) + 0 * b + ((f - e : ℕ) : ℤ) * (f : ℤ) ^ 2
      = (f : ℤ) * b := by
    rw [hz2]; linear_combination (-(f : ℤ)) * hz
  exact_mod_cast this

end Erdos634.Inflation

#print axioms Erdos634.Inflation.a_side_no_b
#print axioms Erdos634.Inflation.b_side_rigid
#print axioms Erdos634.Inflation.c_side_no_b
#print axioms Erdos634.Inflation.c_side_words_scale
#print axioms Erdos634.Inflation.c_side_b_word_at_f
#print axioms Erdos634.Inflation.b_side_alt_word_at_f
