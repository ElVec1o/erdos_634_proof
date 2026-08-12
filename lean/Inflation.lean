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

end Erdos634.Inflation
