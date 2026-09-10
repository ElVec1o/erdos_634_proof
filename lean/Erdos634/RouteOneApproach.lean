import Erdos634.RouteOne
import Erdos634.RouteOneVertexKill

/-!
# The approach sequence is not an obligation: `EscapeData` from interiority and the wall

**Status note (2026-09-11).**  `RouteOne.route_one_given_attachment` names the residue of Route 1 as
*"producing the below-tile `b`, `V` interior, and the approach sequence from a hypothetical base-`β`
tiling"*.  This file settles the third of those three, and settles it completely: **the approach
sequence is free.**  It is not an unbounded object that a hypothetical tiling must be shown to
supply; it is a consequence of `V ∈ interior D.target.carrier` and `Dissection.covers` alone.

**Rule 0.5, the mechanism is partly a rediscovery and that is stated first.**  The covering
ingredient already existed: `RouteOne.approach_covered` (2026-09-01) gives a radius `ρ > 0` inside
which every point is in some tile, and `RouteOne.approach_points_covered` specialises it to a ray.
Neither had **any** consumer anywhere in the corpus — the same orphan pattern that
`RouteOneVertexKill` found for `alpha_wall_figure_real`.  What is new here is not the covering fact
but the *composition*: an explicit sequence realising all five of `EscapeData.ofWall`'s sequence
hypotheses simultaneously, and the constructor that eliminates them.

What this establishes:

* `exists_approach_sequence` — from `V` interior alone, an explicit `pick`, `g` satisfying
  `hg`, `hx`, `hslope`, `hnear`, `hpos` of `RouteOne.EscapeData.ofWall`, **and** staying inside the
  interiority radius.  The sequence is `pick n = V + (t n, t n / (2(n+1)))` with
  `t n = min ρ (1/(n+1)) / 4`.  No hypothesis about tiles, walls, angles or the target's shape.

* `EscapeData.ofInterior` — `RouteOne.EscapeData.ofWall` with its five sequence hypotheses and its
  per-index `habove` replaced by a single **local** wall statement quantified over tiles:

      hwall : ∃ ρ > 0, ∀ j,
                (∃ q ∈ (D.tile j).carrier, 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
                (j = b ∨ ∀ q ∈ (D.tile j).carrier, 0 ≤ (q - V) 1)

  The `ρ` is **existential**, not universal: the statement is local to a neighbourhood of `V`, which
  is the weakest form that still feeds the constructor.  A universal `ρ` would say that *every* tile
  with a point up-and-right of `V` anywhere lies above `V`, which is false in general dissections.

  So the attachment obligation drops from *four* items to *three*: `V` interior, the below-tile `b`
  (with its straight angle, its containment of `V`, and its carrier weakly below), and the local
  wall.

* `EscapeData.ofInterior_vertex` — the same with `hcard` also gone, replaced by
  `RouteOneVertexKill`'s combinatorial vertex witness.  This is the exact composition of this
  session's two results: after it, **every** hypothesis of `EscapeData` that is analytic (a limit, a
  sequence, a metric count) has been eliminated, and what remains is a finite list of statements
  about *named tiles at a named point*.

**What is honestly still open, precisely.**  The residue of
`RouteOne.route_one_given_attachment` after this file is exactly:

1. `hV : V ∈ interior D.target.carrier` for `V = c·u + (c,0)` of `rem:route1uniform`.  This is a
   *finite* check: two strict linear inequalities in the target's coordinates.  It is not formalised
   here because the coordinate model of the base-`β` target at `(1,f)` is not connected to
   `Dissection` in this corpus (`BaseBetaWalks` works with words, not with a `Dissection`).
2. `b` with `(D.tile b).localAngle V = π`, `V ∈ (D.tile b).carrier`, and
   `hbelow : ∀ q ∈ (D.tile b).carrier, (q - V) 1 ≤ 0`.
3. `hwall`.

Items 2 and 3 are **one statement** — literally so: `hwall_disjunct_iff` proves that, given
`hbelow`, the `j = b` disjunct of `hwall` is never taken, so `EscapeData.ofInterior_plain` states the
obligation with the disjunct removed.  And it is the statement `conj:advance` already names as
unproved:
*"that a through-edge, rather than a junction, runs below the line at `V`"*
(`erdos-634-companion.tex`, `conj:advance`).  That is not a finite enumeration and this session's
techniques do not touch it; see the file-end note for why.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RouteOneApproach

open Erdos634.Geometry

/-! ## 1. A coordinate displacement in the plane -/

/-- The displacement with coordinates `(t, s)`. -/
noncomputable def disp (t s : ℝ) : Plane :=
  t • (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) + s • (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

@[simp] theorem disp_zero (t s : ℝ) : (disp t s) 0 = t := by
  simp [disp]

@[simp] theorem disp_one (t s : ℝ) : (disp t s) 1 = s := by
  simp [disp]

theorem norm_disp_le (t s : ℝ) : ‖disp t s‖ ≤ |t| + |s| := by
  refine le_trans (norm_add_le _ _) ?_
  simp [norm_smul, Real.norm_eq_abs]

theorem dist_disp (V : Plane) (t s : ℝ) : dist (V + disp t s) V = ‖disp t s‖ := by
  rw [dist_eq_norm]; congr 1; abel

/-! ## 2. The sequence

`t n = min ρ (1/(n+1)) / 4`, and the point is `V + (t n, t n / (2(n+1)))`. -/

/-- The horizontal step at index `n`. -/
noncomputable def step (ρ : ℝ) (n : ℕ) : ℝ := min ρ (1 / (n + 1 : ℝ)) / 4

theorem step_pos {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) : 0 < step ρ n := by
  have h : (0:ℝ) < 1 / (n + 1 : ℝ) := by positivity
  have : (0:ℝ) < min ρ (1 / (n + 1 : ℝ)) := lt_min hρ h
  unfold step; linarith

theorem step_le_rho {ρ : ℝ} (n : ℕ) : step ρ n ≤ min ρ (1 / (n + 1 : ℝ)) / 4 := le_of_eq rfl

/-! ## 3. The approach sequence exists, from interiority alone -/

/-- **The approach sequence is free.**  For any interior point `V` of the target there is a radius
`ρ > 0` and an explicit sequence of points of the dissection, right of `V`, strictly above `V`, with
slope at most `1/(n+1)`, distance to `V` less than both `1/(n+1)` and `ρ`.  These are exactly the
five sequence hypotheses of `RouteOne.EscapeData.ofWall`, and nothing about tiles, walls or angles
was used to produce them. -/
theorem exists_approach_sequence {N : ℕ} (D : Dissection N) {V : Plane}
    (hV : V ∈ interior D.target.carrier) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) :
    ∃ (pick : ℕ → Plane) (g : ℕ → Fin N),
      (∀ n, pick n ∈ (D.tile (g n)).carrier) ∧
      (∀ n, 0 < (pick n - V) 0) ∧
      (∀ n, (pick n - V) 1 ≤ (1 / (n + 1 : ℝ)) * ((pick n - V) 0)) ∧
      (∀ n, dist (pick n) V < 1 / (n + 1 : ℝ)) ∧
      (∀ n, 0 < (pick n - V) 1) ∧
      (∀ n, dist (pick n) V < ρ₀) := by
  classical
  obtain ⟨ρbig, hρbig, hcovbig⟩ := Erdos634.RouteOne.approach_covered D hV
  set ρ : ℝ := min ρbig ρ₀ with hρdef
  have hρ : 0 < ρ := lt_min hρbig hρ₀
  have hcov : ∀ q : Plane, dist q V < ρ → ∃ i : Fin N, q ∈ (D.tile i).carrier :=
    fun q hq => hcovbig q (lt_of_lt_of_le hq (min_le_left _ _))
  set pick : ℕ → Plane := fun n => V + disp (step ρ n) (step ρ n / (2 * (n + 1 : ℝ))) with hpick
  -- coordinates
  have hsub : ∀ n, pick n - V = disp (step ρ n) (step ρ n / (2 * (n + 1 : ℝ))) := by
    intro n; rw [hpick]; simp only; abel
  have hx : ∀ n, (pick n - V) 0 = step ρ n := by intro n; rw [hsub n]; simp
  have hy : ∀ n, (pick n - V) 1 = step ρ n / (2 * (n + 1 : ℝ)) := by intro n; rw [hsub n]; simp
  -- distance
  have hd : ∀ n, dist (pick n) V < min ρ (1 / (n + 1 : ℝ)) := by
    intro n
    have hs := step_pos hρ n
    have hn1 : (0:ℝ) < 2 * (n + 1 : ℝ) := by positivity
    have hbnd : ‖disp (step ρ n) (step ρ n / (2 * (n + 1 : ℝ)))‖
        ≤ |step ρ n| + |step ρ n / (2 * (n + 1 : ℝ))| := norm_disp_le _ _
    rw [hpick]; simp only
    rw [dist_disp]
    refine lt_of_le_of_lt hbnd ?_
    rw [abs_of_pos hs, abs_of_pos (by positivity)]
    have hhalf : step ρ n / (2 * (n + 1 : ℝ)) ≤ step ρ n / 2 := by
      apply div_le_div_of_nonneg_left hs.le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have hm : (0:ℝ) < min ρ (1 / (n + 1 : ℝ)) := lt_min hρ (by positivity)
    have : step ρ n = min ρ (1 / (n + 1 : ℝ)) / 4 := rfl
    linarith
  -- covering
  have hmem : ∀ n, ∃ i : Fin N, pick n ∈ (D.tile i).carrier := by
    intro n
    exact hcov (pick n) (lt_of_lt_of_le (hd n) (min_le_left _ _))
  choose g hg using hmem
  refine ⟨pick, g, hg, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; rw [hx n]; exact step_pos hρ n
  · intro n
    rw [hx n, hy n]
    have hs := step_pos hρ n
    have hn1 : (0:ℝ) < (n + 1 : ℝ) := by positivity
    have hrw : (1 / (n + 1 : ℝ)) * step ρ n = step ρ n / (n + 1 : ℝ) := by ring
    rw [hrw]
    exact div_le_div_of_nonneg_left hs.le hn1 (by linarith)
  · intro n; exact lt_of_lt_of_le (hd n) (min_le_right _ _)
  · intro n; rw [hy n]; exact div_pos (step_pos hρ n) (by positivity)
  · intro n
    have hle : ρ ≤ ρ₀ := by rw [hρdef]; exact min_le_right _ _
    exact lt_of_lt_of_le (lt_of_lt_of_le (hd n) (min_le_left _ _)) hle

/-! ## 4. `EscapeData` from interiority and a local wall

The five sequence hypotheses of `RouteOne.EscapeData.ofWall` disappear, and its per-index `habove`
becomes a statement about tiles rather than about a chosen sequence. -/

/-- **`EscapeData` with the approach sequence eliminated.**  The remaining hypotheses are: `V`
interior; the below-tile `b` (containing `V`, carrying the straight angle there, with carrier weakly
below); the straight-angle count; and a *local* wall statement — every tile with a point strictly
right of, strictly above, and within `ρ` of `V` is either `b` or lies weakly above `V`.

This is the reduction of the attachment obligation from four items to three. -/
theorem EscapeData.ofInterior {N : ℕ} (D : Dissection N) (V : Plane) (b : Fin N)
    (hV : V ∈ interior D.target.carrier)
    (hVb : V ∈ (D.tile b).carrier)
    (hb : (D.tile b).localAngle V = Real.pi)
    (hcard : ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card = 1)
    (hbelow : ∀ q : Plane, q ∈ (D.tile b).carrier → (q - V) 1 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ j : Fin N,
      (∃ q : Plane, q ∈ (D.tile j).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      (j = b ∨ ∀ q : Plane, q ∈ (D.tile j).carrier → 0 ≤ (q - V) 1)) :
    Nonempty (Erdos634.RouteOne.EscapeData D) := by
  obtain ⟨ρ, hρ, hw⟩ := hwall
  obtain ⟨pick, g, hg, hx, hslope, hnear, hpos, hin⟩ := exists_approach_sequence D hV ρ hρ
  refine Erdos634.RouteOne.EscapeData.ofWall D V b hV hVb hb hcard hbelow pick g hg hx hslope
    hnear hpos ?_
  intro n q hq
  rcases hw (g n) ⟨pick n, hg n, hx n, hpos n, hin n⟩ with h | h
  · exact Or.inr h
  · exact Or.inl (h q hq)

/-- **The same, with `hcard` discharged by a vertex witness.**  Composed with
`RouteOneVertexKill.card_straight_eq_one_of_vertex`: the straight-angle count is no longer assumed
but derived from the purely combinatorial statement that *some* dissection edge ends at `V` — which
`rem:route1uniform` supplies definitionally, `V` being the third vertex of the second side tile.

After this theorem no hypothesis of `EscapeData` is analytic: no limit, no sequence, no metric
count.  Everything left is a statement about named tiles at the named point `V`. -/
theorem EscapeData.ofInterior_vertex {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (V : Plane) (b : Fin N)
    (hV : V ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle V ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (jc : Fin N) (hjc : ∃ k : Fin 3, (D.tile jc).pts k = V)
    (hVb : V ∈ (D.tile b).carrier)
    (hb : (D.tile b).localAngle V = Real.pi)
    (hbelow : ∀ q : Plane, q ∈ (D.tile b).carrier → (q - V) 1 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ j : Fin N,
      (∃ q : Plane, q ∈ (D.tile j).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      (j = b ∨ ∀ q : Plane, q ∈ (D.tile j).carrier → 0 ≤ (q - V) 1)) :
    Nonempty (Erdos634.RouteOne.EscapeData D) := by
  obtain ⟨hcard, -⟩ := Erdos634.RouteOneVertexKill.card_straight_eq_one_of_vertex D
    hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hγdef hrel hirr
    hV hvals jc hjc b hb
  exact EscapeData.ofInterior D V b hV hVb hb hcard hbelow hwall

/-- **Route 1's conclusion, with the analytic layer gone.**  The composition of everything above
with `RouteOne.route_one_given_attachment`: from `V` interior, a vertex witness at `V`, and the
below-tile-plus-local-wall data, Route 1's flank conclusion holds.  Compare
`RouteOne.route_one_given_attachment`, whose hypothesis was the whole of `EscapeData`. -/
theorem route_one_given_wall {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (V : Plane) (b : Fin N)
    (hV : V ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle V ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (jc : Fin N) (hjc : ∃ k : Fin 3, (D.tile jc).pts k = V)
    (hVb : V ∈ (D.tile b).carrier)
    (hb : (D.tile b).localAngle V = Real.pi)
    (hbelow : ∀ q : Plane, q ∈ (D.tile b).carrier → (q - V) 1 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ j : Fin N,
      (∃ q : Plane, q ∈ (D.tile j).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      (j = b ∨ ∀ q : Plane, q ∈ (D.tile j).carrier → 0 ≤ (q - V) 1)) :
    ∃ (E : Erdos634.RouteOne.EscapeData D) (k : Fin 3), (D.tile E.i).pts k = E.V :=
  Erdos634.RouteOne.route_one_given_attachment D
    (EscapeData.ofInterior_vertex D hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
      hπ2π hπ0 h2π0 hγdef hrel hirr V b hV hvals jc hjc hVb hb hbelow hwall)

/-! ### The `j = b` disjunct in `hwall` is redundant

`hbelow` says every point of the below-tile has `y ≤ y(V)`, so the below-tile can never supply the
antecedent's point, which is *strictly* above `V`.  Hence the disjunct is never taken, and `hwall`
is equivalent to the plain statement "every tile with a point strictly up-and-right of `V` within
`ρ` lies weakly above `V`".  This is what makes `hwall` and `hbelow` one obligation rather than two
and shows the bundle is not disjunctively hedged. -/

/-- **The below-tile supplies no strictly-above point.** -/
theorem below_no_upper_point {N : ℕ} (D : Dissection N) (V : Plane) (b : Fin N) (ρ : ℝ)
    (hbelow : ∀ q : Plane, q ∈ (D.tile b).carrier → (q - V) 1 ≤ 0) :
    ¬ ∃ q : Plane, q ∈ (D.tile b).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ := by
  rintro ⟨q, hq, -, hpos, -⟩
  exact absurd (hbelow q hq) (not_le.mpr hpos)

/-- **The disjunct is redundant.**  Given `hbelow`, the disjunctive local wall statement is
*equivalent* to the plain one. -/
theorem hwall_disjunct_iff {N : ℕ} (D : Dissection N) (V : Plane) (b : Fin N) (ρ : ℝ)
    (hbelow : ∀ q : Plane, q ∈ (D.tile b).carrier → (q - V) 1 ≤ 0) :
    (∀ j : Fin N,
      (∃ q : Plane, q ∈ (D.tile j).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      (j = b ∨ ∀ q : Plane, q ∈ (D.tile j).carrier → 0 ≤ (q - V) 1)) ↔
    (∀ j : Fin N,
      (∃ q : Plane, q ∈ (D.tile j).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      ∀ q : Plane, q ∈ (D.tile j).carrier → 0 ≤ (q - V) 1) := by
  constructor
  · intro h j hj
    rcases h j hj with heq | h'
    · rw [heq] at hj; exact absurd hj (below_no_upper_point D V b ρ hbelow)
    · exact h'
  · intro h j hj; exact Or.inr (h j hj)

/-- **`EscapeData` from interiority and the plain local wall.**  `ofInterior` with the redundant
disjunct removed: the whole remaining obligation is now `hV`, the below-tile `b`, and

    ∃ ρ > 0, every tile with a point strictly right of and strictly above `V` within `ρ`
             lies weakly above `V`. -/
theorem EscapeData.ofInterior_plain {N : ℕ} (D : Dissection N) (V : Plane) (b : Fin N)
    (hV : V ∈ interior D.target.carrier)
    (hVb : V ∈ (D.tile b).carrier)
    (hb : (D.tile b).localAngle V = Real.pi)
    (hcard : ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card = 1)
    (hbelow : ∀ q : Plane, q ∈ (D.tile b).carrier → (q - V) 1 ≤ 0)
    (hwall : ∃ ρ : ℝ, 0 < ρ ∧ ∀ j : Fin N,
      (∃ q : Plane, q ∈ (D.tile j).carrier ∧ 0 < (q - V) 0 ∧ 0 < (q - V) 1 ∧ dist q V < ρ) →
      ∀ q : Plane, q ∈ (D.tile j).carrier → 0 ≤ (q - V) 1) :
    Nonempty (Erdos634.RouteOne.EscapeData D) := by
  obtain ⟨ρ, hρ, hw⟩ := hwall
  exact EscapeData.ofInterior D V b hV hVb hb hcard hbelow
    ⟨ρ, hρ, (hwall_disjunct_iff D V b ρ hbelow).mpr hw⟩

/-! ## 5. Non-vacuity of the sequence layer

A constructor whose hypotheses cannot be met proves nothing.  `exists_approach_sequence` has one
hypothesis, `V ∈ interior D.target.carrier`, and it is met by any dissection with a nonempty target
interior; the theorem below records that its *output* — the five-fold conjunction — is genuinely
inhabited rather than vacuously derived, by exhibiting the concrete numbers at `n = 0`, `ρ = 1`. -/

/-- At `ρ = 1`, `n = 0` the constructed point sits at `(1/4, 1/8)` relative to `V`: strictly right,
strictly above, slope `1/2 ≤ 1`, distance `< 1`.  The sequence layer is not vacuous. -/
theorem approach_witness :
    step 1 0 = 1 / 4 ∧ step 1 0 / (2 * (0 + 1 : ℝ)) = 1 / 8 ∧
      (1 / 8 : ℝ) ≤ (1 / (0 + 1 : ℝ)) * (1 / 4) ∧ (0 : ℝ) < 1 / 8 := by
  refine ⟨by norm_num [step], by norm_num [step], by norm_num, by norm_num⟩

/-! ## 6. What this does *not* do, dated 2026-09-11

The residue of `RouteOne.route_one_given_attachment` after this file is `hV`, the below-tile data
(`hVb`, `hb`, `hbelow`) and `hwall`.  Of these:

* `hV` is a finite check once the base-`β` target is presented as a `Dissection` with coordinates.
  That presentation does not exist in this corpus and is real work, but it is bounded work.

**CORRECTED 2026-09-11 (later, same day) — read `RouteOneWallOnly.lean` before using the note
below.**  The identification of `hbelow` with `conj:advance`'s clause (a) is an artefact of the
vehicle: `RouteOne.EscapeData` carries the below-tile `b`, `hb` and `hcard` as *fields*, so every
theorem routed through it inherits them.  `RouteOneWallOnly.flank_from_wall_only` reaches the same
flank conclusion at `V` with **no below-tile at any position** — `b`, `hVb`, `hb`, `hcard` and
`hbelow` are all absent — by composing `exists_approach_sequence` with
`RouteOne.route_one_flank_from_configuration` (2026-09-09), which `lean/PAPER_MAP.md` already
records as removing clause (a) at the flank step.  What survives of the residue is `hwall` alone,
a statement about tiles *above* the line.  The paragraph below overstates the obligation and is
kept only for the record.

* `hbelow` **and** `hwall` are the same statement in two places, and it is the one `conj:advance`
  records as unproved: *a through-edge, rather than a junction, runs below the line at `V`.*  It is
  not a finite enumeration.  It is a statement about **which** tile occupies the region immediately
  below the horizontal line through `V` in a hypothetical tiling, and the set of candidate
  occupants is not bounded by the local vertex figure: `RouteOneVertexKill.straight_dichotomy`
  constrains the *angles* at `V` but says nothing about which tile of the `N` carries the straight
  angle, nor about the extent of its carrier away from `V`.  Both the corner-witness technique of
  `RouteOneVertexKill` (which is local to the vertex figure at a single point) and the clearance
  technique of `EpredWedgeClearance` (which computes placement windows relative to a **base corner**
  of the target, using `cot β` of the target's apex angle) act on data this statement does not
  involve: the first sees only angles at `V`, the second only distances along the base.  Neither
  bounds the below-tile.
-/

end Erdos634.RouteOneApproach
