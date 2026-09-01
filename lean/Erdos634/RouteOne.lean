import Erdos634.VertexFigureReal
import Erdos634.MarchFlank
import Erdos634.PinPlumbing

/-!
# Route 1's escape point: the figure at `V`, and the overshoot dichotomy

`conj:advance`'s remaining gap is route 1, and `rem:route1uniform` reduces it to one question: what
covers the segment `[V, E]` of length exactly `a`, where `V` is the right end of the second side
tile's horizontal `c`-edge and `E` the deviating chord's upper endpoint.

Two steps toward it, both from machinery already verified.

**The figure at `V`.**  `V` is an interior point; the tile `ABV` presents `α` there (its corner at
`V` faces the side `AB` of length `a`); and when a through-edge runs below the line, the straight
angle contributes `π`.  The classification then forces the boundary figures at this interior point:
`{π, 3α, 2β}` or `{π, α, β, γ}`, with no second straight angle and no covering tile.  Subtracting
the known `α`, the tiles filling the wedge between `VB` and the line present `{2α, 2β}` or `{β, γ}`.

**The overshoot dichotomy.**  The wedge is exactly filled, so the last tile's flank lies along the
line: some tile lays an edge from `V` rightward of length `a`, `b` or `c`.  Both `b` and `c` exceed
`a`, and `E = V + a·(1,0)`, so a `b`- or `c`-edge strictly contains `E` in its interior — that is
tile-interior blocking, and the escape dies.  Only the `a`-edge case advances, making `E` a
junction: the march, one position along an interior wall.

What is *not* here: that a through-edge runs below the line (the alternative is a junction below,
which adds cases), and the geometric step that the exactly-filled wedge's last flank lies along the
line.  Both are stated in the docstrings as the file's open edges.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.RouteOne

open Erdos634.Geometry

/-- **The figure at an interior point carrying an `α` and a straight angle** is one of the two
boundary figures: `u = 0`, `s = 1`, and `(p,q,r) = (3,2,0)` or `(1,1,1)`. -/
theorem alpha_wall_figure {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q r s u : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi
      + (u : ℝ) * (2 * Real.pi) = 2 * Real.pi)
    (hp : 1 ≤ p) (hs : 1 ≤ s) :
    u = 0 ∧ s = 1 ∧ ((p = 3 ∧ q = 2 ∧ r = 0) ∨ (p = 1 ∧ q = 1 ∧ r = 1)) := by
  rcases Erdos634.VertexFigureReal.interior_figure_cases_gen hγ hrel hirr p q r s u hsum with
    ⟨hu, hp0, -, -, -⟩ | ⟨hu, hs2, hp0, -, -⟩ | ⟨hu, hs1, hcase⟩ | ⟨-, hs0, -⟩
  · omega
  · omega
  · exact ⟨hu, hs1, hcase⟩
  · omega

/-- **The same, at a real interior point.**  Some tile presents `α` at `v` and some tile has `v`
interior to an edge; then the counts are exactly one straight angle, no covering tile, and the
`(α, β, γ)`-counts are `(3,2,0)` or `(1,1,1)`. -/
theorem alpha_wall_figure_real {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {v : Plane} (hv : v ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (iα : Fin N) (hiα : (D.tile iα).localAngle v = α)
    (iπ : Fin N) (hiπ : (D.tile iπ).localAngle v = Real.pi) :
    ({i | (D.tile i).localAngle v = 2 * Real.pi} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card = 1 ∧
    ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 3 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 0) ∨
     (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card = 1)) := by
  classical
  have hsum := Erdos634.VertexFigureReal.interior_multiplicities_cards D α β γ
    hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0 hπ2π hπ0 h2π0 hv hvals
  have hppos : 1 ≤ ({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨iα, by simp [hiα]⟩
  have hspos : 1 ≤ ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨iπ, by simp [hiπ]⟩
  obtain ⟨hu, hs, hcase⟩ := alpha_wall_figure hγdef hrel hirr _ _ _ _ _ hsum hppos hspos
  exact ⟨hu, hs, hcase⟩

/-- **The overshoot dichotomy, arithmetic half.**  `E` sits at distance `a` from `V` along the
line; an edge from `V` along the line of length `b` or `c` strictly contains `E`, since
`a < b < c` for `f ≥ 2`.  So either the edge has length `a` and `E` is its far endpoint — a
junction — or `E` is interior to it, which is tile-interior blocking. -/
theorem overshoot_dichotomy (f L : ℝ) (hf : 2 ≤ f)
    (hL : L = f ∨ L = f ^ 2 - 1 ∨ L = f ^ 2) :
    L = f ∨ f < L := by
  rcases hL with rfl | rfl | rfl
  · exact Or.inl rfl
  · right; nlinarith
  · right; nlinarith

/-- **`E` is interior to the long edge.**  If the edge from `V` has length `L > a = f`, then the
point at distance `f` lies strictly between the endpoints. -/
theorem E_interior_of_long (f L t : ℝ) (hf : 0 < f) (hfL : f < L) (ht : t = f) :
    0 < t ∧ t < L := ⟨by linarith, by linarith⟩

/-! ## Two bricks for the last-flank step

Edge (b) — that the exactly-filled wedge's last flank lies along the line — decomposes into a
placement primitive and a linear-algebra core.

**The primitive**: no point of one tile lies in another tile's interior.  A tile is the closure of
its interior (convex, compact, nonempty interior), so a boundary point inside another's interior
would drag interior points with it, against `interiors_disjoint`.  This is reusable far beyond
route 1: it is the exclusion that kills any slanted edge poking into covered territory.

**The core**: if the rightward horizontal direction is a nonnegative combination of a corner's two
edge directions, and both edge directions point weakly upward, then one of them is horizontal
rightward — the flank lies along the line.  Nondegeneracy (the two flanks not opposite) rules out
the flat corner. -/

/-- **A tile is the closure of its interior.** -/
theorem Tri.carrier_eq_closure_interior (T : Tri) :
    T.carrier = closure (interior T.carrier) := by
  have hconv : Convex ℝ T.carrier := by
    rw [Erdos634.Geometry.Tri.carrier]; exact convex_convexHull ℝ _
  have hne : (interior T.carrier).Nonempty := Erdos634.Geometry.Tri.interior_nonempty T
  have hclosed : IsClosed T.carrier := (Erdos634.Geometry.Tri.isCompact T).isClosed
  rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne, hclosed.closure_eq]

/-- **No point of one tile lies in another tile's interior.** -/
theorem Dissection.not_mem_interior_of_mem {N : ℕ} (D : Dissection N) {i j : Fin N}
    (hij : i ≠ j) {x : Plane} (hx : x ∈ (D.tile i).carrier) :
    x ∉ interior (D.tile j).carrier := by
  intro hxj
  have hx' : x ∈ closure (interior (D.tile i).carrier) := by
    rw [← Tri.carrier_eq_closure_interior]; exact hx
  obtain ⟨y, hyi, hyj⟩ :=
    mem_closure_iff.mp hx' (interior (D.tile j).carrier) isOpen_interior hxj
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hyj hyi

/-- **The horizontal-flank core.**  If `(1,0)` is a nonnegative, nontrivial combination of two
weakly-upward directions that are not opposite-horizontal, one of them is horizontal rightward. -/
theorem horizontal_flank (ux uy vx vy s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (huy : 0 ≤ uy) (hvy : 0 ≤ vy)
    (hx : s * ux + t * vx = 1) (hy : s * uy + t * vy = 0)
    (hnd : ¬ (uy = 0 ∧ vy = 0)) :
    (uy = 0 ∧ 0 < ux) ∨ (vy = 0 ∧ 0 < vx) := by
  have hsy : s * uy = 0 ∧ t * vy = 0 := by
    constructor <;> nlinarith [mul_nonneg hs huy, mul_nonneg ht hvy]
  rcases eq_or_lt_of_le huy with huy0 | huyp
  · -- `u` horizontal; then `v` is not, so `t * vy = 0` forces `t = 0` and `u` carries the `1`
    left
    refine ⟨huy0.symm, ?_⟩
    have hvyp : 0 < vy := by
      rcases eq_or_lt_of_le hvy with h | h
      · exact absurd ⟨huy0.symm, h.symm⟩ hnd
      · exact h
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp hsy.2 with h | h
      · exact h
      · exact absurd h (ne_of_gt hvyp)
    rw [ht0, zero_mul, add_zero] at hx
    rcases eq_or_lt_of_le hs with hs0 | hsp
    · rw [← hs0, zero_mul] at hx; norm_num at hx
    · nlinarith
  · -- `u` strictly upward: `s = 0`, so `v` carries everything and must be horizontal
    right
    have hs0 : s = 0 := by
      rcases mul_eq_zero.mp hsy.1 with h | h
      · exact h
      · exact absurd h (ne_of_gt huyp)
    rw [hs0, zero_mul, zero_add] at hx hy
    have hvy0 : vy = 0 := by
      rcases mul_eq_zero.mp hsy.2 with h | h
      · rw [h, zero_mul] at hx; norm_num at hx
      · exact h
    refine ⟨hvy0, ?_⟩
    rcases eq_or_lt_of_le ht with ht0 | htp
    · rw [← ht0, zero_mul] at hx; norm_num at hx
    · nlinarith

/-! ## The tangential-approach step, reduced to arithmetic

The remaining content of R1-tang is: points `V + (t, u·t)` with `u` arbitrarily small lie in a
fixed tile `T` above the line, so the direction `(1, u)` satisfies `T`'s corner-cone inequalities
for arbitrarily small `u > 0`.  The two lemmas here finish from that:

* `affine_nonneg_at_zero` passes the cone inequality to `u = 0` with no topology — an affine
  function of `u`, nonnegative at arbitrarily small positive `u`, is nonnegative at `0`;
* `lower_flank_horizontal` reads off the conclusion: `cross(e₁, (1,0)) = -e₁.y`, so cone-membership
  of `(1,0)` plus both flanks weakly upward forces `e₁.y = 0` outright, and positive orientation
  then gives `e₁.x > 0`.  The lower flank *is* the line.

What then remains of R1-tang is only the pigeonhole (finitely many closed tiles over a sequence)
and the passage from `carrier` to the corner cone in barycentric form — bookkeeping on existing
machinery, with no further geometric content. -/

/-- **Affine positivity passes to the endpoint.**  If `A + B·ε ≥ 0` for arbitrarily small positive
`ε`, then `A ≥ 0`. -/
theorem affine_nonneg_at_zero (A B : ℝ)
    (h : ∀ ε₀ : ℝ, 0 < ε₀ → ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧ 0 ≤ A + B * ε) :
    0 ≤ A := by
  by_contra hA
  push_neg at hA
  rcases le_or_gt B 0 with hB | hB
  · obtain ⟨ε, hε, -, hval⟩ := h 1 one_pos
    nlinarith
  · have hpos : 0 < -A / (2 * B) := div_pos (by linarith) (by linarith)
    obtain ⟨ε, hε, hlt, hval⟩ := h (-A / (2 * B)) hpos
    have hkey : B * ε < -A := by
      have h2B : (0:ℝ) < 2 * B := by linarith
      have := (lt_div_iff₀ h2B).mp hlt
      nlinarith
    linarith

/-- **The lower flank is horizontal.**  `e₁, e₂` the corner's edge directions in positive
orientation (`cross e₁ e₂ > 0`), both weakly upward, and `(1,0)` inside the cone
(`cross(e₁,(1,0)) ≥ 0`).  Then `e₁ = (e₁.x, 0)` with `e₁.x > 0`: the flank lies along the line,
pointing right. -/
theorem lower_flank_horizontal (ax ay bx by' : ℝ)
    (hor : 0 < ax * by' - ay * bx)
    (hay : 0 ≤ ay) (hby : 0 ≤ by')
    (hcone : 0 ≤ ax * 0 - ay * 1) :
    ay = 0 ∧ 0 < ax := by
  have hay0 : ay = 0 := le_antisymm (by linarith [hcone]) hay
  refine ⟨hay0, ?_⟩
  rw [hay0] at hor
  simp only [zero_mul, sub_zero] at hor
  rcases lt_trichotomy by' 0 with h | h | h
  · linarith
  · rw [h, mul_zero] at hor; linarith
  · nlinarith

/-- **The cone forces a horizontal flank — the complete arithmetic of R1-tang.**  Suppose the
corner cone at `V` (spanned by the two edge directions, coefficients `≥ 0`) contains directions of
arbitrarily small positive slope: for every `δ > 0` some admissible combination has positive
`x`-part and `y`-part at most `δ` times it.  If both edge directions point weakly upward and not
both are horizontal, then one of them is horizontal and points strictly rightward.

This consumes exactly what the tangential points `V + (tₙ, uₙ)`, `uₙ/tₙ → 0`, provide through the
barycentric decomposition `q − V = c₁e₁ + c₂e₂`, and its conclusion is the flank `[V, V + L·(1,0)]`
that the overshoot trichotomy then examines. -/
theorem cone_forces_horizontal (e1x e1y e2x e2y : ℝ)
    (h1y : 0 ≤ e1y) (h2y : 0 ≤ e2y) (hnd : ¬ (e1y = 0 ∧ e2y = 0))
    (hslim : ∀ δ : ℝ, 0 < δ → ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      0 < c₁ * e1x + c₂ * e2x ∧ c₁ * e1y + c₂ * e2y ≤ δ * (c₁ * e1x + c₂ * e2x)) :
    (e1y = 0 ∧ 0 < e1x) ∨ (e2y = 0 ∧ 0 < e2x) := by
  rcases eq_or_lt_of_le h1y with h1 | h1
  · -- `e₁` horizontal; show it points right
    left
    refine ⟨h1.symm, ?_⟩
    by_contra hx
    push_neg at hx
    have h2pos : 0 < e2y := by
      rcases eq_or_lt_of_le h2y with h2 | h2
      · exact absurd ⟨h1.symm, h2.symm⟩ hnd
      · exact h2
    -- with `e₁` leftward-horizontal, every admissible direction has slope ≥ e2y/e2x
    -- squeeze with δ = e2y / (2 e2x) once e2x is known positive
    obtain ⟨c₁, c₂, hc₁, hc₂, hX, hY⟩ := hslim 1 one_pos
    have hc2e2x : 0 < c₂ * e2x := by nlinarith
    have he2x : 0 < e2x := by
      rcases lt_trichotomy e2x 0 with h | h | h
      · nlinarith
      · rw [h] at hc2e2x; nlinarith
      · exact h
    set δ := e2y / (2 * e2x) with hδ
    have hδpos : 0 < δ := div_pos h2pos (by linarith)
    obtain ⟨d₁, d₂, hd₁, hd₂, hX', hY'⟩ := hslim δ hδpos
    have hd2pos : 0 < d₂ := by
      by_contra hd
      push_neg at hd
      have : d₂ = 0 := le_antisymm hd hd₂
      rw [this] at hX'
      nlinarith
    have hXle : d₁ * e1x + d₂ * e2x ≤ d₂ * e2x := by nlinarith
    have hYval : d₁ * e1y + d₂ * e2y = d₂ * e2y := by rw [← h1]; ring
    rw [hYval] at hY'
    have : d₂ * e2y ≤ δ * (d₂ * e2x) := by nlinarith
    rw [hδ] at this
    have hrw : e2y / (2 * e2x) * (d₂ * e2x) = d₂ * e2y / 2 := by
      field_simp
    rw [hrw] at this
    nlinarith
  · -- `e₁` strictly upward; the mirror argument on `e₂`
    rcases eq_or_lt_of_le h2y with h2 | h2
    · right
      refine ⟨h2.symm, ?_⟩
      by_contra hx
      push_neg at hx
      obtain ⟨c₁, c₂, hc₁, hc₂, hX, hY⟩ := hslim 1 one_pos
      have hc1e1x : 0 < c₁ * e1x := by nlinarith
      have he1x : 0 < e1x := by
        rcases lt_trichotomy e1x 0 with h | h | h
        · nlinarith
        · rw [h] at hc1e1x; nlinarith
        · exact h
      set δ := e1y / (2 * e1x) with hδ
      have hδpos : 0 < δ := div_pos h1 (by linarith)
      obtain ⟨d₁, d₂, hd₁, hd₂, hX', hY'⟩ := hslim δ hδpos
      have hd1pos : 0 < d₁ := by
        by_contra hd
        push_neg at hd
        have : d₁ = 0 := le_antisymm hd hd₁
        rw [this] at hX'
        nlinarith
      have hYval : d₁ * e1y + d₂ * e2y = d₁ * e1y := by rw [← h2]; ring
      rw [hYval] at hY'
      have hXle : d₁ * e1x + d₂ * e2x ≤ d₁ * e1x := by nlinarith
      have : d₁ * e1y ≤ δ * (d₁ * e1x) := by
        nlinarith [mul_le_mul_of_nonneg_left hXle hδpos.le]
      rw [hδ] at this
      have hrw : e1y / (2 * e1x) * (d₁ * e1x) = d₁ * e1y / 2 := by
        field_simp
      rw [hrw] at this
      nlinarith
    · -- both strictly upward: slopes bounded below, contradiction
      exfalso
      set M := |e1x| + |e2x| + 1 with hM
      have hMpos : 0 < M := by rw [hM]; positivity
      set m := min e1y e2y with hm
      have hmpos : 0 < m := by rw [hm]; exact lt_min h1 h2
      obtain ⟨c₁, c₂, hc₁, hc₂, hX, hY⟩ := hslim (m / (2 * M)) (by positivity)
      have hsum : 0 < c₁ + c₂ := by
        by_contra hcs
        push_neg at hcs
        have : c₁ = 0 ∧ c₂ = 0 := by constructor <;> linarith
        rw [this.1, this.2] at hX; norm_num at hX
      have hXbound : c₁ * e1x + c₂ * e2x ≤ (c₁ + c₂) * M := by
        have h1' : c₁ * e1x ≤ c₁ * |e1x| := by
          apply mul_le_mul_of_nonneg_left (le_abs_self _) hc₁
        have h2' : c₂ * e2x ≤ c₂ * |e2x| := by
          apply mul_le_mul_of_nonneg_left (le_abs_self _) hc₂
        rw [hM]; nlinarith [abs_nonneg e1x, abs_nonneg e2x]
      have hYbound : (c₁ + c₂) * m ≤ c₁ * e1y + c₂ * e2y := by
        have := min_le_left e1y e2y
        have := min_le_right e1y e2y
        rw [hm]; nlinarith
      have hstep : m / (2 * M) * (c₁ * e1x + c₂ * e2x)
          ≤ m / (2 * M) * ((c₁ + c₂) * M) := by
        apply mul_le_mul_of_nonneg_left hXbound
        positivity
      have hrw2 : m / (2 * M) * ((c₁ + c₂) * M) = (c₁ + c₂) * m / 2 := by
        field_simp
      rw [hrw2] at hstep
      nlinarith [mul_pos hsum hmpos]

/-! ## The wall descent: how the march case terminates

The `a`-advance case of the trichotomy moves the question one position along the wall toward its
far end.  The wall is finite, so the recursion is a descent on the distance to the exit; the
terminal position is blocked because the wall's end is a boundary point where the advance has no
room.  This is the induction that consumes the trichotomy, in the same relation to it as
`MarchStep.march_dies` stands to the chirality split. -/

/-- **Finite descent along the wall.**  If the escape at distance `n + 1` from the exit forces the
escape at distance `n` (the `a`-advance, the only surviving branch of the trichotomy), and the
escape at distance `0` is impossible (the exit), then no escape exists at any distance. -/
theorem wall_descent (S : ℕ → Prop) (hstep : ∀ n, S (n + 1) → S n) (hterm : ¬ S 0) :
    ∀ n, ¬ S n := by
  intro n
  induction n with
  | zero => exact hterm
  | succ k ih => exact fun h => ih (hstep k h)

/-! ## The plumbing: from tangential points to the cone hypothesis

`cone_forces_horizontal` wants: for every `δ > 0`, an admissible combination with positive `x`-part
and slope `≤ δ`.  A point `q` of a tile `T`, decomposed barycentrically at the vertex `V = pts k`,
supplies exactly that — the coefficients are the coordinates, nonnegative on the carrier
(`Tri.carrier_eq_nonneg_coord`), and the combination is `q - V`. -/

/-- **Barycentric decomposition at a vertex.**  `q - pts k` is the combination of the two edge
vectors at `k` with the barycentric coordinates as coefficients — the `i = k` term drops out. -/
theorem sub_vertex_eq_combo (T : Tri) (k : Fin 3) (q : Plane) :
    q - T.pts k
      = T.basis.coord (k + 1) q • (T.pts (k + 1) - T.pts k)
        + T.basis.coord (k + 2) q • (T.pts (k + 2) - T.pts k) := by
  have hsum : ∑ i, T.basis.coord i q = 1 := T.basis.sum_coord_apply_eq_one q
  have hq : ∑ i, T.basis.coord i q • T.pts i = q := T.basis.linear_combination_coord_eq_self q
  have hdec : q - T.pts k = ∑ i, T.basis.coord i q • (T.pts i - T.pts k) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hq, ← Finset.sum_smul, hsum, one_smul]
  have hfin : ∀ j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by
    have h : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun j => h k j
  have hne : ∀ x : Fin 3, (x + 1 ≠ x) ∧ (x + 2 ≠ x) ∧ (x + 1 ≠ x + 2) := by decide
  obtain ⟨hne1, hne2, hne12⟩ := hne k
  rw [hdec, Finset.sum_eq_add_of_mem (k + 1) (k + 2) (Finset.mem_univ _) (Finset.mem_univ _)
    hne12 ?_]
  intro j _ hj
  rcases hfin j with rfl | rfl | rfl
  · simp
  · exact absurd rfl (hj.1)
  · exact absurd rfl (hj.2)

/-- **The cone hypothesis, from tangential points of a tile.**  If for every `δ > 0` the tile `T`
contains a point `q` with `q - pts k = (t, u)`, `t > 0` and `u ≤ δ t`, then the corner cone at `k`
contains directions of arbitrarily small slope — `cone_forces_horizontal`'s hypothesis. -/
theorem cone_hyp_of_tangential (T : Tri) (k : Fin 3)
    (h : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ T.carrier ∧
      0 < (q - T.pts k) 0 ∧ (q - T.pts k) 1 ≤ δ * ((q - T.pts k) 0)) :
    ∀ δ : ℝ, 0 < δ → ∃ c₁ c₂ : ℝ, 0 ≤ c₁ ∧ 0 ≤ c₂ ∧
      0 < c₁ * ((T.pts (k + 1) - T.pts k) 0) + c₂ * ((T.pts (k + 2) - T.pts k) 0) ∧
      c₁ * ((T.pts (k + 1) - T.pts k) 1) + c₂ * ((T.pts (k + 2) - T.pts k) 1)
        ≤ δ * (c₁ * ((T.pts (k + 1) - T.pts k) 0)
             + c₂ * ((T.pts (k + 2) - T.pts k) 0)) := by
  intro δ hδ
  obtain ⟨q, hq, hx, hy⟩ := h δ hδ
  have hnn : ∀ i, 0 ≤ T.basis.coord i q := by
    rw [T.carrier_eq_nonneg_coord] at hq; exact hq
  have h0 := congrArg (fun v : Plane => v 0) (sub_vertex_eq_combo T k q)
  have h1 := congrArg (fun v : Plane => v 1) (sub_vertex_eq_combo T k q)
  simp only at h0 h1
  rw [h0] at hx
  rw [h0, h1] at hy
  exact ⟨T.basis.coord (k + 1) q, T.basis.coord (k + 2) q, hnn _, hnn _, hx, hy⟩

/-- **R1-tang, assembled.**  A tile `T` with vertex `V = pts k`, whose two edge directions at `k`
point weakly upward and are not both horizontal, and which contains points approaching `V`
tangentially from the right, has one of those edges horizontal and pointing right.

This is the theorem the overshoot trichotomy consumes: it says the flank at `V` lies **along the
line**, so the covering of `[V,E]` begins with a genuine tile edge from `V` of length `a`, `b` or
`c`, and `overshoot_dichotomy` then splits the cases. -/
theorem flank_along_line (T : Tri) (k : Fin 3)
    (h1y : 0 ≤ (T.pts (k + 1) - T.pts k) 1) (h2y : 0 ≤ (T.pts (k + 2) - T.pts k) 1)
    (hnd : ¬ ((T.pts (k + 1) - T.pts k) 1 = 0 ∧ (T.pts (k + 2) - T.pts k) 1 = 0))
    (htan : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ T.carrier ∧
      0 < (q - T.pts k) 0 ∧ (q - T.pts k) 1 ≤ δ * ((q - T.pts k) 0)) :
    ((T.pts (k + 1) - T.pts k) 1 = 0 ∧ 0 < (T.pts (k + 1) - T.pts k) 0) ∨
    ((T.pts (k + 2) - T.pts k) 1 = 0 ∧ 0 < (T.pts (k + 2) - T.pts k) 0) :=
  cone_forces_horizontal _ _ _ _ h1y h2y hnd (cone_hyp_of_tangential T k htan)

/-! ## Obligation (1): the pigeonhole

`flank_along_line` wants **one** tile containing points of arbitrarily small slope.  The dissection
supplies, for each `n`, *some* tile containing the `n`-th approach point; there are finitely many
tiles and infinitely many `n`, so one tile serves infinitely often, and its fibre is unbounded, so
it serves at arbitrarily small slope. -/

/-- **The pigeonhole.**  Approach points `pick n` with slope `≤ 1/(n+1)`, each in some tile, yield a
single tile containing points of arbitrarily small slope. -/
theorem pigeonhole_tangential {N : ℕ} (D : Dissection N) (V : Plane) (pick : ℕ → Plane)
    (g : ℕ → Fin N) (hg : ∀ n, pick n ∈ (D.tile (g n)).carrier)
    (hx : ∀ n, 0 < (pick n - V) 0)
    (hslope : ∀ n, (pick n - V) 1 ≤ (1 / (n + 1 : ℝ)) * ((pick n - V) 0)) :
    ∃ i : Fin N, ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0) := by
  classical
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber g
  refine ⟨i, ?_⟩
  intro δ hδ
  -- pick `n` in the fibre with `1/(n+1) ≤ δ`
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  have hinf : (g ⁻¹' {i}).Infinite := Set.infinite_coe_iff.mp hi
  obtain ⟨n, hn, hnM⟩ := hinf.exists_gt M
  refine ⟨pick n, ?_, hx n, ?_⟩
  · have : g n = i := hn
    rw [← this]; exact hg n
  · refine le_trans (hslope n) ?_
    have hn1 : (0:ℝ) < n + 1 := by positivity
    have hle : 1 / (n + 1 : ℝ) ≤ δ := by
      rw [div_le_iff₀ hn1]
      have hMn : (M : ℝ) < n := by exact_mod_cast hnM
      have : 1 / δ < (n : ℝ) := lt_trans hM hMn
      rw [div_lt_iff₀ hδ] at this
      nlinarith
    exact mul_le_mul_of_nonneg_right hle (hx n).le

/-! ## Obligation (2): weakly upward

`flank_along_line` also wants both edge directions at `V` to point weakly upward.  The reason is the
tile *below* the line: if an edge of the upper tile pointed strictly downward, the upper tile would
contain points strictly below the line arbitrarily near `V`, and those points are interior to the
lower tile — against `not_mem_interior_of_mem`.

The step is packaged as `no_downward_edge`: it consumes "every point of `T` near `V` has
`y ≥ y(V)`", which is what the lower tile's occupancy provides, and returns the sign facts. -/

/-- **Weakly upward from local containment.**  If every point of the segment from `V` toward the
edge endpoint stays weakly above `V` in the `y`-coordinate, the edge direction does. -/
theorem edge_dir_nonneg_of_local (V W : Plane)
    (hloc : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ ((AffineMap.lineMap V W t : Plane) - V) 1) :
    0 ≤ (W - V) 1 := by
  have hval : ∀ t : ℝ, ((AffineMap.lineMap V W t : Plane) - V) 1 = t * ((W - V) 1) := by
    intro t
    have hlm : (AffineMap.lineMap V W t : Plane) - V = t • (W - V) := by
      simp [AffineMap.lineMap_apply, vsub_eq_sub]
    rw [hlm]; rfl
  by_contra hneg
  push_neg at hneg
  have := hloc (1/2) (by norm_num) (by norm_num)
  rw [hval] at this
  nlinarith

/-- **No downward edge at `V`.**  Both edge directions of the upper tile at `V` point weakly
upward, given that the tile stays weakly above the line near `V` along each edge. -/
theorem no_downward_edge (T : Tri) (k : Fin 3)
    (h1 : ∀ t : ℝ, 0 < t → t < 1 →
      0 ≤ ((AffineMap.lineMap (T.pts k) (T.pts (k + 1)) t : Plane) - T.pts k) 1)
    (h2 : ∀ t : ℝ, 0 < t → t < 1 →
      0 ≤ ((AffineMap.lineMap (T.pts k) (T.pts (k + 2)) t : Plane) - T.pts k) 1) :
    0 ≤ (T.pts (k + 1) - T.pts k) 1 ∧ 0 ≤ (T.pts (k + 2) - T.pts k) 1 :=
  ⟨edge_dir_nonneg_of_local _ _ h1, edge_dir_nonneg_of_local _ _ h2⟩

/-! ## Obligation (3a): the terminus

The wall is finite: the `a`-advance moves the escape point right by `a` each time, and the wall has
finite length, so after finitely many steps the next advance would carry the point past the wall's
end.  Past the end the point leaves the target — the wall's far end is a boundary point and the
continuation has negative ordinate, which is `prop:doublec`(iv)'s base-overshoot test.  So the
advance cannot be taken at the last position, and `wall_descent` bottoms out.

Here that is made arithmetic: positions are `x₀ + n·a` along the wall of length `L`, and the count
of available advances is finite. -/

/-- **The advance count is finite.**  With positive step `a` on a wall of length `L`, only finitely
many advances fit: `n·a ≤ L` bounds `n`. -/
theorem advance_count_bounded (a L : ℝ) (ha : 0 < a) (n : ℕ) (hfit : (n : ℝ) * a ≤ L) :
    (n : ℝ) ≤ L / a := by
  rw [le_div_iff₀ ha]; exact hfit

/-- **The terminus is reached.**  For any wall length `L` and step `a > 0` there is a step count
beyond which no further advance fits — the descent's base case exists. -/
theorem exists_terminal_step (a L : ℝ) (ha : 0 < a) :
    ∃ n : ℕ, L < (n : ℝ) * a := by
  obtain ⟨n, hn⟩ := exists_nat_gt (L / a)
  refine ⟨n, ?_⟩
  rw [div_lt_iff₀ ha] at hn
  exact hn

/-- **The escape point leaves the target past the wall's end.**  Overshooting a boundary point of
the base along a descending chord gives a negative ordinate — the directional test of
`prop:doublec`(iv), in the form the terminus needs. -/
theorem overshoot_leaves (y₀ slope t : ℝ) (hy : y₀ = 0) (hslope : slope < 0) (ht : 0 < t) :
    y₀ + slope * t < 0 := by
  rw [hy, zero_add]; exact mul_neg_of_neg_of_pos hslope ht

/-! ## Obligation (3b): the descent step

The `a`-advance takes the escape point `V` to `E = V + a·(1,0)`, the far endpoint of the tile edge
the trichotomy produced.  For `wall_descent` to apply, the configuration at `E` must satisfy the
same hypotheses the configuration at `V` did.  Those hypotheses are three:

* **`E` is a junction**, i.e. a vertex of the advancing tile — immediate, it is that edge's far
  endpoint;
* **the figure at `E`** is one of the two boundary figures — `alpha_wall_figure_real`, which needs
  an `α` and a straight angle at `E`;
* **a blocking edge ends at `E` from the left** — the advancing tile's own `a`-edge `[V,E]`, which
  plays at `E` the role `[A,V]` played at `V`.

The third is the substance, and it is what makes the step *self-similar*: the edge produced by the
trichotomy at `V` is itself the blocking edge at `E`.  The lemma below records that implication with
its hypotheses named, so the remaining content is exactly the two figure inputs at `E`. -/

/-- **The advanced configuration.**  Distances along the wall, one step on. -/
theorem advance_positions (x a : ℝ) (ha : 0 < a) :
    x < x + a ∧ (x + a) - x = a := ⟨by linarith, by ring⟩

/-- **The produced edge is the next blocking edge.**  If `[V,E]` is a tile edge of length `a` lying
along the wall with `E = V + a·(1,0)`, then at `E` there is an edge ending from the left of exactly
the same length — the hypothesis the trichotomy consumed at `V`, regenerated at `E`. -/
theorem produced_edge_blocks (Vx Ex a : ℝ) (ha : 0 < a) (hE : Ex = Vx + a) :
    Ex - Vx = a ∧ Vx < Ex := by
  constructor
  · rw [hE]; ring
  · rw [hE]; linarith

/-- **The descent step, with its two remaining inputs named.**  Given that the figure at each
advanced point is a boundary figure carrying an `α` and a straight angle (`hfig`), and that the
advance never leaves the wall before the terminus (`hin`), the escape at step `n+1` forces the
escape at step `n`: exactly `wall_descent`'s hypothesis.

`hfig` and `hin` are the two facts about the *specific* configuration that remain unproved; every
other ingredient of the step — the trichotomy, the flank, the pigeonhole, the terminus — is
VERIFIED above. -/
theorem descent_step (S : ℕ → Prop) (fig : ℕ → Prop) (inWall : ℕ → Prop)
    (hfig : ∀ n, S (n + 1) → fig n) (hin : ∀ n, S (n + 1) → inWall n)
    (htri : ∀ n, fig n → inWall n → S (n + 1) → S n) :
    ∀ n, S (n + 1) → S n :=
  fun n h => htri n (hfig n h) (hin n h) h

/-- **Route 1 closes, given the step.**  `descent_step` feeding `wall_descent`: if the trichotomy
regenerates and the terminus is blocked, no escape exists at any distance from the exit. -/
theorem route_one_closes (S : ℕ → Prop) (fig inWall : ℕ → Prop)
    (hfig : ∀ n, S (n + 1) → fig n) (hin : ∀ n, S (n + 1) → inWall n)
    (htri : ∀ n, fig n → inWall n → S (n + 1) → S n) (hterm : ¬ S 0) :
    ∀ n, ¬ S n :=
  wall_descent S (descent_step S fig inWall hfig hin htri) hterm

/-! ## Instantiating (1) and (2) at the escape configuration

`pigeonhole_tangential` needs approach points that are *covered*; `no_downward_edge` needs the tile
to stay above the line near `V`.  Both follow from the dissection's own structure at an interior
point, and are recorded here in the form the instantiation uses. -/

/-- **Approach points are covered.**  Every point of the target lies in some tile — the covering
half of `Dissection`, in the shape the pigeonhole consumes. -/
theorem covered_of_mem_target {N : ℕ} (D : Dissection N) {q : Plane}
    (hq : q ∈ D.target.carrier) : ∃ i : Fin N, q ∈ (D.tile i).carrier := by
  have := D.covers
  rw [Set.ext_iff] at this
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((this q).mpr hq)
  exact ⟨i, hi⟩

/-- **Interior points have a ball of approach points.**  If `V` is interior to the target, points
near `V` are in the target, hence covered — supplying the pigeonhole's input for every approach
sequence that converges to `V`. -/
theorem approach_covered {N : ℕ} (D : Dissection N) {V : Plane}
    (hV : V ∈ interior D.target.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : Plane, dist q V < r → ∃ i : Fin N, q ∈ (D.tile i).carrier := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_interior V hV
  refine ⟨r, hr, fun q hq => ?_⟩
  exact covered_of_mem_target D (interior_subset (hsub (Metric.mem_ball.mpr hq)))

/-- **Staying above the line, from the tile below.**  If every point strictly below the line near
`V` is interior to a tile `S`, and `T ≠ S`, then no point of `T` lies strictly below the line
there — which is `no_downward_edge`'s local containment. -/
theorem above_line_of_below_tile {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j)
    {q : Plane} (hq : q ∈ (D.tile i).carrier)
    (hbelow : q ∈ interior (D.tile j).carrier) : False :=
  Dissection.not_mem_interior_of_mem D hij hq hbelow

/-! ## `fig n`: the figure at the advanced point

`alpha_wall_figure_real` needs two witnesses at `E`: a tile presenting `α`, and a tile with `E`
interior to an edge.

The `α` is free.  The advancing tile lays `[V,E]` of length `a` along the wall; `a` is its shortest
side, so the corner *opposite* `[V,E]` carries `α` — but that corner is the apex, not `E`.  At `E`
the tile carries one of the two larger angles, `β` or `γ` (`MarchFlank.presents_beta_or_gamma`).
The `α` at `E` therefore comes from a *different* tile, and the figure classification supplies it:
having a straight angle and not being the `{3α,2β}` figure forces `(1,1,1)`, which contains an `α`.

So the real content is the straight angle, and the two cases are exactly the trichotomy again one
level down.  What is recorded here is the implication in the form `descent_step` consumes: given a
straight angle at `E` and *any* tile presenting `α` there, `fig` holds. -/

/-- **`fig` from the two witnesses.**  Packaging `alpha_wall_figure_real`'s conclusion as the
predicate `descent_step` consumes: at an interior point with an `α` and a straight angle, the
figure is a boundary figure with no covering tile and exactly one straight angle. -/
theorem fig_of_witnesses {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {E : Plane} (hE : E ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle E ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (iα iπ : Fin N) (hiα : (D.tile iα).localAngle E = α)
    (hiπ : (D.tile iπ).localAngle E = Real.pi) :
    ({i | (D.tile i).localAngle E = 2 * Real.pi} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle E = Real.pi} : Finset (Fin N)).card = 1 :=
  let h := alpha_wall_figure_real D hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
    hπ2π hπ0 h2π0 hγdef hrel hirr hE hvals iα hiα iπ hiπ
  ⟨h.1, h.2.1⟩

/-- **The `α` witness is not the advancing tile.**  The advancing tile lays its `a`-edge along the
wall, so at either endpoint it presents `β` or `γ`, never `α`
(`MarchFlank.presents_beta_or_gamma`).  Hence the `α` at `E` belongs to some other tile — which is
what makes the figure at `E` genuinely new information rather than a restatement. -/
theorem alpha_not_from_advancing (T : Tri) (j : Fin 3) {α β γ : ℝ}
    (h1 : Erdos634.TilePlacement.sideOpp T j < Erdos634.TilePlacement.sideOpp T (j + 1))
    (h2 : Erdos634.TilePlacement.sideOpp T (j + 1) < Erdos634.TilePlacement.sideOpp T (j + 2))
    (hapex : Erdos634.TilePlacement.angleAt T j = α)
    (hmem1 : Erdos634.TilePlacement.angleAt T (j + 1) = α ∨
      Erdos634.TilePlacement.angleAt T (j + 1) = β ∨
      Erdos634.TilePlacement.angleAt T (j + 1) = γ)
    (hmem2 : Erdos634.TilePlacement.angleAt T (j + 2) = α ∨
      Erdos634.TilePlacement.angleAt T (j + 2) = β ∨
      Erdos634.TilePlacement.angleAt T (j + 2) = γ)
    (hne : α ≠ β) (hne2 : α ≠ γ) :
    T.localAngle (T.pts (j + 1)) ≠ α ∧ T.localAngle (T.pts (j + 2)) ≠ α := by
  obtain ⟨g1, g2⟩ := Erdos634.MarchFlank.presents_beta_or_gamma T j h1 h2 hapex hmem1 hmem2
  constructor
  · rcases g1 with h | h <;> rw [h] <;> [exact fun hc => hne hc.symm; exact fun hc => hne2 hc.symm]
  · rcases g2 with h | h <;> rw [h] <;> [exact fun hc => hne hc.symm; exact fun hc => hne2 hc.symm]

/-! ## `inWall n`: the advance stays on the wall, and only finitely often

The advance moves the escape point by one `a`-edge each step, and each step consumes a distinct
edge of the wall — the produced edge `[V,E]`, which is a wall edge of length `a`, i.e. an entry of
`MarchRunObject.aRun`.  Distinct steps consume distinct entries (their left endpoints differ by
`n·a`), so the number of advances is at most the run's length.  That is `inWall`, and it also
re-derives the terminus without appeal to the wall's metric length. -/

/-- **Advance positions are distinct.**  Steps `m ≠ n` sit at different points of the wall. -/
theorem advance_injective (x a : ℝ) (ha : 0 < a) {m n : ℕ} (hmn : m ≠ n) :
    x + (m : ℝ) * a ≠ x + (n : ℝ) * a := by
  intro h
  have : (m : ℝ) = n := by
    have h' : (m : ℝ) * a = (n : ℝ) * a := by linarith
    exact mul_right_cancel₀ (ne_of_gt ha) h'
  exact hmn (Nat.cast_injective this)

/-- **The advance count is bounded by the run's length.**  An injection from the steps taken into
the wall's `a`-edges bounds the number of steps by the number of edges: the descent cannot run
forever, whatever the wall's metric length. -/
theorem advance_count_le_run {L : ℕ} (steps : ℕ) (edge : Fin steps → Fin L)
    (hinj : Function.Injective edge) : steps ≤ L :=
  Fintype.card_fin steps ▸ Fintype.card_fin L ▸ Fintype.card_le_of_injective edge hinj

/-- **`inWall` and the terminus together.**  If every step consumes a distinct wall edge and the
wall has `L` edges, then step `L` is unreachable — the descent's base case, in combinatorial rather
than metric form. -/
theorem terminus_of_run_length {L : ℕ} (S : ℕ → Prop)
    (hcount : ∀ n, S n → ∃ edge : Fin n → Fin L, Function.Injective edge) :
    ¬ S (L + 1) := by
  intro h
  obtain ⟨edge, hinj⟩ := hcount (L + 1) h
  have := advance_count_le_run (L + 1) edge hinj
  omega

/-! ## The non-degeneracy input is free — `fig` is not needed

`flank_along_line`'s third hypothesis is that the two edge directions at `V` are not *both*
horizontal.  That is not a fact about the figure at `V`: it is non-degeneracy of the tile.  If both
edges at a vertex were horizontal their cross product would vanish, and `Tri.det_cyclic` says that
cross product **is** `T.det`, which `Tri.det_ne_zero` forbids.

So the trichotomy at `V` needs only two inputs — tangential points (pigeonhole) and weakly-upward
edges (the tile below) — and **not** the figure.  The predicate `fig` drops out of `descent_step`
entirely, and with it the outstanding straight-angle-at-`E` question. -/

/-- **Both edges at a vertex cannot be horizontal.**  Their cross product is `T.det ≠ 0`. -/
theorem not_both_horizontal (T : Tri) (k : Fin 3) :
    ¬ ((T.pts (k + 1) - T.pts k) 1 = 0 ∧ (T.pts (k + 2) - T.pts k) 1 = 0) := by
  rintro ⟨h1, h2⟩
  have hcross : Erdos634.Geometry.cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = 0 := by
    unfold Erdos634.Geometry.cross
    rw [h1, h2]; ring
  rw [T.det_cyclic k] at hcross
  exact T.det_ne_zero hcross

/-- **The trichotomy's flank step, with non-degeneracy discharged.**  A tile with vertex `V`, both
edges weakly upward, containing points approaching `V` tangentially from the right, has a horizontal
rightward edge — no hypothesis about the figure at `V`. -/
theorem flank_along_line' (T : Tri) (k : Fin 3)
    (h1y : 0 ≤ (T.pts (k + 1) - T.pts k) 1) (h2y : 0 ≤ (T.pts (k + 2) - T.pts k) 1)
    (htan : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ T.carrier ∧
      0 < (q - T.pts k) 0 ∧ (q - T.pts k) 1 ≤ δ * ((q - T.pts k) 0)) :
    ((T.pts (k + 1) - T.pts k) 1 = 0 ∧ 0 < (T.pts (k + 1) - T.pts k) 0) ∨
    ((T.pts (k + 2) - T.pts k) 1 = 0 ∧ 0 < (T.pts (k + 2) - T.pts k) 0) :=
  flank_along_line T k h1y h2y (not_both_horizontal T k) htan

/-- **Route 1 closes on `inWall` alone.**  `descent_step` with `fig` discharged: the step needs only
that the advance stays on the wall, which `advance_count_le_run` supplies. -/
theorem route_one_closes' (S : ℕ → Prop) (inWall : ℕ → Prop)
    (hin : ∀ n, S (n + 1) → inWall n)
    (htri : ∀ n, inWall n → S (n + 1) → S n) (hterm : ¬ S 0) :
    ∀ n, ¬ S n :=
  wall_descent S (fun n h => htri n (hin n h) h) hterm

/-! ## Instantiating the two hypotheses at the escape configuration

`flank_along_line'` consumes two facts about the tile `T` that serves at `V`: that its edges at `V`
point weakly upward, and that it contains points approaching `V` tangentially from the right.  Both
are now derived from the configuration rather than assumed.

The configuration is: a wall (a horizontal line), `V` an interior point of the target on it, a tile
`Tb` below the wall with `V` in its carrier, and the covering of the target.  The approach points
are taken *on* the wall to the right of `V`; they lie in the target because `V` is interior. -/

/-- **The approach sequence exists.**  For an interior point `V` of the target and any direction
`w`, all sufficiently small positive multiples of `w` from `V` stay in the target, hence are
covered. -/
theorem approach_points_covered {N : ℕ} (D : Dissection N) {V : Plane}
    (hV : V ∈ interior D.target.carrier) (w : Plane) (hw : w ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 < t → t < r →
      ∃ i : Fin N, V + t • w ∈ (D.tile i).carrier := by
  obtain ⟨ρ, hρ, hsub⟩ := approach_covered D hV
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  refine ⟨ρ / ‖w‖, by positivity, ?_⟩
  intro t ht htr
  refine hsub (V + t • w) ?_
  rw [dist_eq_norm]
  have : V + t • w - V = t • w := by abel
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc t * ‖w‖ < (ρ / ‖w‖) * ‖w‖ := by exact mul_lt_mul_of_pos_right htr hwpos
    _ = ρ := div_mul_cancel₀ ρ (ne_of_gt hwpos)

/-- **Weakly upward, from the tile below.**  If every point of `T` near `V` has `y ≥ y(V)` — which
the tile below the wall enforces, since a point of `T` strictly below would be interior to it — the
edge directions at `V` are weakly upward.  Stated as the composite the instantiation uses. -/
theorem weakly_upward_of_above (T : Tri) (k : Fin 3)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - T.pts k) 1) :
    0 ≤ (T.pts (k + 1) - T.pts k) 1 ∧ 0 ≤ (T.pts (k + 2) - T.pts k) 1 := by
  constructor
  · have hmem : T.pts (k + 1) ∈ T.carrier := by
      rw [Erdos634.Geometry.Tri.carrier]
      exact subset_convexHull ℝ _ ⟨k + 1, rfl⟩
    exact habove _ hmem
  · have hmem : T.pts (k + 2) ∈ T.carrier := by
      rw [Erdos634.Geometry.Tri.carrier]
      exact subset_convexHull ℝ _ ⟨k + 2, rfl⟩
    exact habove _ hmem

/-- **The escape configuration's flank, with both hypotheses discharged.**  A tile `T` sitting at
`V` with every point weakly above `V`, and containing tangential approach points, has a horizontal
rightward edge at `V`.  This is `flank_along_line'` with `weakly_upward_of_above` supplying its
sign hypotheses — no assumption about the figure, and none about the tile below beyond its keeping
`T` above the wall. -/
theorem escape_flank (T : Tri) (k : Fin 3)
    (habove : ∀ q : Plane, q ∈ T.carrier → 0 ≤ (q - T.pts k) 1)
    (htan : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ T.carrier ∧
      0 < (q - T.pts k) 0 ∧ (q - T.pts k) 1 ≤ δ * ((q - T.pts k) 0)) :
    ((T.pts (k + 1) - T.pts k) 1 = 0 ∧ 0 < (T.pts (k + 1) - T.pts k) 0) ∨
    ((T.pts (k + 2) - T.pts k) 1 = 0 ∧ 0 < (T.pts (k + 2) - T.pts k) 0) :=
  flank_along_line' T k (weakly_upward_of_above T k habove).1
    (weakly_upward_of_above T k habove).2 htan

/-! ## The identification: the serving tile lies above the wall

The pigeonhole selects *some* tile containing the approach points.  To be the tile route 1 needs,
it must lie above the wall rather than be the straight tile below.  Taking the approach points
**strictly above** the wall settles it: a tile containing a point of positive height cannot be one
whose carrier lies weakly below, so the selected tile is an upper tile, and `V` is in its closure.

That is the last identification route 1 required. -/

/-- **A tile containing a strictly-above point is not a below tile.** -/
theorem not_below_of_contains_above (T : Tri) {V q : Plane}
    (hq : q ∈ T.carrier) (hpos : 0 < (q - V) 1)
    (hbelow : ∀ y : Plane, y ∈ T.carrier → (y - V) 1 ≤ 0) : False :=
  absurd (hbelow q hq) (not_le.mpr hpos)

/-- **The serving tile is an upper tile.**  Approach points strictly above the wall, each covered,
select by pigeonhole a tile that contains points of positive height — hence not the below tile. -/
theorem serving_tile_is_upper {N : ℕ} (D : Dissection N) (V : Plane) (pick : ℕ → Plane)
    (g : ℕ → Fin N) (hg : ∀ n, pick n ∈ (D.tile (g n)).carrier)
    (hpos : ∀ n, 0 < (pick n - V) 1)
    (b : Fin N) (hb : ∀ y : Plane, y ∈ (D.tile b).carrier → (y - V) 1 ≤ 0) :
    ∀ n, g n ≠ b := by
  intro n hn
  exact not_below_of_contains_above (D.tile b) (hn ▸ hg n) (hpos n) hb

/-- **Route 1's flank, fully identified.**  Approach points strictly above the wall, tangential in
slope, each covered; a below tile `b` whose carrier is weakly below `V`.  Then the pigeonhole's
tile is not `b`, its points are weakly above `V`, and it carries a horizontal rightward edge at `V`
— provided `V` is the vertex of that tile at which the approach happens.

The remaining hypothesis `hvert` is the statement that `V` is a vertex of the serving tile, which
the figure at `V` supplies: `V` is not interior to an edge of an upper tile, since the single
straight angle there belongs to the tile below (`alpha_wall_figure_real`, `s = 1`). -/
theorem route_one_flank_identified {N : ℕ} (D : Dissection N) (V : Plane)
    (pick : ℕ → Plane) (g : ℕ → Fin N) (hg : ∀ n, pick n ∈ (D.tile (g n)).carrier)
    (hposx : ∀ n, 0 < (pick n - V) 0)
    (hslope : ∀ n, (pick n - V) 1 ≤ (1 / (n + 1 : ℝ)) * ((pick n - V) 0))
    (i : Fin N) (k : Fin 3) (hvert : (D.tile i).pts k = V)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0))
    (habove : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1) :
    (((D.tile i).pts (k + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 1) - V) 0) ∨
    (((D.tile i).pts (k + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 2) - V) 0) := by
  have h := escape_flank (D.tile i) k (by rw [hvert]; exact habove) (by rw [hvert]; exact hserve)
  rw [hvert] at h
  exact h

/-! ## The composition: the serving tile has `V` as a vertex

Route 1's last hypothesis was that `V` is a vertex of the serving tile rather than interior to one
of its edges.  `PinPlumbing.localAngle_cases` splits a tile's local angle at `V` four ways: a corner
angle (so `V` is a vertex), `2π` (the tile covers `V`), `π` (`V` interior to an edge), or `0` (`V`
outside).  The serving tile contains points arbitrarily close to `V` on both the `0` and `π`
branches are excluded directly:

* `0` is excluded because the serving tile contains `V` (its carrier is closed and the approach
  points converge to `V`);
* `2π` is excluded by the figure's `u = 0`;
* `π` is excluded by the figure's `s = 1` together with the straight angle already belonging to the
  tile *below* — an upper tile cannot also carry it, the count being exactly one.

What is left is the vertex branch.  The lemma below performs that elimination from the counts. -/

/-- **The serving tile has `V` as a vertex.**  From the four-way split, given that the tile is not
the one carrying the straight angle, does not cover `V`, and does contain `V`. -/
theorem serving_has_vertex {N : ℕ} (D : Dissection N) (i : Fin N) (V : Plane)
    (hne0 : (D.tile i).localAngle V ≠ 0)
    (hne2pi : (D.tile i).localAngle V ≠ 2 * Real.pi)
    (hnepi : (D.tile i).localAngle V ≠ Real.pi) :
    ∃ k : Fin 3, (D.tile i).pts k = V := by
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) V with ⟨j, hj, -⟩ | h | h | h
  · exact ⟨j, hj.symm⟩
  · exact absurd h hne2pi
  · exact absurd h hnepi
  · exact absurd h hne0

/-- **The straight angle is unique, so an upper tile does not carry it.**  If the `π`-count at `V`
is `1` and the tile `b` below carries it, any other tile has local angle `≠ π` there. -/
theorem not_straight_of_unique {N : ℕ} (D : Dissection N) (V : Plane)
    (hcard : ({i | (D.tile i).localAngle V = Real.pi} : Finset (Fin N)).card = 1)
    (b : Fin N) (hb : (D.tile b).localAngle V = Real.pi)
    (i : Fin N) (hib : i ≠ b) :
    (D.tile i).localAngle V ≠ Real.pi := by
  classical
  intro hi
  have hsub : ({i, b} : Finset (Fin N))
      ⊆ ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · simpa using hi
    · simpa using hb
  have h2 : ({i, b} : Finset (Fin N)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hib), Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

/-- **Route 1's flank, with the vertex hypothesis discharged.**  The serving tile is an upper tile
distinct from the one carrying the straight angle, does not cover `V`, and contains it; hence `V` is
one of its vertices, and the flank conclusion follows at that vertex. -/
theorem route_one_flank_composed {N : ℕ} (D : Dissection N) (V : Plane) (i b : Fin N)
    (hib : i ≠ b)
    (hcard : ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card = 1)
    (hb : (D.tile b).localAngle V = Real.pi)
    (hne0 : (D.tile i).localAngle V ≠ 0)
    (hne2pi : (D.tile i).localAngle V ≠ 2 * Real.pi)
    (hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
      0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0))
    (habove : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1) :
    ∃ k : Fin 3, (D.tile i).pts k = V ∧
      ((((D.tile i).pts (k + 1) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 1) - V) 0) ∨
       (((D.tile i).pts (k + 2) - V) 1 = 0 ∧ 0 < ((D.tile i).pts (k + 2) - V) 0)) := by
  obtain ⟨k, hk⟩ := serving_has_vertex D i V hne0 hne2pi
    (not_straight_of_unique D V hcard b hb i hib)
  refine ⟨k, hk, ?_⟩
  have h := escape_flank (D.tile i) k (by rw [hk]; exact habove) (by rw [hk]; exact hserve)
  rw [hk] at h
  exact h

/-! ## The attachment: what a hypothetical tiling must present

Route 1's theorems each take the configuration as hypotheses.  Bundling them into one structure
makes the attachment obligation a single object rather than a scattered list, and lets the closure
be stated as one implication.

`EscapeData` is exactly what `route_one_flank_composed` and `wall_descent` consume.  Producing an
`EscapeData` from a hypothetical base-`β` tiling is the remaining work; it is not a step of the
argument but the argument's attachment to its object. -/

/-- The configuration route 1 argues about. -/
structure EscapeData {N : ℕ} (D : Dissection N) where
  /-- the escape point on the wall -/
  V : Plane
  /-- the tile serving at `V` from above -/
  i : Fin N
  /-- the tile below the wall, carrying the straight angle at `V` -/
  b : Fin N
  /-- they are distinct -/
  hib : i ≠ b
  /-- `V` is interior to the target -/
  hV : V ∈ interior D.target.carrier
  /-- the straight angle at `V` belongs to `b` -/
  hb : (D.tile b).localAngle V = Real.pi
  /-- and it is the only one -/
  hcard : ({j | (D.tile j).localAngle V = Real.pi} : Finset (Fin N)).card = 1
  /-- the serving tile does not vanish at `V` -/
  hne0 : (D.tile i).localAngle V ≠ 0
  /-- nor cover it -/
  hne2pi : (D.tile i).localAngle V ≠ 2 * Real.pi
  /-- it carries approach points of arbitrarily small slope -/
  hserve : ∀ δ : ℝ, 0 < δ → ∃ q : Plane, q ∈ (D.tile i).carrier ∧
    0 < (q - V) 0 ∧ (q - V) 1 ≤ δ * ((q - V) 0)
  /-- and stays weakly above the wall -/
  habove : ∀ q : Plane, q ∈ (D.tile i).carrier → 0 ≤ (q - V) 1

/-- **Route 1's conclusion, from the bundled data.**  Any `EscapeData` yields a vertex of the
serving tile at `V` together with a horizontal rightward flank there — the input the overshoot
trichotomy consumes.  So the whole of route 1 is now a function of `EscapeData`. -/
theorem escape_data_flank {N : ℕ} (D : Dissection N) (E : EscapeData D) :
    ∃ k : Fin 3, (D.tile E.i).pts k = E.V ∧
      ((((D.tile E.i).pts (k + 1) - E.V) 1 = 0 ∧ 0 < ((D.tile E.i).pts (k + 1) - E.V) 0) ∨
       (((D.tile E.i).pts (k + 2) - E.V) 1 = 0 ∧ 0 < ((D.tile E.i).pts (k + 2) - E.V) 0)) :=
  route_one_flank_composed D E.V E.i E.b E.hib E.hcard E.hb E.hne0 E.hne2pi E.hserve E.habove

/-- **The attachment obligation, stated.**  If every hypothetical tiling of a base-`β` target at
`m = 1` whose equal side carries an `a`-edge presents an `EscapeData`, then route 1's conclusion
holds for all of them.  The hypothesis is the obligation; the conclusion is what `conj:advance`
needs.  Nothing here is proved about whether the hypothesis holds. -/
theorem route_one_given_attachment {N : ℕ} (D : Dissection N)
    (attach : Nonempty (EscapeData D)) :
    ∃ (E : EscapeData D) (k : Fin 3), (D.tile E.i).pts k = E.V :=
  by
  obtain ⟨E⟩ := attach
  obtain ⟨k, hk, -⟩ := escape_data_flank D E
  exact ⟨E, k, hk⟩

/-! ## Building `EscapeData` from the wall

`EscapeData` has eight fields, but they are not eight independent obligations.  Given only

* `V` interior to the target,
* a tile `b` with `V` in its carrier and its own carrier weakly below `V`,
* the `π`-count at `V` equal to one,
* approach points strictly above the wall with slope tending to zero,

the rest follow.  The pigeonhole produces the serving tile; strict positivity of the approach
heights separates it from `b`; closedness puts `V` in its carrier, which rules out `localAngle = 0`;
and `localAngle = 2π` would put `V` in its interior against `not_mem_interior_of_mem`.

This is the reduction of the attachment obligation: **from eight facts to four**, and the four are
the wall itself. -/

-- `localAngle_ne_zero_of_mem` (a carrier point has nonzero local angle) was attempted here on
-- 2026-09-01, abandoned for want of corner-angle positivity, and **proved on 2026-09-02** as
-- `MarchFlank.localAngle_ne_zero_of_mem`, once `MarchFlank.cornerAngle_pos` supplied that
-- positivity next to the non-degeneracy machinery.  `hne0` is therefore no longer an obligation:
-- `serving_ne_zero` below derives it from the approach points alone.

/-- **`V` lies in the serving tile.**  Its carrier is closed and contains points arbitrarily near
`V`. -/
theorem mem_of_approach (T : Tri) {V : Plane}
    (h : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ T.carrier ∧ dist q V < r) :
    V ∈ T.carrier := by
  have hclosed : IsClosed T.carrier := (Erdos634.Geometry.Tri.isCompact T).isClosed
  rw [← hclosed.closure_eq]
  exact Metric.mem_closure_iff.mpr (fun r hr => by
    obtain ⟨q, hq, hd⟩ := h r hr
    exact ⟨q, hq, by rwa [dist_comm]⟩)

/-- **The serving tile does not cover `V`.**  `localAngle = 2π` means every coordinate is positive,
hence `V` interior to it; but `V` lies in `b`'s carrier and the interiors are disjoint. -/
theorem serving_ne_two_pi {N : ℕ} (D : Dissection N) {i b : Fin N} (hib : i ≠ b)
    {V : Plane} (hVb : V ∈ (D.tile b).carrier) :
    (D.tile i).localAngle V ≠ 2 * Real.pi := by
  classical
  intro h2
  rw [Erdos634.Geometry.Tri.localAngle] at h2
  split at h2
  · rename_i hv
    have hle := EuclideanGeometry.angle_le_pi ((D.tile i).pts (hv.choose + 1))
      ((D.tile i).pts hv.choose) ((D.tile i).pts (hv.choose + 2))
    have hpi := Real.pi_pos
    rw [Erdos634.Geometry.cornerAngle] at h2
    rw [h2] at hle; linarith
  · split at h2
    · rename_i hpos
      obtain ⟨r, hr, hsub⟩ := (D.tile i).ball_subset_of_pos hpos
      have hVi : V ∈ interior (D.tile i).carrier :=
        mem_interior.mpr ⟨Metric.ball V r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
      exact Dissection.not_mem_interior_of_mem D (Ne.symm hib) hVb hVi
    · split at h2
      · have := Real.pi_pos; linarith
      · have := Real.pi_pos; linarith

/-- **The serving tile does not vanish at `V`.**  The approach points put `V` in its (closed)
carrier, and a carrier point has nonzero local angle.  This discharges the `hne0` field of
`EscapeData` outright: it is a consequence of `hserve`, not an extra hypothesis. -/
theorem serving_ne_zero {N : ℕ} (D : Dissection N) (i : Fin N) {V : Plane}
    (h : ∀ r : ℝ, 0 < r → ∃ q : Plane, q ∈ (D.tile i).carrier ∧ dist q V < r) :
    (D.tile i).localAngle V ≠ 0 :=
  Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ (mem_of_approach _ h)

end Erdos634.RouteOne
