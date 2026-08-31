import Erdos634.VertexFigureReal

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

end Erdos634.RouteOne
