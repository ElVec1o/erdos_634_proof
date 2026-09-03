import Erdos634.CornerAnglePermCensus

/-!
# The base-`β` target's shape

Split out of `CornerAnglePerm.lean` (Lean rule 2.3's file-length guideline). `lem:census` and the
route-1 chain both take `htarget` — that each of the target's corners is `3α` or `β` — as a
hypothesis; this is not an independent assumption but the *isosceles* shape of the base-`β` target
(the two base corners carry `β`), together with the angle sum, proved here.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Geometry

/-! ## The base-`β` target's shape

`lem:census` and the route-1 chain both take `htarget` — that each of the target's corners is `3α` or
`β` — as a hypothesis.  It is not an independent assumption: it is the *isosceles* shape of the
base-`β` target, namely that the two base corners carry `β`, together with the angle sum. -/

/-- **The indexed corner angles sum to `π`.**  `cornerAngle_sum` in the `k`, `k+1`, `k+2` indexing,
for any starting index. -/
theorem cornerAngle_sum_indexed (T : Tri) (a : Fin 3) :
    cornerAngle (T.pts (a + 1)) (T.pts a) (T.pts (a + 2))
      + cornerAngle (T.pts (a + 1 + 1)) (T.pts (a + 1)) (T.pts (a + 1 + 2))
      + cornerAngle (T.pts (a + 2 + 1)) (T.pts (a + 2)) (T.pts (a + 2 + 2)) = Real.pi := by
  have hsum := Erdos634.Geometry.cornerAngle_sum T
  have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hall a with rfl | rfl | rfl <;>
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] <;>
    linarith [hsum]

/-- **`htarget` from the isosceles shape.**  If the two corners other than `a` carry `β`, then every
corner carries `3α` or `β` — the apex `a` carrying `π - 2β = 3α`.  This replaces the `htarget`
hypothesis of `congruentDissection_vertex_census` and of the route-1 chain by the base-`β` target's
defining shape. -/
theorem htarget_of_isosceles (T : Tri) {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (a : Fin 3)
    (h₁ : cornerAngle (T.pts (a + 1 + 1)) (T.pts (a + 1)) (T.pts (a + 1 + 2)) = β)
    (h₂ : cornerAngle (T.pts (a + 2 + 1)) (T.pts (a + 2)) (T.pts (a + 2 + 2)) = β) :
    ∀ k : Fin 3, cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = 3 * α ∨
      cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = β := by
  have hsum := cornerAngle_sum_indexed T a
  rw [h₁, h₂] at hsum
  have hidx : ∀ x : Fin 3, ∀ k : Fin 3, k = x ∨ k = x + 1 ∨ k = x + 2 := by decide
  intro k
  rcases hidx a k with rfl | rfl | rfl
  · exact Or.inl (by linarith)
  · exact Or.inr h₁
  · exact Or.inr h₂

/-- **The second base corner is free.**  Six files (`BaseDecomposition`, `BaseWalkGeneral`,
`GammaTrap`, `Realizable`, `TileAt`, `SideWalk`) carry `hcornerbase` at one corner and `hcornerapex`
at the next as separate hypotheses.  Given those two, the *third* corner is `β` as well: the angle
sum gives `π − β − 3α = β` by `hrel`.  So the target's isosceles shape is available at every one of
those call sites without assuming it. -/
theorem third_corner_of_base_apex (T : Tri) {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (k : Fin 3)
    (hbase : cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = β)
    (hapex : cornerAngle (T.pts (k + 1 + 1)) (T.pts (k + 1)) (T.pts (k + 1 + 2)) = 3 * α) :
    cornerAngle (T.pts (k + 2 + 1)) (T.pts (k + 2)) (T.pts (k + 2 + 2)) = β := by
  have hsum := cornerAngle_sum_indexed T k
  rw [hbase, hapex] at hsum
  linarith

/-- **`lem:census`, stated over the base-`β` target's own shape.**  The same conclusion as
`congruentDissection_vertex_census`, with the `htarget` disjunction replaced by what the paper
actually says about the target: it is isosceles with base angles `β`, the apex being the remaining
corner.  `htarget_of_isosceles` supplies the rest. -/
theorem congruentDissection_vertex_census_isosceles {N : ℕ} (D : CongruentDissection N)
    (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (a : Fin 3)
    (hbase₁ : cornerAngle (D.target.pts (a + 1 + 1)) (D.target.pts (a + 1))
      (D.target.pts (a + 1 + 2)) = β)
    (hbase₂ : cornerAngle (D.target.pts (a + 2 + 1)) (D.target.pts (a + 2))
      (D.target.pts (a + 2 + 2)) = β) :
    ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (0, 1, 3))).card
      = 1 + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (3, 2, 0))).card
        + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (4, 3, 1))).card
        + 2 * ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (6, 4, 0))).card :=
  congruentDissection_vertex_census D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
    hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr
    (htarget_of_isosceles D.target hrel a hbase₁ hbase₂)

/-- **`lem:apex`'s first clause: the apex angle is `π − 2β = 3α`.**  Immediate from the target's
isosceles shape and the angle sum.  The paper states this as a fact about the base-`β` target; here
it is derived from the target being isosceles with base angles `β`, rather than assumed. -/
theorem target_apex_angle (T : Tri) {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (a : Fin 3)
    (h₁ : cornerAngle (T.pts (a + 1 + 1)) (T.pts (a + 1)) (T.pts (a + 1 + 2)) = β)
    (h₂ : cornerAngle (T.pts (a + 2 + 1)) (T.pts (a + 2)) (T.pts (a + 2 + 2)) = β) :
    cornerAngle (T.pts (a + 1)) (T.pts a) (T.pts (a + 2)) = 3 * α := by
  have hsum := cornerAngle_sum_indexed T a
  rw [h₁, h₂] at hsum
  linarith

end Erdos634.Geometry
