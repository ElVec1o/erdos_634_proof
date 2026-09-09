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

/-- **`lem:parity` (Straight-figure parity), for a real congruent dissection.**  Write
`S = n₁ + n₂` for the total number of straight (`π`) figures — the classes `{α,β,γ}` (label
`(1,1,1)`) and `{3α,2β}` (label `(3,2,0)`).  Then `S ≡ N + 1 (mod 2)`.

This is `Frontier.census_parity`'s arithmetic, with its hypothesis — the census `α`-identity
`3 + n₁ + 3n₂ + 2v₂ + 4v₃ + 6v₄ = N` — discharged for a real dissection by `census_alpha_sum`
together with `apex_fibre_card` (the apex fibre is a single point, the constant `3`) and
`base_fibre_card` (the base-corner fibre has two points, contributing `0` to the `α`-count). -/
theorem congruentDissection_straight_parity {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα2π : α ≠ 2 * Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ2π : β ≠ 2 * Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ2π : γ ≠ 2 * Real.pi) (hγ0 : γ ≠ 0)
    (hπ2π : Real.pi ≠ 2 * Real.pi) (hπ0 : Real.pi ≠ 0) (h2π0 : 2 * Real.pi ≠ 0)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (htarget : ∀ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = 3 * α ∨
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β) :
    (((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (1, 1, 1))).card
      + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (3, 2, 0))).card + N) % 2 = 1 := by
  classical
  have ha := census_alpha_sum D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
      hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  have hap := apex_fibre_card D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
      hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  have hba := base_fibre_card D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
      hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  simp only [censusLabels, Prod.mk.injEq] at ha ⊢
  simp only [Prod.mk.injEq] at hap hba
  norm_num at ha hap hba ⊢
  omega

/-- **`lem:parity` over the base-`β` target's own shape.**  Same conclusion as
`congruentDissection_straight_parity`, with the `htarget` disjunction replaced by the target being
isosceles with base angles `β` — the paper's own description of the base-`β` target. -/
theorem congruentDissection_straight_parity_isosceles {N : ℕ} (D : CongruentDissection N)
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
    (((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (1, 1, 1))).card
      + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (3, 2, 0))).card + N) % 2 = 1 :=
  congruentDissection_straight_parity D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
    hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr
    (htarget_of_isosceles D.target hrel a hbase₁ hbase₂)

/-- **`lem:census` (The vertex census), as a single statement, for a real congruent dissection of
the base-`β` target.**  Assembles the four clauses of the paper's lemma into one theorem, so that
the match against the paper text is a single comparison rather than a survey of ingredients:

1. *the corner fills* — "the base corners fill uniquely as `{β}` and the apex as `{3α}`":
   the apex `D.target.pts a` carries `(3,0,0)` and each base corner `D.target.pts (a+1)`,
   `D.target.pts (a+2)` carries `(0,1,0)` (`TileAt.congruentDissection_apex_counts` /
   `.congruentDissection_base_corner_counts`);
2. *the identity* — `v₁ = 1 + n₂ + v₃ + 2v₄` (`congruentDissection_vertex_census_isosceles`);
3. *"in particular `v₁ ≥ 1`"* (`congruentDissection_climber_mandatory`).

The target hypothesis is the base-`β` target's own shape: isosceles with base angles `β` at the two
corners other than `a`, the apex angle `3α` then being forced (`target_apex_angle`).

The lemma's remaining sentence — "it is also the *entire* content of corner counting: the three
balance equations admit exactly one relation" — is `OrderForcing.census_gamma_dependent` /
`.census_single_relation`, a statement about the abstract linear system rather than about `D`, and
so is not a conjunct here. -/
theorem congruentDissection_census_isosceles {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
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
    (({i | (D.tile i).localAngle (D.target.pts a) = α} : Finset (Fin N)).card = 3 ∧
      ({i | (D.tile i).localAngle (D.target.pts a) = β} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle (D.target.pts a) = γ} : Finset (Fin N)).card = 0) ∧
    (({i | (D.tile i).localAngle (D.target.pts (a + 1)) = α} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle (D.target.pts (a + 1)) = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle (D.target.pts (a + 1)) = γ} : Finset (Fin N)).card = 0) ∧
    (({i | (D.tile i).localAngle (D.target.pts (a + 2)) = α} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle (D.target.pts (a + 2)) = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle (D.target.pts (a + 2)) = γ} : Finset (Fin N)).card = 0) ∧
    ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (0, 1, 3))).card = 1 + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (3, 2, 0))).card + ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (4, 3, 1))).card + 2 * ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (6, 4, 0))).card ∧
    1 ≤ ((cornerPts D.toDissection).filter (fun v =>
      ((({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card,
        ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card) : ℕ × ℕ × ℕ)
        = (0, 1, 3))).card := by
  have htarget := htarget_of_isosceles D.target hrel a hbase₁ hbase₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ :=
      Erdos634.Geometry.Dissection.congruentDissection_apex_counts D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
        hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ a (target_apex_angle D.target hrel a hbase₁ hbase₂)
    exact ⟨h1, h2, h3⟩
  · obtain ⟨h1, h2, h3, -⟩ :=
      Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D α β γ hαβ hαγ hαπ hα0 hβγ
        hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ (a + 1) hbase₁
    exact ⟨h1, h2, h3⟩
  · obtain ⟨h1, h2, h3, -⟩ :=
      Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts D α β γ hαβ hαγ hαπ hα0 hβγ
        hβπ hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hmα hmβ hmγ (a + 2) hbase₂
    exact ⟨h1, h2, h3⟩
  · exact congruentDissection_vertex_census D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
      hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget
  · exact congruentDissection_climber_mandatory D α β γ hαβ hαγ hαπ hα2π hα0 hβγ hβπ hβ2π hβ0 hγπ hγ2π hγ0
      hπ2π hπ0 h2π0 hmα hmβ hmγ hγdef hrel hirr htarget

end Erdos634.Geometry
