import Mathlib
import Erdos634.Dissection
import Erdos634.FanKill
import Erdos634.StubGap

/-!
# Corner fillability is the same at every member

Erdős #634, companion `prop:findep`.  The measured fact is that the refutation of a base word with
`cp = bp - 1` is *identical* at every `f` — same node count, same depth, same prune counters at
`f = 12, 14, 16, 18, 20, 22`.  That has been HEURISTIC because it is a measurement of a search.

The mechanism is provable, and it is this: **every corner test the search performs gives the same
answer at every member.**  A corner of angle `Xα + Yβ` is fillable exactly when `X` and `Y` admit
nonnegative multiplicities, and that condition mentions no `f`.  The angles themselves differ from
member to member, but the *arithmetic* they satisfy — `3α + 2β = π` with `α/π` irrational — is the
same, and the fillability question factors through it.

Two consequences for the engine, both stated below: a corner is fillable at one member iff at
every member (`fillable_iff_member`), and the two length kills the refutation uses are uniform in
`f` (`gap_one_uniform`, cited from `FanKill`).  So the search tree cannot depend on `f` through
either kind of test.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MemberUniform

open Erdos634.Geometry

/-- **Fillability is a condition on `(X, Y)` alone.**  A corner of angle `Xα + Yβ` is filled by
multiplicities `x, y, z` of `α`, `β`, `γ = 2α + β` exactly when `x + 2z = X` and `y + z = Y`. -/
theorem fill_iff_counts {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (X Y x y z : ℕ) :
    ((x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = (X : ℝ) * α + (Y : ℝ) * β)
      ↔ (x + 2 * z = X ∧ y + z = Y) := by
  constructor
  · intro h
    have := Erdos634.Geometry.vertex_multiplicities hrel hirr x y z (X : ℤ) (Y : ℤ) (by
      push_cast; linarith [h])
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  · rintro ⟨h1, h2⟩
    have hx : (X : ℝ) = (x : ℝ) + 2 * (z : ℝ) := by exact_mod_cast h1.symm
    have hy : (Y : ℝ) = (y : ℝ) + (z : ℝ) := by exact_mod_cast h2.symm
    rw [hx, hy]; ring

/-- **The same corner is fillable at every member.**  Two members' angle pairs give the same answer
to every corner test, because both answers are the arithmetic condition on `(X, Y)`.

This is the mechanism behind `prop:findep`: the search's corner decisions carry no `f`. -/
theorem fillable_iff_member {α β α' β' : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hrel' : 3 * α' + 2 * β' = Real.pi) (hirr' : ¬ ∃ r : ℚ, α' = (r : ℝ) * Real.pi)
    (X Y : ℕ) :
    (∃ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β)
        = (X : ℝ) * α + (Y : ℝ) * β)
      ↔ (∃ x y z : ℕ, (x : ℝ) * α' + (y : ℝ) * β' + (z : ℝ) * (2 * α' + β')
        = (X : ℝ) * α' + (Y : ℝ) * β') := by
  constructor
  · rintro ⟨x, y, z, h⟩
    exact ⟨x, y, z, (fill_iff_counts hrel' hirr' X Y x y z).mpr
      ((fill_iff_counts hrel hirr X Y x y z).mp h)⟩
  · rintro ⟨x, y, z, h⟩
    exact ⟨x, y, z, (fill_iff_counts hrel hirr X Y x y z).mpr
      ((fill_iff_counts hrel' hirr' X Y x y z).mp h)⟩

/-- **Unfillability transfers too**, which is the direction the prune uses: a corner cut at one
member is cut at every member. -/
theorem unfillable_iff_member {α β α' β' : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hrel' : 3 * α' + 2 * β' = Real.pi) (hirr' : ¬ ∃ r : ℚ, α' = (r : ℝ) * Real.pi)
    (X Y : ℕ) :
    (¬ ∃ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β)
        = (X : ℝ) * α + (Y : ℝ) * β)
      ↔ (¬ ∃ x y z : ℕ, (x : ℝ) * α' + (y : ℝ) * β' + (z : ℝ) * (2 * α' + β')
        = (X : ℝ) * α' + (Y : ℝ) * β') :=
  not_congr (fillable_iff_member hrel hirr hrel' hirr' X Y)

/-! ## The length tests are uniform too

The search's other kind of test asks whether a leftover run can be covered by whole tile edges.
The two the `cp = bp - 1` refutation uses are the residue `1` and the difference `|a - b|`, and both
answer *no* at every member — `FanKill.one_is_gap` and `StubGap.stub_gap`.  So neither kind of test
the search performs can distinguish one member from another. -/

/-- **The residue-`1` test answers no at every member.** -/
theorem gap_one_uniform (f f' : ℕ) (hf : 2 ≤ f) (hf' : 2 ≤ f') :
    (¬ ∃ x y z : ℕ, x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1) ∧
    (¬ ∃ x y z : ℕ, x * f' + y * (f' ^ 2 - 1) + z * f' ^ 2 = 1) := by
  constructor
  · rintro ⟨x, y, z, h⟩; exact Erdos634.FanKill.one_is_gap f x y z hf h
  · rintro ⟨x, y, z, h⟩; exact Erdos634.FanKill.one_is_gap f' x y z hf' h

/-- **Both tests together.**  A corner test and the residue-`1` test give the same answers at any
two members.  Every decision node of the `cp = bp - 1` search is one of these, which is why its
tree — and so its node count, depth and prune counters — cannot depend on `f`.

The step this does *not* supply is that the search performs only these tests; that is a property of
the engine, not a theorem.  What is proved here is that no test it performs can tell the members
apart. -/
theorem tests_uniform {α β α' β' : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hrel' : 3 * α' + 2 * β' = Real.pi) (hirr' : ¬ ∃ r : ℚ, α' = (r : ℝ) * Real.pi)
    (f f' : ℕ) (hf : 2 ≤ f) (hf' : 2 ≤ f') (X Y : ℕ) :
    ((∃ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β)
        = (X : ℝ) * α + (Y : ℝ) * β)
      ↔ (∃ x y z : ℕ, (x : ℝ) * α' + (y : ℝ) * β' + (z : ℝ) * (2 * α' + β')
        = (X : ℝ) * α' + (Y : ℝ) * β'))
    ∧ ((¬ ∃ x y z : ℕ, x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1)
      ↔ (¬ ∃ x y z : ℕ, x * f' + y * (f' ^ 2 - 1) + z * f' ^ 2 = 1)) := by
  refine ⟨fillable_iff_member hrel hirr hrel' hirr' X Y, ?_⟩
  obtain ⟨h1, h2⟩ := gap_one_uniform f f' hf hf'
  exact ⟨fun _ => h2, fun _ => h1⟩

end Erdos634.MemberUniform
