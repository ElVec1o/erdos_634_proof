import Mathlib.Tactic

/-!
# Coset propagation along a connected adjacency (Erdős #634, the skeleton of DL-2c)

`prop:gammagrading` (companion) has two halves. The algebraic half — that `α` and `β` generate
`⟨γ⟩`, since `α ≡ 2γ` and `β ≡ −3γ` and `gcd(2,3) = 1` — is already machine-checked in
`LabelCalculus.lean` (`gamma_generates`). The other half is a propagation argument:

> a tile's three directions are `θ, θ−α, θ−α−β`, a translate of a fixed set; two tiles sharing a
> boundary segment share a direction, so their offsets differ by an element of `⟨α,β⟩`; the tile
> adjacency graph is connected, so all offsets lie in one coset.

The geometry there is the *first* clause (what a tile's directions are, and that adjacent tiles share
one). The rest is pure combinatorics, and that is what this file isolates and proves: **on a
connected adjacency, a function whose differences along edges lie in a subgroup is constant modulo
that subgroup.**

This is deliberately stated for an arbitrary abelian group and an arbitrary reachability relation, so
that no dissection theory is needed. Instantiating it at `A = ℝ/πℤ`, `H = ⟨α,β⟩` and the tile
adjacency relation is exactly the second half of `prop:gammagrading`; what remains unformalized is
only the geometric first clause.
-/

namespace Erdos634.CosetPropagation

variable {V : Type*} {A : Type*} [AddCommGroup A]

/-- Reachability in the reflexive-transitive-symmetric closure of `adj`. -/
inductive Reach (adj : V → V → Prop) : V → V → Prop
  | refl (v : V) : Reach adj v v
  | step {u v w : V} : Reach adj u v → (adj v w ∨ adj w v) → Reach adj u w

/-- **Coset propagation.** If the value of `f` changes by an element of `H` along every adjacency,
then any two reachable vertices differ by an element of `H`. -/
theorem sub_mem_of_reach {adj : V → V → Prop} {f : V → A} {H : AddSubgroup A}
    (hstep : ∀ u v, adj u v → f u - f v ∈ H) {u v : V} (h : Reach adj u v) :
    f u - f v ∈ H := by
  induction h with
  | refl => simpa using H.zero_mem
  | @step b c _hab hbc ih =>
      have hbc' : f b - f c ∈ H := by
        rcases hbc with h1 | h1
        · exact hstep _ _ h1
        · have := H.neg_mem (hstep _ _ h1)
          rwa [neg_sub] at this
      have heq : f u - f c = (f u - f b) + (f b - f c) := by abel
      rw [heq]
      exact H.add_mem ih hbc'

/-- **All values lie in one coset.** With a base point `v₀` reachable from everything, every value of
`f` differs from `f v₀` by an element of `H`: the whole image sits in a single coset. -/
theorem image_subset_coset {adj : V → V → Prop} {f : V → A} {H : AddSubgroup A}
    (hstep : ∀ u v, adj u v → f u - f v ∈ H) (v₀ : V) (hconn : ∀ v, Reach adj v v₀) :
    ∀ v, f v - f v₀ ∈ H :=
  fun v => sub_mem_of_reach hstep (hconn v)

/-- The form used by `prop:gammagrading`: writing `f v = f v₀ + h v` with `h v ∈ H`, every direction
is the reference direction shifted by an element of the angle subgroup. -/
theorem exists_shift {adj : V → V → Prop} {f : V → A} {H : AddSubgroup A}
    (hstep : ∀ u v, adj u v → f u - f v ∈ H) (v₀ : V) (hconn : ∀ v, Reach adj v v₀) (v : V) :
    ∃ h ∈ H, f v = f v₀ + h :=
  ⟨f v - f v₀, image_subset_coset hstep v₀ hconn v, by abel⟩

end Erdos634.CosetPropagation
