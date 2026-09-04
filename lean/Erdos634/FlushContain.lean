import Erdos634.FlushCounts
import Erdos634.SupportFace

/-!
# Discharging the containment hypothesis

Erdős #634.  `FlushJoin.sum_sideLen_eq_dist` and `FlushCounts.exists_counts_of_wall` carry a
hypothesis `hsub : ∀ e ∈ lineChain, edge ⊆ segment P Q` — a side must not overshoot the wall
segment.  This file removes it in the case that matters: when `P Q` is the target's **whole**
contact set with the line `{f = c}`.

Two steps, both real:

* `edge_subset_of_target_contact`: a chain edge lies on the line *and* inside the target (edges are
  in the tile, tiles are in the target), so it lies in the target's contact set — hence in `P Q`
  whenever the contact set does.
* `target_contact_eq_side`: for a functional maximized on a side of the target, the contact set
  **is** that side.  This is `SupportFace.contact_eq_face` specialized to a `Tri`: the three
  vertices with two on the line and one strictly below, so the face is the segment between the two.

Composed, `exists_counts_of_wall_of_side` is `exists_counts_of_wall` with `hsub` gone: on a side of
the target, the tile side lengths are a nonnegative integer combination equal to the side's length.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.FlushContain

open Erdos634.Geometry Erdos634.FlushJoin Erdos634.FlushCounts Set

variable {N : ℕ}

/-- Any index of `Fin 3` is `j`, `j+1` or `j+2`. -/
theorem fin3_tri (j k : Fin 3) : k = j ∨ k = j + 1 ∨ k = j + 2 := by
  revert j k; decide

/-- **Containment from the target's contact set.**  A chain edge lies in `{x ∈ target | f x = c}`;
if that set is inside `segment P Q`, so is the edge. -/
theorem edge_subset_of_target_contact (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (P Q : Plane) (htarget : {x ∈ D.target.carrier | f x = c} ⊆ segment ℝ P Q)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    (D.tile e.1).edge e.2 ⊆ segment ℝ P Q := by
  intro x hx
  refine htarget ⟨?_, D.lineChain_edge_subset he x hx⟩
  exact Erdos634.Geometry.tile_subset_target D e.1 ((D.tile e.1).edge_subset_carrier e.2 hx)

/-- **The target's contact set is a side.**  If `f ≤ c` on the target, `f = c` at two vertices and
`f < c` at the third, the contact set is exactly the segment between the two. -/
theorem target_contact_eq_side (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (j : Fin 3)
    (hle : ∀ x ∈ T.carrier, f x ≤ c)
    (h0 : f (T.pts j) = c) (h1 : f (T.pts (j + 1)) = c) (h2 : f (T.pts (j + 2)) ≠ c) :
    {x ∈ T.carrier | f x = c} = segment ℝ (T.pts j) (T.pts (j + 1)) := by
  classical
  have hrange : (Set.range T.pts) = ((Finset.univ.image T.pts : Finset Plane) : Set Plane) := by
    ext y; simp [Set.mem_range]
  have hvle : ∀ v ∈ (Finset.univ.image T.pts : Finset Plane), f v ≤ c := by
    intro v hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
    exact hle _ (subset_convexHull ℝ _ ⟨k, rfl⟩)
  have hcar : T.carrier = convexHull ℝ ((Finset.univ.image T.pts : Finset Plane) : Set Plane) := by
    rw [Tri.carrier, hrange]
  rw [hcar, Erdos634.SupportFace.contact_eq_face f c _ hvle]
  -- the filtered vertex set is exactly `{pts j, pts (j+1)}`
  have hfilt : ((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane)
      = {T.pts j, T.pts (j + 1)} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨k, rfl⟩, hfk⟩
      rcases fin3_tri j k with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hfk h2
    · rintro (rfl | rfl)
      · exact ⟨⟨j, rfl⟩, h0⟩
      · exact ⟨⟨j + 1, rfl⟩, h1⟩
  rw [hfilt]
  simp [Finset.coe_insert, convexHull_pair]

/-- **`exists_counts_of_wall` with the containment hypothesis discharged.**  On a wall segment `P Q`
that is the target's whole contact set with `{f = c}`, the tile side lengths are a nonnegative
integer combination of the model's three side lengths equal to `dist P Q`. -/
theorem exists_counts_of_side (D : CongruentDissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    (P Q : Plane) (hPQ : P ≠ Q)
    (hS : segment ℝ P Q ⊆ {y | f y = c})
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (htarget : {x ∈ D.target.carrier | f x = c} ⊆ segment ℝ P Q) :
    ∃ na nb nc : ℕ,
      na * dist (D.model.pts 0) (D.model.pts 1)
        + nb * dist (D.model.pts 2) (D.model.pts 0)
        + nc * dist (D.model.pts 1) (D.model.pts 2) = dist P Q :=
  exists_counts_of_wall D f hf c P Q hPQ hS hint hwall
    (fun e he => edge_subset_of_target_contact D.toDissection f c P Q htarget he)

end Erdos634.FlushContain
