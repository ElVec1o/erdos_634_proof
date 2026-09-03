import Erdos634.Dissection

/-!
# Towards a real `ChordTrace`: the sign trichotomy

Erdős #634. `ChordDecomp.ChordTrace` (the `(3,7)`-specific chord-trace data behind
`prop:chorddecomp`/`prop:straddle`) carries its geometry as hypotheses ("the obligation is named
rather than [discharged]", per that file's own header) because nothing built the general fact a
real `Dissection` needs: for an *internal* chord line (not a supporting line of the whole target —
tiles can straddle it), which tiles straddle and which touch it only in a face.

The existing `tile_contact_face`/`contacts_cover_side` machinery in `Dissection.lean` does not
apply here: it assumes the tile already lies weakly on one side of the line (`hle`), which is
exactly false for a straddling tile. This file supplies the missing case split.

`Tri.sign_trichotomy` is the first piece: any tile against any line either lies weakly below it,
weakly above it, or has vertices strictly on both sides (straddles). Still needed for a real
`ChordTrace`: extracting the actual crossing segment in the straddle case (the two boundary points
where `f = c`), and then the multi-tile covering/length-additivity bookkeeping across a whole
chord — both unattempted so far.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry

namespace Erdos634.ChordTraceReal

/-- **A tile's sign relative to an external line, from its vertices alone.** Since `T.carrier` is
the convex hull of its three vertices and `f` is linear, `f`'s extreme values over the whole tile
are attained at vertices: `T` lies weakly below `f = c` iff every vertex does. This is the
foundational classification `ChordDecomp`'s straddle/flush dichotomy needs, for a general internal
line -- not just a supporting line of the whole target, which is all the existing
`tile_contact_face`/`contacts_cover_side` machinery handles. -/
theorem Tri.le_iff_forall_vertices_le (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ x ∈ T.carrier, f x ≤ c) ↔ ∀ i, f (T.pts i) ≤ c := by
  constructor
  · intro h i; exact h _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
  · intro h x hx
    rw [Tri.carrier] at hx
    refine convexHull_min ?_ (convex_halfSpace_le f.isLinear c) hx
    rintro y ⟨i, rfl⟩; exact h i

/-- The `≥` mirror of `Tri.le_iff_forall_vertices_le`. -/
theorem Tri.ge_iff_forall_vertices_ge (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ x ∈ T.carrier, c ≤ f x) ↔ ∀ i, c ≤ f (T.pts i) := by
  constructor
  · intro h i; exact h _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
  · intro h x hx
    rw [Tri.carrier] at hx
    refine convexHull_min ?_ (convex_halfSpace_ge f.isLinear c) hx
    rintro y ⟨i, rfl⟩; exact h i

/-- **The sign trichotomy.** Any tile, against any external line, either lies weakly below it,
weakly above it, or straddles it (has a vertex strictly on each side). The first two folds in the
case where the tile only touches the line in a face. -/
theorem Tri.sign_trichotomy (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) :
    (∀ x ∈ T.carrier, f x ≤ c) ∨ (∀ x ∈ T.carrier, c ≤ f x)
      ∨ ((∃ i, f (T.pts i) < c) ∧ (∃ j, c < f (T.pts j))) := by
  by_cases hlo : ∀ i, f (T.pts i) ≤ c
  · exact Or.inl ((Tri.le_iff_forall_vertices_le T f c).mpr hlo)
  · by_cases hhi : ∀ i, c ≤ f (T.pts i)
    · exact Or.inr (Or.inl ((Tri.ge_iff_forall_vertices_ge T f c).mpr hhi))
    · push Not at hlo hhi
      exact Or.inr (Or.inr ⟨hhi, hlo⟩)

end Erdos634.ChordTraceReal
