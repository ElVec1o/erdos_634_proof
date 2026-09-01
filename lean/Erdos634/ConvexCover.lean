import Erdos634.Dissection

/-!
# From an area-exhausting family of tiles to a `Dissection` (the certified-search bridge, topological half)

Erdős #634. Eight `PROVED` rows — `thm:44`, `thm:63`, `cor:elevenm`, `thm:frontier`(×4),
`thm:eq105` — rest on a certified search whose output is a finite family of concrete triangles
inside a target, with (C1) side lengths, (C2) containment, (C3) pairwise separating lines
(⟹ disjoint interiors), (C4) total signed area equal to the target's. The recorded blocker in
`PAPER_MAP` was always the same: turning that data into an actual `Dissection`, whose `covers`
field demands the *pointwise* set equality `⋃ tileᵢ.carrier = target.carrier`, not merely
measure-theoretic exhaustion.

This file supplies exactly that missing step, once and for all, in the `Tri`/`Dissection`
framework:

* `closed_full_measure_subset` — a closed full-measure subset of a convex set with nonempty
  interior is the whole set. (Its complement is relatively open and null; a nonempty relatively-open
  subset of such a convex set meets the interior, so has positive measure.)
* `iUnion_carrier_eq_of_area` — `N` tiles inside a target, with pairwise-disjoint interiors and
  total area equal to the target's, cover the target exactly. (`measure_biUnion_finset₀` turns
  disjoint interiors + null frontiers into `volume (⋃) = ∑ volume`, hence full measure; the union
  of finitely many compacts is closed; then the lemma above.)
* `dissectionOfCover` — packages the two `Dissection` fields, giving the `Dissection` object the
  bridge needs.

What this does **not** do is the *other* half of the bridge: translating a specific certificate's
`ℤ[√d]`-coordinate data (e.g. `Tiling44`'s `Pt = ℤ×ℤ×ℤ×ℤ` triangles) into `Tri` objects over
`Plane = EuclideanSpace ℝ (Fin 2)`, and re-deriving (C2)/(C3)/(C4) there. That is per-certificate
arithmetic transport, still to be done; but the geometric/measure content — the part that had no
counterpart in Mathlib — is now closed and reusable.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Geometry

open MeasureTheory Set Filter Topology

/-- **A closed full-measure subset of a convex set with nonempty interior is the whole set.** -/
theorem closed_full_measure_subset {K S : Set Plane} (hK : Convex ℝ K)
    (hne : (interior K).Nonempty) (hSK : S ⊆ K) (hS : IsClosed S)
    (hnull : volume (K \ S) = 0) : S = K := by
  refine Set.Subset.antisymm hSK (fun x hx => ?_)
  by_contra hxS
  obtain ⟨p, hp⟩ := hne
  have hc : Continuous (fun t : ℝ => x + t • (p - x)) := by fun_prop
  have htend : Tendsto (fun t : ℝ => x + t • (p - x)) (𝓝[>] (0:ℝ)) (𝓝 x) := by
    have h := (hc.continuousAt (x := (0:ℝ))).continuousWithinAt (s := Ioi (0:ℝ))
    simpa only [ContinuousWithinAt, zero_smul, add_zero] using h
  have hScnhd : Sᶜ ∈ 𝓝 x := hS.isOpen_compl.mem_nhds hxS
  have hev1 : ∀ᶠ t in 𝓝[>] (0:ℝ), (x + t • (p - x)) ∈ Sᶜ := htend.eventually hScnhd
  have hIoc : Ioc (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := by
    rw [← Ioi_inter_Iic]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num)))
  have hev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Ioc (0:ℝ) 1 := eventually_mem_set.mpr hIoc
  obtain ⟨t, htSc, htIoc⟩ := (hev1.and hev2).exists
  set z := x + t • (p - x) with hz
  have hzint : z ∈ interior K := hK.add_smul_sub_mem_interior hx hp htIoc
  have hopen : IsOpen (interior K ∩ Sᶜ) := isOpen_interior.inter hS.isOpen_compl
  have hsub : interior K ∩ Sᶜ ⊆ K \ S := fun w ⟨hw1, hw2⟩ => ⟨interior_subset hw1, hw2⟩
  have hpos : 0 < volume (interior K ∩ Sᶜ) := hopen.measure_pos volume ⟨z, hzint, htSc⟩
  have hlt : 0 < volume (K \ S) := lt_of_lt_of_le hpos (measure_mono hsub)
  rw [hnull] at hlt
  exact lt_irrefl _ hlt

variable {N : ℕ}

/-- **The union of an area-exhausting disjoint-interior family covers the target exactly.** -/
theorem iUnion_carrier_eq_of_area (target : Tri) (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (harea : ∑ i, volume (tile i).carrier = volume target.carrier) :
    (⋃ i, (tile i).carrier) = target.carrier := by
  classical
  -- the union is a.e.-disjoint (interiors disjoint, frontiers null), so its volume is the sum
  have hae : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∀ j ∈ (Finset.univ : Finset (Fin N)),
      i ≠ j → AEDisjoint volume (tile i).carrier (tile j).carrier := by
    intro i _ j _ hij
    have hsub' : (tile i).carrier ∩ (tile j).carrier ⊆
        frontier (tile i).carrier ∪ frontier (tile j).carrier := by
      rintro x ⟨hxi, hxj⟩
      by_cases h1 : x ∈ interior (tile i).carrier
      · by_cases h2 : x ∈ interior (tile j).carrier
        · exact absurd h2 (Set.disjoint_left.mp (hdisj hij) h1)
        · exact Or.inr ⟨subset_closure hxj, h2⟩
      · exact Or.inl ⟨subset_closure hxi, h1⟩
    exact measure_mono_null hsub'
      (measure_union_null (tile i).volume_frontier (tile j).volume_frontier)
  have hvolU : volume (⋃ i ∈ (Finset.univ : Finset (Fin N)), (tile i).carrier)
      = ∑ i, volume (tile i).carrier :=
    measure_biUnion_finset₀ hae (fun i _ => (tile i).nullMeasurableSet)
  have hU : (⋃ i, (tile i).carrier) = ⋃ i ∈ (Finset.univ : Finset (Fin N)), (tile i).carrier := by
    simp
  -- the union is closed (finite union of compacts) and full-measure inside the target
  have hclosed : IsClosed (⋃ i, (tile i).carrier) :=
    isClosed_iUnion_of_finite (fun i => (tile i).isCompact.isClosed)
  have hsubU : (⋃ i, (tile i).carrier) ⊆ target.carrier := Set.iUnion_subset hsub
  have hfull : volume (⋃ i, (tile i).carrier) = volume target.carrier := by
    rw [hU, hvolU, harea]
  have hnull : volume (target.carrier \ (⋃ i, (tile i).carrier)) = 0 := by
    have hle : volume (⋃ i, (tile i).carrier) ≤ volume target.carrier :=
      measure_mono hsubU
    have hdiff := measure_diff hsubU hclosed.nullMeasurableSet
      (ne_top_of_le_ne_top target.volume_ne_top hle)
    rw [hdiff, hfull, tsub_self]
  exact closed_full_measure_subset target.convex target.interior_nonempty hsubU hclosed hnull

/-- **The certified-search bridge, topological half: a `Dissection` from area + disjoint
interiors.** Given `N` tiles inside a target with pairwise-disjoint interiors and total area equal
to the target's, the `Dissection N` whose covering is `iUnion_carrier_eq_of_area` and whose
disjointness is the hypothesis. -/
def dissectionOfCover (target : Tri) (tile : Fin N → Tri)
    (hsub : ∀ i, (tile i).carrier ⊆ target.carrier)
    (hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier))
    (harea : ∑ i, volume (tile i).carrier = volume target.carrier) : Dissection N where
  target := target
  tile := tile
  covers := iUnion_carrier_eq_of_area target tile hsub hdisj harea
  interiors_disjoint := hdisj

end Erdos634.Geometry
