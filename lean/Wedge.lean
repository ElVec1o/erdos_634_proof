import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Tactic

/-!
Draft (E2h): the sector, described by half-planes rather than by polar coordinates.

`SectorArea.sector θ = polarCoord.symm '' ((0,1) ×ˢ (0,θ))` is a polar description. `TangentCone`
produces a cone as an intersection of half-planes. This file connects them:

  `sector θ = {p | ‖p‖ < 1} ∩ {p | 0 < p.2} ∩ {p | 0 < sin θ * p.1 - cos θ * p.2}`   (0 < θ < π)

Only the `⊆` direction is attempted here; that is the direction the assembly needs, since it lets a
cone-with-angle-θ be recognised as containing the sector, and the reverse follows from measure once
both are known to be sectors. Development copy.
-/

open Set Real

namespace Erdos634.Wedge

def polarBox (θ : ℝ) : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) θ

def sector (θ : ℝ) : Set (ℝ × ℝ) := polarCoord.symm '' polarBox θ

/-- `polarCoord.symm (r,φ) = (r cos φ, r sin φ)`. -/
theorem symm_apply (r φ : ℝ) : polarCoord.symm (r, φ) = (r * Real.cos φ, r * Real.sin φ) := rfl

/-- **The sector lies in the wedge cut out by two half-planes.** -/
theorem sector_subset_halfplanes {θ : ℝ} (hπ : θ < Real.pi) :
    sector θ ⊆ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
             ∩ {p : ℝ × ℝ | 0 < p.2}
             ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} := by
  rintro _ ⟨⟨r, φ⟩, ⟨hr, hφ⟩, rfl⟩
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hφ0, hφθ⟩ := hφ
  have hφπ : φ < Real.pi := lt_trans hφθ hπ
  have hsinφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ
  rw [symm_apply]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- inside the unit disc: r² cos² + r² sin² = r² < 1
    have : (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ
      nlinarith [this]
    rw [this]
    nlinarith
  · -- above the first ray
    exact mul_pos hr0 hsinφ
  · -- below the second ray: sin θ (r cos φ) − cos θ (r sin φ) = r sin(θ − φ) > 0
    have hexp : Real.sin θ * (r * Real.cos φ) - Real.cos θ * (r * Real.sin φ)
        = r * Real.sin (θ - φ) := by
      rw [Real.sin_sub]; ring
    rw [hexp]
    have : 0 < Real.sin (θ - φ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    exact mul_pos hr0 this

/-- On `(-π, π)`, a positive sine forces a positive argument. -/
theorem pos_of_sin_pos {x : ℝ} (hlo : -Real.pi < x) (hs : 0 < Real.sin x) : 0 < x := by
  by_contra h
  simp only [not_lt] at h
  have : Real.sin x ≤ 0 := by
    rcases eq_or_lt_of_le h with rfl | hneg
    · simp
    · have h1 : 0 < -x := by linarith
      have h2 : -x < Real.pi := by linarith
      have := Real.sin_pos_of_pos_of_lt_pi h1 h2
      rw [Real.sin_neg] at this; linarith
  linarith

/-- **The wedge is contained in the sector.** -/
theorem halfplanes_subset_sector {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
      ∩ {p : ℝ × ℝ | 0 < p.2}
      ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} ⊆ sector θ := by
  rintro p ⟨⟨hball, hy⟩, hwedge⟩
  simp only [Set.mem_setOf_eq] at hball hy hwedge
  -- p lies in the source, so it is the polar image of its own polar coordinates
  have hsrc : p ∈ polarCoord.source := Or.inr (by simpa using ne_of_gt hy)
  set q := polarCoord p with hq
  have hinv : polarCoord.symm q = p := polarCoord.left_inv hsrc
  have hqt : q ∈ polarCoord.target := polarCoord.map_source hsrc
  obtain ⟨hr, hφ⟩ := hqt
  simp only [Set.mem_Ioi] at hr
  simp only [Set.mem_Ioo] at hφ
  -- write p in polar form
  have hp1 : p.1 = q.1 * Real.cos q.2 := by rw [← hinv]; rfl
  have hp2 : p.2 = q.1 * Real.sin q.2 := by rw [← hinv]; rfl
  -- the angle is positive
  have hsinφ : 0 < Real.sin q.2 := by
    by_contra h
    simp only [not_lt] at h
    rw [hp2] at hy
    nlinarith
  have hφpos : 0 < q.2 := pos_of_sin_pos hφ.1 hsinφ
  -- the angle is below θ
  have hkey : Real.sin θ * p.1 - Real.cos θ * p.2 = q.1 * Real.sin (θ - q.2) := by
    rw [hp1, hp2, Real.sin_sub]; ring
  have hsinsub : 0 < Real.sin (θ - q.2) := by
    by_contra h
    simp only [not_lt] at h
    rw [hkey] at hwedge
    nlinarith
  have hφθ : q.2 < θ := by
    have := pos_of_sin_pos (by linarith [hφ.2]) hsinsub
    linarith
  -- the radius is below 1
  have hrad : q.1 < 1 := by
    have hsq : q.1 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      rw [hp1, hp2]; nlinarith [Real.sin_sq_add_cos_sq q.2]
    nlinarith
  exact ⟨q, ⟨⟨hr, hrad⟩, ⟨hφpos, hφθ⟩⟩, hinv⟩


/-- **E2h: the sector IS the wedge.** The polar description used by `SectorArea` and the
half-plane description produced by `TangentCone` define the same set. Combined with
`SectorArea.volume_sector`, the cone of opening `θ` cut by the unit ball has area `θ/2`, which is
the `hsector` hypothesis of `AngleSumAssembled`. -/
theorem sector_eq_halfplanes {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    sector θ = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
             ∩ {p : ℝ × ℝ | 0 < p.2}
             ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} :=
  Set.Subset.antisymm (sector_subset_halfplanes hπ) (halfplanes_subset_sector h0 hπ)

end Erdos634.Wedge
