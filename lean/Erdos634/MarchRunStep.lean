import Erdos634.MarchKill

/-!
# The run step: distances force the components, and `BG → GB` dies from distances alone

`MarchKill.bg_gb_dies` consumes the junction configuration through *component* hypotheses.  This
file removes them: the components are **forced by the side lengths**.  If a triangle has its base
`[A, B]` of length `a = f` on a line and its apex at distance `c = f²` from `A` and `b = f² - 1`
from `B`, above the line, then the apex's offsets are exactly `(dBG, h)` — the intersection of two
circles has one point in the upper half-plane, and its coordinates are the model's.

So the final statement, `run_step_bg_gb_dies`, needs only:

* the two base edges: consecutive, equal components `(f, 0)`;
* the four apex **distances** (which is what congruence to the tile provides, via the corner
  figure deciding which corner sits at which end);
* the two apexes above the line.

Conclusion: `False`.  No coordinates of the apexes are assumed — they are derived.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.MarchRunStep

open Erdos634.Geometry Erdos634.MarchCoords

/-- **Two circles meet at a forced abscissa.**  From `u₀² + u₁² = c²` and `(u₀ - f)² + u₁² = b²`,
the abscissa is `(c² - b² + f²)/(2f)`. -/
theorem circle_x (u0 u1 b c f : ℝ) (hf : 0 < f)
    (h1 : u0 ^ 2 + u1 ^ 2 = c ^ 2) (h2 : (u0 - f) ^ 2 + u1 ^ 2 = b ^ 2) :
    u0 = (c ^ 2 - b ^ 2 + f ^ 2) / (2 * f) := by
  have key : 2 * f * u0 = c ^ 2 - b ^ 2 + f ^ 2 := by nlinarith [h1, h2]
  field_simp
  linarith [key]

/-- **The `BG` apex abscissa**, from the distances: `c` to the left end, `b` to the right. -/
theorem bg_abscissa (u0 u1 f : ℝ) (hf : 1 < f)
    (h1 : u0 ^ 2 + u1 ^ 2 = (f ^ 2) ^ 2)
    (h2 : (u0 - f) ^ 2 + u1 ^ 2 = (f ^ 2 - 1) ^ 2) :
    u0 = dBG f := by
  have hf0 : 0 < f := lt_trans zero_lt_one hf
  rw [circle_x u0 u1 (f ^ 2 - 1) (f ^ 2) f hf0 h1 h2]
  unfold dBG; field_simp; ring

/-- **The `GB` apex abscissa**: `b` to the left end, `c` to the right. -/
theorem gb_abscissa (v0 v1 f : ℝ) (hf : 1 < f)
    (h1 : v0 ^ 2 + v1 ^ 2 = (f ^ 2 - 1) ^ 2)
    (h2 : (v0 - f) ^ 2 + v1 ^ 2 = (f ^ 2) ^ 2) :
    v0 = dGB f := by
  have hf0 : 0 < f := lt_trans zero_lt_one hf
  rw [circle_x v0 v1 (f ^ 2) (f ^ 2 - 1) f hf0 h1 h2]
  unfold dGB; field_simp; ring

/-- **The two apex heights agree.**  Both square to `h2 f`, and both are positive. -/
theorem heights_agree (u0 u1 v0 v1 f : ℝ) (hf : 1 < f)
    (hu : u0 ^ 2 + u1 ^ 2 = (f ^ 2) ^ 2) (hu0 : u0 = dBG f)
    (hv : v0 ^ 2 + v1 ^ 2 = (f ^ 2 - 1) ^ 2) (hv0 : v0 = dGB f)
    (hup : 0 < u1) (hvp : 0 < v1) : u1 = v1 := by
  have hf0 : (0:ℝ) < f := lt_trans zero_lt_one hf
  have hfne : f ≠ 0 := ne_of_gt hf0
  have hq1 : u1 ^ 2 = (f ^ 2) ^ 2 - dBG f ^ 2 := by rw [← hu0]; linarith [hu]
  have hq2 : v1 ^ 2 = (f ^ 2 - 1) ^ 2 - dGB f ^ 2 := by rw [← hv0]; linarith [hv]
  have hbgc : dBG f ^ 2 + Erdos634.MarchCoords.h2 f = (f ^ 2) ^ 2 := bg_left f hfne
  have hgbb : dGB f ^ 2 + Erdos634.MarchCoords.h2 f = (f ^ 2 - 1) ^ 2 := gb_left f hfne
  have hsq : u1 ^ 2 = v1 ^ 2 := by rw [hq1, hq2]; linarith [hbgc, hgbb]
  nlinarith [hsq, hup, hvp]

/-- **The run step, from distances alone.**  Two distinct tiles of a dissection: the first has
base `[A, B]` with components `(f, 0)` and apex `X₁` at distances `c, b` from `A, B`; the second
has base `[B, D]` with components `(f, 0)` and apex `X₂` at distances `b, c` from `B, D`.  Both
apexes above the line.  That is a `BG` tile followed by a `GB` tile, and it is impossible. -/
theorem run_step_bg_gb_dies {N : ℕ} (D : Dissection N) {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂)
    {k₁ k₂ : Fin 3} (f : ℝ) (hf : 1 < f)
    (A B Dd X₁ X₂ : Plane)
    (hp₁ : (D.tile i₁).pts k₁ = B) (hp₁A : (D.tile i₁).pts (k₁ + 1) = A)
    (hp₁X : (D.tile i₁).pts (k₁ + 2) = X₁)
    (hp₂ : (D.tile i₂).pts k₂ = B) (hp₂D : (D.tile i₂).pts (k₂ + 1) = Dd)
    (hp₂X : (D.tile i₂).pts (k₂ + 2) = X₂)
    (hAB0 : B 0 - A 0 = f) (hAB1 : B 1 - A 1 = 0)
    (hBD0 : Dd 0 - B 0 = f) (hBD1 : Dd 1 - B 1 = 0)
    (hX1A : (X₁ 0 - A 0) ^ 2 + (X₁ 1 - A 1) ^ 2 = (f ^ 2) ^ 2)
    (hX1B : (X₁ 0 - B 0) ^ 2 + (X₁ 1 - B 1) ^ 2 = (f ^ 2 - 1) ^ 2)
    (hX2B : (X₂ 0 - B 0) ^ 2 + (X₂ 1 - B 1) ^ 2 = (f ^ 2 - 1) ^ 2)
    (hX2D : (X₂ 0 - Dd 0) ^ 2 + (X₂ 1 - Dd 1) ^ 2 = (f ^ 2) ^ 2)
    (hup1 : 0 < X₁ 1 - B 1) (hup2 : 0 < X₂ 1 - B 1) :
    False := by
  have hsub : ∀ (x y : Plane) (j : Fin 2), (x - y) j = x j - y j := fun _ _ _ => rfl
  -- the left apex, in coordinates relative to A, then B
  have hA1B : A 1 = B 1 := by linarith [hAB1]
  have hu1 : X₁ 1 - A 1 = X₁ 1 - B 1 := by rw [hA1B]
  have hu0eq : X₁ 0 - A 0 = dBG f := by
    refine bg_abscissa _ _ f hf hX1A ?_
    have : X₁ 0 - A 0 - f = X₁ 0 - B 0 := by linarith [hAB0]
    rw [this, hu1]; exact hX1B
  -- the right apex, relative to B
  have hv0eq : X₂ 0 - B 0 = dGB f := by
    refine gb_abscissa _ _ f hf hX2B ?_
    have : X₂ 0 - B 0 - f = X₂ 0 - Dd 0 := by linarith [hBD0]
    have h2' : X₂ 1 - B 1 = X₂ 1 - Dd 1 := by linarith [hBD1]
    rw [this, h2']; exact hX2D
  -- the common height
  have hX1Arw : (X₁ 0 - A 0) ^ 2 + (X₁ 1 - B 1) ^ 2 = (f ^ 2) ^ 2 := by
    rw [← hu1]; exact hX1A
  have hh : X₁ 1 - B 1 = X₂ 1 - B 1 :=
    heights_agree _ _ _ _ f hf hX1Arw hu0eq hX2B hv0eq hup1 hup2
  -- feed the component kill
  refine Erdos634.MarchKill.bg_gb_dies D hne (hp₁.trans hp₂.symm) f (X₁ 1 - B 1) hf hup1
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hp₁A, hp₁, hsub]; linarith [hAB0]
  · rw [hp₁A, hp₁, hsub]; linarith [hAB1]
  · rw [hp₁X, hp₁, hsub]
    have : X₁ 0 - B 0 = (X₁ 0 - A 0) - f := by linarith [hAB0]
    rw [this, hu0eq]
  · rw [hp₁X, hp₁, hsub]
  · rw [hp₂D, hp₂, hsub]; linarith [hBD0]
  · rw [hp₂D, hp₂, hsub]; linarith [hBD1]
  · rw [hp₂X, hp₂, hsub, hv0eq]
  · rw [hp₂X, hp₂, hsub]; linarith [hh]

/-! ## The same kill, from metric distances

`run_step_bg_gb_dies` takes squared component sums; congruence to the tile speaks in `dist`.  The
bridge is one identity, and the wrapper below is the natural final form of the junction kill: two
distinct tiles, consecutive `a`-edges on a line, apex distances `c, b` then `b, c` — the two
chirality assignments — apexes above.  Impossible. -/

/-- Squared distance in the plane, componentwise. -/
theorem dist_sq_plane (x y : Plane) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- **The junction kill, metric form.** -/
theorem run_step_bg_gb_dies_of_dist {N : ℕ} (D : Dissection N) {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂)
    {k₁ k₂ : Fin 3} (f : ℝ) (hf : 1 < f)
    (A B Dd X₁ X₂ : Plane)
    (hp₁ : (D.tile i₁).pts k₁ = B) (hp₁A : (D.tile i₁).pts (k₁ + 1) = A)
    (hp₁X : (D.tile i₁).pts (k₁ + 2) = X₁)
    (hp₂ : (D.tile i₂).pts k₂ = B) (hp₂D : (D.tile i₂).pts (k₂ + 1) = Dd)
    (hp₂X : (D.tile i₂).pts (k₂ + 2) = X₂)
    (hAB0 : B 0 - A 0 = f) (hAB1 : B 1 - A 1 = 0)
    (hBD0 : Dd 0 - B 0 = f) (hBD1 : Dd 1 - B 1 = 0)
    (hd1A : dist X₁ A = f ^ 2) (hd1B : dist X₁ B = f ^ 2 - 1)
    (hd2B : dist X₂ B = f ^ 2 - 1) (hd2D : dist X₂ Dd = f ^ 2)
    (hup1 : 0 < X₁ 1 - B 1) (hup2 : 0 < X₂ 1 - B 1) :
    False := by
  refine run_step_bg_gb_dies D hne f hf A B Dd X₁ X₂ hp₁ hp₁A hp₁X hp₂ hp₂D hp₂X
    hAB0 hAB1 hBD0 hBD1 ?_ ?_ ?_ ?_ hup1 hup2
  · rw [← dist_sq_plane, hd1A]
  · rw [← dist_sq_plane, hd1B]
  · rw [← dist_sq_plane, hd2B]
  · rw [← dist_sq_plane, hd2D]

end Erdos634.MarchRunStep
