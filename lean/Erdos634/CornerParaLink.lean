import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# Wedge containment forces ray equality

`prop:cornerpara`'s proof (`paper/erdos-634.tex:771`) opens with "`T_A` is the unique tile at `A`
and its two edges there are `a` and `c`, **one along each side of `ABC`**" — i.e. the corner
tile's two edges from the corner point don't merely have the right *lengths*, they lie exactly
*along* the target's two boundary rays. `TileAt.lean`'s
`congruentDissection_base_corner_tile_vertex` gets as far as: the corner point is a genuine vertex
of the covering tile, with the same local angle `β` as the target's corner. What is missing before
`TilePlacement.c_corner_side_a`/`.a_corner_side_c` become applicable is exactly the geometric fact
that a sub-wedge of angle `β`, sitting inside a wedge of the *same* angle `β` at the same vertex,
must have its two boundary rays coincide with the outer wedge's — otherwise the "along" in the
paper's sentence is unjustified and the tile's edges could point anywhere inside the target's
corner wedge with only the *length* pinned down.

This file proves that fact in general, for oriented angles at a point of a 2-dimensional real
inner product space, then draws the ray-equality conclusion via
`Orientation.oangle_eq_zero_iff_sameRay`.

## Statement and why the containment hypothesis is doing real work

Unsigned angle equality alone (`InnerProductGeometry.angle u v = InnerProductGeometry.angle u' v'`)
is not enough: a wedge and its exact mirror image (swap orientation sense) have the same unsigned
angle without any of their rays coinciding. The genuine content of "the same two boundary
directions bounding a sub-wedge, again of angle `β`, that sits inside the big wedge" is captured by
requiring `u'` and `v'` (the sub-wedge's two boundary directions) to *individually lie inside* the
big wedge, i.e. their **oriented** angle from `u` lies between `0` and the big wedge's own oriented
angle from `u` to `v`. This one-sided-cone membership hypothesis, together with the sub-wedge
having the same *unsigned* angle `β`, is what pins the sub-wedge's rays to the big wedge's boundary
— dropping it would let `u'` sit anywhere inside and the theorem is false (e.g. `u'` at oriented
angle `β/2` from `u`, `v'` at oriented angle `β/2` "the other way", both unsigned angle `β/2` short
of the full `β`, is excluded once we also *impose* the sub-wedge's own angle be `β`, but a rotated
copy of the whole wedge that merely touches the big wedge at a single ray and *escapes* it on the
other side is excluded only by the membership hypothesis, not by the angle-equality hypothesis
alone).

The two-sided conclusion (`SameRay u u' ∧ SameRay v v'`, or the swapped pairing
`SameRay v u' ∧ SameRay u v'`) reflects that the sub-wedge could present its two directions in
either of the two matching orders; `prop:cornerpara`'s own use of `c_corner_side_a`/`a_corner_side_c`
already carries the analogous case split (a corner tile lays `c` on the base *or* lays `a` on the
base), so a two-way disjunction here is the right shape to feed that lemma pair, not a defect.
-/

namespace Erdos634.Geometry

open Real InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- **Real-number scaffolding**: two reals `s, t` lying in the unordered interval between `0` and
`σ`, whose difference has the same absolute value as `σ` itself, must be the two endpoints
`{0, σ}` — in one order or the other. Pure real arithmetic, isolated from the angle machinery so
the geometric proof below is just bookkeeping. -/
theorem endpoints_of_uIcc_abs_sub_eq (σ s t : ℝ) (hs : s ∈ Set.uIcc 0 σ) (ht : t ∈ Set.uIcc 0 σ)
    (habs : |t - s| = |σ|) : (s = 0 ∧ t = σ) ∨ (s = σ ∧ t = 0) := by
  rcases Set.mem_uIcc.mp hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩ <;>
    rcases Set.mem_uIcc.mp ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩ <;>
    rcases abs_eq_abs.mp habs with heq | heq <;>
    first
      | (left; exact ⟨by linarith, by linarith⟩)
      | (right; exact ⟨by linarith, by linarith⟩)

/-- **The wedge/ray link.** Let `u, v` bound a wedge of unsigned angle `β ∈ (0, π)` at the origin,
and let `u', v'` bound a sub-wedge, again of unsigned angle `β`, whose two directions each lie
inside the big wedge (their oriented angle from `u` falls between `0` and the big wedge's own
oriented angle from `u` to `v`). Then the two wedges' boundary rays coincide, in one of the two
matching orders. -/
theorem wedge_forces_ray_eq (u v u' v' : V) (hu : u ≠ 0) (hv : v ≠ 0) (hu' : u' ≠ 0)
    (hv' : v' ≠ 0) (β : ℝ) (hβ0 : 0 < β) (hβπ : β < π)
    (hangle : InnerProductGeometry.angle u v = β)
    (hangle' : InnerProductGeometry.angle u' v' = β)
    (hmemu' : (o.oangle u u').toReal ∈ Set.uIcc 0 (o.oangle u v).toReal)
    (hmemv' : (o.oangle u v').toReal ∈ Set.uIcc 0 (o.oangle u v).toReal) :
    (SameRay ℝ u u' ∧ SameRay ℝ v v') ∨ (SameRay ℝ v u' ∧ SameRay ℝ u v') := by
  set σ : ℝ := (o.oangle u v).toReal with hσdef
  set s : ℝ := (o.oangle u u').toReal with hsdef
  set t : ℝ := (o.oangle u v').toReal with htdef
  -- `σ`'s absolute value is `β`, since the unsigned angle is the absolute value of the toReal
  -- part of the oriented angle.
  have hσabs : |σ| = β := by
    rw [hσdef, ← o.angle_eq_abs_oangle_toReal hu hv, hangle]
  -- likewise every `toReal` coerces back to itself, and the additivity law for oriented angles
  -- turns into ordinary subtraction of the corresponding reals.
  have hcoe_s : (s : Real.Angle) = o.oangle u u' := Real.Angle.coe_toReal _
  have hcoe_t : (t : Real.Angle) = o.oangle u v' := Real.Angle.coe_toReal _
  have hcoe_σ : (σ : Real.Angle) = o.oangle u v := Real.Angle.coe_toReal _
  have hadd : o.oangle u u' + o.oangle u' v' = o.oangle u v' := o.oangle_add hu hu' hv'
  have hu'v' : o.oangle u' v' = ((t - s : ℝ) : Real.Angle) := by
    have : o.oangle u' v' = o.oangle u v' - o.oangle u u' := by
      rw [← hadd]; abel
    rw [this, ← hcoe_s, ← hcoe_t, Real.Angle.coe_sub]
  -- `t - s` already lies strictly between `-π` and `π`, since both `s` and `t` lie between `0`
  -- and `σ`, whose absolute value is `β < π`.
  have hσcase : σ = β ∨ σ = -β := (abs_eq hβ0.le).mp hσabs
  have htsbound : |t - s| ≤ β := by
    rcases hσcase with hσc | hσc <;> rw [hσc] at hmemu' hmemv' <;>
      rcases Set.mem_uIcc.mp hmemu' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases Set.mem_uIcc.mp hmemv' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rw [abs_le] <;> exact ⟨by linarith, by linarith⟩
  have htsrange : -π < t - s ∧ t - s ≤ π := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp htsbound
    constructor <;> linarith
  have htoReal : ((t - s : ℝ) : Real.Angle).toReal = t - s :=
    Real.Angle.toReal_coe_eq_self_iff.mpr htsrange
  have hu'v'toReal : (o.oangle u' v').toReal = t - s := by rw [hu'v', htoReal]
  have hβ' : |t - s| = β := by
    rw [← hu'v'toReal, ← hangle', o.angle_eq_abs_oangle_toReal hu' hv']
  have hβσ : |t - s| = |σ| := by rw [hβ', hσabs]
  rcases endpoints_of_uIcc_abs_sub_eq σ s t hmemu' hmemv' hβσ with ⟨hs0, htσ⟩ | ⟨hsσ, ht0⟩
  · -- `s = 0, t = σ`: `u'` sits on the `u`-ray and `v'` sits on the `v`-ray.
    left
    refine ⟨?_, ?_⟩
    · have : o.oangle u u' = 0 := by rw [← hcoe_s, hs0]; simp
      exact o.oangle_eq_zero_iff_sameRay.mp this
    · have huv' : o.oangle u v' = o.oangle u v := by rw [← hcoe_t, htσ, hcoe_σ]
      have : o.oangle v v' = 0 := by
        have hstep : o.oangle v u + o.oangle u v' = o.oangle v v' := o.oangle_add hv hu hv'
        rw [← hstep, o.oangle_rev, huv']
        abel
      exact o.oangle_eq_zero_iff_sameRay.mp this
  · -- `s = σ, t = 0`: the sub-wedge's rays are swapped relative to `u, v`.
    right
    refine ⟨?_, ?_⟩
    · have huu' : o.oangle u u' = o.oangle u v := by rw [← hcoe_s, hsσ, hcoe_σ]
      have : o.oangle v u' = 0 := by
        have hstep : o.oangle v u + o.oangle u u' = o.oangle v u' := o.oangle_add hv hu hu'
        rw [← hstep, o.oangle_rev, huu']
        abel
      exact o.oangle_eq_zero_iff_sameRay.mp this
    · have : o.oangle u v' = 0 := by rw [← hcoe_t, ht0]; simp
      exact o.oangle_eq_zero_iff_sameRay.mp this

/-- **Non-vacuity witness.** The hypotheses of `wedge_forces_ray_eq` are satisfiable: taking the
sub-wedge equal to the big wedge itself (`u' = u`, `v' = v`) discharges every hypothesis as long as
`u, v` themselves make a genuine angle `β ∈ (0, π)`, which is exactly the corner-tile situation
(`β` is a base corner angle of a nondegenerate triangle). -/
example (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) (β : ℝ) (hβ0 : 0 < β) (hβπ : β < π)
    (hangle : InnerProductGeometry.angle u v = β) :
    (SameRay ℝ u u ∧ SameRay ℝ v v) ∨ (SameRay ℝ v u ∧ SameRay ℝ u v) :=
  wedge_forces_ray_eq o u v u v hu hv hu hv β hβ0 hβπ hangle hangle
    (by rw [o.oangle_self]; simp [Set.left_mem_uIcc]) (by exact Set.right_mem_uIcc)

end Erdos634.Geometry

#print axioms Erdos634.Geometry.wedge_forces_ray_eq
