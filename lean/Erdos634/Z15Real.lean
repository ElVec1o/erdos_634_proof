import Mathlib.Analysis.SpecialFunctions.Sqrt
import Erdos634.CertCoord

/-!
# `ℤ[√15]` as real numbers

Erdős #634. Every tiling certificate in this project (`Tiling44`, `Tiling99`, `CevianTiling63`,
`PgramTiling22`, …) works in `ℤ[√15]`, represented as a pair of integers `(a, b) ↦ a + b√15`, and
decides its four checks there by `decide`. To feed those checks to the geometry — `CertCoord`,
`CertGeom`, `AreaDet` — each has to become a statement about real numbers.

This file is that translation. `toR` is the embedding, `toR_add`/`toR_sub`/`toR_mul` say it is a
ring map, and `toR_nonneg` / `toR_pos` transfer the certificates' sign tests. Note what is *not*
needed: injectivity of `toR`, hence not the irrationality of `√15`. Every check a certificate
performs is transferred in one direction only — an equality or an inequality *in* `ℤ[√15]` implies
the corresponding statement in `ℝ` — so the arithmetic is entirely one-way.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Z15Real

/-- An element of `ℤ[√15]`, as a pair of integers. -/
abbrev Z15 := ℤ × ℤ

/-- The embedding `a + b√15`. -/
noncomputable def toR (z : Z15) : ℝ := (z.1 : ℝ) + (z.2 : ℝ) * Real.sqrt 15

theorem sqrt15_nonneg : (0:ℝ) ≤ Real.sqrt 15 := Real.sqrt_nonneg 15

theorem sqrt15_sq : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)

theorem sqrt15_pos : (0:ℝ) < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)

/-- **A concrete-instance nonvanishing test, decidable per certificate edge.** `toR z = 0` forces
`z.1 = -z.2 * √15`, and squaring (valid regardless of sign) gives the integer equation
`z.1 ^ 2 = 15 * z.2 ^ 2` — false for any specific `z` one can name, checkable by `decide`/`norm_num`
without proving `√15` irrational in general. This is exactly what a certificate's edge endpoints
need for `CertGeom.lineFun_linear_ne_zero`: `P ≠ Q` in `ℤ[√15]` alone does not give `toR P ≠ toR Q`
(since `toR` is deliberately not proved injective), but for a *named* edge the difference
`zx Q - zx P` / `zy Q - zy P` is a concrete pair, and this lemma closes it. -/
theorem toR_ne_zero_of_sq_ne {z : Z15} (h : z.1 ^ 2 ≠ 15 * z.2 ^ 2) : toR z ≠ 0 := by
  intro heq
  have h0 : (z.1 : ℝ) = -(z.2 : ℝ) * Real.sqrt 15 := by
    simp only [toR] at heq; linarith
  have hsq : (z.1 : ℝ) ^ 2 = 15 * (z.2 : ℝ) ^ 2 := by
    have h1 : (z.1 : ℝ) ^ 2 = (z.2 : ℝ) ^ 2 * Real.sqrt 15 ^ 2 := by rw [h0]; ring
    rw [sqrt15_sq] at h1; linarith
  have : (z.1 ^ 2 : ℤ) = 15 * z.2 ^ 2 := by exact_mod_cast hsq
  exact h this

/-- Addition in `ℤ[√15]`. -/
def zadd (u v : Z15) : Z15 := (u.1 + v.1, u.2 + v.2)
/-- Subtraction in `ℤ[√15]`. -/
def zsub (u v : Z15) : Z15 := (u.1 - v.1, u.2 - v.2)
/-- Multiplication in `ℤ[√15]`. -/
def zmul (u v : Z15) : Z15 := (u.1 * v.1 + 15 * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

@[simp] theorem toR_add (u v : Z15) : toR (zadd u v) = toR u + toR v := by
  simp only [toR, zadd, Int.cast_add]; ring

@[simp] theorem toR_sub (u v : Z15) : toR (zsub u v) = toR u - toR v := by
  simp only [toR, zsub, Int.cast_sub]; ring

@[simp] theorem toR_mul (u v : Z15) : toR (zmul u v) = toR u * toR v := by
  simp only [toR, zmul, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  have h : Real.sqrt 15 * Real.sqrt 15 = 15 := by
    have := sqrt15_sq; nlinarith [this]
  push_cast
  linear_combination (-(u.2:ℝ) * (v.2:ℝ)) * h

@[simp] theorem toR_zero : toR (0, 0) = 0 := by simp [toR]

/-- The certificates' nonnegativity test on `ℤ[√15]`. -/
def znonneg (z : Z15) : Bool :=
  if 0 ≤ z.1 then (if 0 ≤ z.2 then true else 15 * z.2 * z.2 ≤ z.1 * z.1)
  else (if z.2 < 0 then false else z.1 * z.1 ≤ 15 * z.2 * z.2)

/-- **The nonnegativity test is sound.** -/
theorem toR_nonneg {z : Z15} (h : znonneg z = true) : 0 ≤ toR z := by
  obtain ⟨a, b⟩ := z
  simp only [znonneg] at h
  have hs := sqrt15_nonneg
  have hsq : Real.sqrt 15 * Real.sqrt 15 = 15 := by nlinarith [sqrt15_sq]
  simp only [toR]
  by_cases ha : 0 ≤ a
  · simp only [ha, if_true] at h
    by_cases hb : 0 ≤ b
    · have ha' : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
      have hb' : (0:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
      positivity
    · simp only [hb, if_false, decide_eq_true_eq] at h
      have ha' : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
      have hb' : (b:ℝ) < 0 := by exact_mod_cast (not_le.mp hb)
      have h' : (15:ℝ) * b * b ≤ a * a := by exact_mod_cast h
      nlinarith [hsq, hs, mul_nonneg ha' hs, sq_nonneg ((a:ℝ) - b * Real.sqrt 15)]
  · simp only [ha, if_false] at h
    by_cases hb : b < 0
    · simp only [hb, if_true] at h
      exact absurd h (by simp)
    · simp only [hb, if_false, decide_eq_true_eq] at h
      have ha' : (a:ℝ) < 0 := by exact_mod_cast (not_le.mp ha)
      have hb' : (0:ℝ) ≤ (b:ℝ) := by exact_mod_cast (not_lt.mp hb)
      have h' : ((a:ℝ)) * a ≤ 15 * b * b := by exact_mod_cast h
      nlinarith [hsq, hs, mul_nonneg hb' hs, sq_nonneg ((a:ℝ) + b * Real.sqrt 15)]

/-- **The nonnegativity test is also complete**, so it decides the sign exactly. -/
theorem toR_nonneg_iff {z : Z15} : znonneg z = true ↔ 0 ≤ toR z := by
  refine ⟨toR_nonneg, ?_⟩
  obtain ⟨a, b⟩ := z
  intro h
  have hs := sqrt15_nonneg
  have hsq : Real.sqrt 15 * Real.sqrt 15 = 15 := by nlinarith [sqrt15_sq]
  simp only [toR] at h
  simp only [znonneg]
  by_cases ha : 0 ≤ a
  · simp only [ha, if_true]
    by_cases hb : 0 ≤ b
    · simp [hb]
    · simp only [hb, if_false, decide_eq_true_eq]
      have hb' : (b:ℝ) < 0 := by exact_mod_cast (not_le.mp hb)
      have ha' : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
      have hpos : (0:ℝ) ≤ (a:ℝ) - b * Real.sqrt 15 := by nlinarith [sqrt15_pos, hb', ha']
      have hprod := mul_nonneg h hpos
      have key : (15:ℝ) * b * b ≤ (a:ℝ) * a := by nlinarith [hprod, hsq]
      exact_mod_cast key
  · simp only [ha, if_false]
    have ha' : (a:ℝ) < 0 := by exact_mod_cast (not_le.mp ha)
    by_cases hb : b < 0
    · exfalso
      have hb' : (b:ℝ) < 0 := by exact_mod_cast hb
      nlinarith [h, hs, mul_nonneg (le_of_lt (neg_pos.mpr hb')) hs]
    · simp only [hb, if_false, decide_eq_true_eq]
      have hb' : (0:ℝ) ≤ (b:ℝ) := by exact_mod_cast (not_lt.mp hb)
      have hpos : (0:ℝ) ≤ (b:ℝ) * Real.sqrt 15 - a := by nlinarith [ha', mul_nonneg hb' hs]
      have hprod := mul_nonneg h hpos
      have key : (a:ℝ) * a ≤ 15 * b * b := by nlinarith [hprod, hsq]
      exact_mod_cast key

/-- The certificates' positivity test. -/
def zpos (z : Z15) : Bool := !(znonneg (-z.1, -z.2))

/-- **The positivity test is sound.** -/
theorem toR_pos {z : Z15} (h : zpos z = true) : 0 < toR z := by
  simp only [zpos, Bool.not_eq_true'] at h
  have hne : ¬ (0 ≤ toR (-z.1, -z.2)) := by
    intro hcon
    rw [← toR_nonneg_iff] at hcon
    exact absurd hcon (by simp [h])
  have hneg : toR (-z.1, -z.2) = -toR z := by simp only [toR]; push_cast; ring
  rw [hneg] at hne
  linarith [not_le.mp hne]

/-- A certificate point: two `ℤ[√15]` coordinates. -/
abbrev ZPt := ℤ × ℤ × ℤ × ℤ

/-- Its `x` coordinate. -/
def zx (p : ZPt) : Z15 := (p.1, p.2.1)
/-- Its `y` coordinate. -/
def zy (p : ZPt) : Z15 := (p.2.2.1, p.2.2.2)

/-- The point of `Plane` a certificate point names. -/
noncomputable def toPlanePt (p : ZPt) : Erdos634.Geometry.Plane :=
  Erdos634.CertCoord.mkPt (toR (zx p)) (toR (zy p))

/-- The `ℤ[√15]` cross product `(a-o) × (b-o)`, matching every certificate file's `cross`. -/
def zcross (o a b : ZPt) : Z15 :=
  zsub (zmul (zsub (zx a) (zx o)) (zsub (zy b) (zy o)))
       (zmul (zsub (zy a) (zy o)) (zsub (zx b) (zx o)))

/-- **The transfer lemma the certificate-to-`Tri` bridge needs**: a certificate's `ℤ[√15]` cross
product, read through `toR`, is exactly `CertCoord.det3` on the transferred real coordinates. So a
`decide`-checked sign of `zcross` transfers directly to the sign hypotheses `CertCoord.mkTri` and
`CertCoord.mem_carrier_of_dets` consume. -/
theorem toR_zcross (o a b : ZPt) :
    Erdos634.CertCoord.det3 (toR (zx o)) (toR (zy o)) (toR (zx a)) (toR (zy a))
      (toR (zx b)) (toR (zy b)) = toR (zcross o a b) := by
  simp only [zcross, Erdos634.CertCoord.det3, toR_sub, toR_mul]; ring

end Erdos634.Z15Real
