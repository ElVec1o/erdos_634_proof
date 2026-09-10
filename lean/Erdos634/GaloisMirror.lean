import Erdos634.MirrorGauge
import Erdos634.BaseBetaQuadField

/-!
# The Galois group of the coordinate field *is* the mirror gauge

Erdős #634, base-`β`.  Two independent lines of this project arrived at the same plane map without
noticing:

* **the arithmetic line.**  `BaseBetaQuadCoord`/`BaseBetaQuadField` put every tile direction, and
  (given the orientation hypothesis) every vertex, in the imaginary quadratic field
  `K = ℚ(√−D)`, `D = 4f² − e²`.  `Gal(K/ℚ) = {1, σ}` with `σ : x + y√−D ↦ x − y√−D`
  (`BaseBetaQuad.qconj`).  The `crossing` room's Laczkovich seat (2026-09-05, S6) observed that `σ`
  acts on the coordinate plane as a reflection and concluded that Laczkovich's conjugate-tiling /
  Condition-(K) engine degenerates on this family.
* **the geometric line.**  `MirrorGauge` (2026-09-09) introduced `mirrorPt`, reflection in the first
  coordinate axis, proved it carries dissections to dissections with the *same* model, negates every
  tile determinant, and derived `no_global_orientation_count` and `mirror_invariant_forces_mixed`:
  no mirror-invariant criterion can supply the endpoint fact reach-4 needs.

This file proves the two maps are **the same map**, exactly, not merely similar in flavour:

  `pt_qconj : pt e f (qconj z) = MirrorGauge.mirrorPt (pt e f z)`

and on the complex model `emb_qconj : emb e f (σ z) = conj (emb e f z)` — `σ` is complex
conjugation, and complex conjugation is the mirror.  From there:

* `Tri.mirror_of_coords` — a tile whose vertices are `K`-coordinates has, as its `MirrorGauge`
  mirror, exactly the tile of the `σ`-conjugated coordinates.  So *the Galois-conjugate tiling and
  the mirror tiling are literally the same tiling*.
* `galoisStable_iff_mirrorInvariant` — for a predicate on plane points, being stable under `σ` on
  coordinates is **equivalent** to being invariant under `mirrorPt` on the image.

## The consequence, stated honestly

Every invariant one can build out of the *arithmetic of `K`* alone — the norm form, the trace, the
ideal factorisation of a coordinate up to the Galois action, the class of an ideal, the unit group,
the pair of valuations `{v_𝔭, v_𝔭̄}` at a split prime — is by construction `Gal(K/ℚ)`-stable, hence
by `galoisStable_iff_mirrorInvariant` **mirror-invariant**, hence lands in the class
`MirrorGauge.mirror_invariant_forces_mixed` already proves cannot give the endpoint fact: such a
criterion holds only on *mixed* runs, so establishing it for a run would prove that run **is** the
bad configuration.  The only escape is an invariant that breaks the Galois symmetry by preferring
one of the two primes `𝔭, 𝔭̄` above a split `p` — which is precisely the `𝔭`-adic *level* the
Laczkovich seat already built and killed (S10–S12: unbounded on interior vertices; equal to the
`b`-residue calculus, tool class 7, on the boundary; and its range is *wider* on the `m=3`
certificate than on the `m=2` one, refuting every bound).

So: the algebraic-number-theoretic route over `K` is not an unexplored fifth route family beside
local-planar, local-angular, global-counting and cross-strip.  It is the *same* obstruction as
global-counting, now with the identification proved rather than asserted, plus one Galois-breaking
residue that is separately dead.  **No label moves and no named target falls.**

Non-vacuity is exhibited (`sigma_moves_a_point`, `pt_ne_mirror_witness`): at `(e,f) = (1,2)`,
`D = 15`, the point `√−15` is genuinely moved by `σ`, so the identification is not the identity map
asserted about an empty class.

Axiom-clean, no `sorry`.  Date: 2026-09-10.
-/

namespace Erdos634.GaloisMirror

open Erdos634.Geometry Erdos634.BaseBetaQuad Erdos634.MirrorGauge

/-! ## The coordinate plane of `K = ℚ(√−D)` -/

/-- `√D` as a real number, `D = 4f² − e²`. -/
noncomputable def rD (e f : ℚ) : ℝ := Real.sqrt ((Dq e f : ℚ) : ℝ)

/-- The plane point of a `K`-coordinate `z = x + y√−D`: real part on the first axis, the
`√−D`-part on the second.  This is the same identification `BaseBetaQuadField.emb` makes into `ℂ`,
read in `Plane = EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def pt (e f : ℚ) (z : ℚ × ℚ) : Plane :=
  WithLp.toLp 2 ![(z.1 : ℝ), (z.2 : ℝ) * rD e f]

@[simp] theorem pt_zero (e f : ℚ) (z : ℚ × ℚ) : pt e f z 0 = (z.1 : ℝ) := rfl

@[simp] theorem pt_one (e f : ℚ) (z : ℚ × ℚ) : pt e f z 1 = (z.2 : ℝ) * rD e f := rfl

/-! ## The identification -/

/-- **The Galois involution of `K` is the plane mirror.**  `σ : x + y√−D ↦ x − y√−D` acts on the
coordinate plane exactly as `MirrorGauge.mirrorPt`, reflection in the first axis.  This is the
whole point of the file: the arithmetic symmetry and the geometric gauge are one map. -/
theorem pt_qconj (e f : ℚ) (z : ℚ × ℚ) : pt e f (qconj z) = mirrorPt (pt e f z) := by
  ext i
  fin_cases i
  · show ((qconj z).1 : ℝ) = (z.1 : ℝ)
    simp [qconj]
  · show ((qconj z).2 : ℝ) * rD e f = -((z.2 : ℝ) * rD e f)
    simp [qconj]

/-- **On the complex model, `σ` is complex conjugation.**  `BaseBetaQuadField.emb` intertwines the
coordinate conjugation with `starRingEnd ℂ`, whose action on the plane is reflection in the real
axis — the same mirror again. -/
theorem emb_qconj (e f : ℚ) (z : ℚ × ℚ) :
    emb e f (qconj z) = (starRingEnd ℂ) (emb e f z) := by
  simp only [emb, qconj, sD, map_add, map_mul, Complex.conj_I]
  push_cast
  simp [Complex.conj_ofReal]

/-- The mirror is an involution on coordinates too, as it must be for a quadratic Galois group. -/
@[simp] theorem qconj_involutive (z : ℚ × ℚ) : qconj (qconj z) = z := by
  simp [qconj]

/-! ## Non-vacuity: `σ` really moves points -/

/-- `D = 15` at `(e,f) = (1,2)`. -/
theorem Dq_one_two : Dq 1 2 = 15 := by norm_num [Dq]

/-- `√15 ≠ 0`. -/
theorem rD_one_two_pos : 0 < rD 1 2 := by
  have : ((Dq 1 2 : ℚ) : ℝ) = 15 := by rw [Dq_one_two]; norm_num
  rw [rD, this]
  exact Real.sqrt_pos.mpr (by norm_num)

/-- **Non-vacuity.**  At the smallest member `(e,f) = (1,2)` the coordinate `√−15` is genuinely
moved by `σ`: the identification `pt_qconj` is a statement about a nontrivial involution, not a
theorem about the identity map. -/
theorem sigma_moves_a_point : pt 1 2 (qconj (0, 1)) ≠ pt 1 2 (0, 1) := by
  intro h
  have h1 : ((qconj ((0 : ℚ), (1 : ℚ))).2 : ℝ) * rD 1 2
      = ((((0 : ℚ), (1 : ℚ)) : ℚ × ℚ).2 : ℝ) * rD 1 2 := by
    rw [← pt_one 1 2, ← pt_one 1 2, h]
  simp only [qconj] at h1
  push_cast at h1
  linarith [rD_one_two_pos]

/-- Restated against the mirror: the mirror is not the identity on the coordinate plane. -/
theorem pt_ne_mirror_witness : mirrorPt (pt 1 2 (0, 1)) ≠ pt 1 2 (0, 1) := by
  rw [← pt_qconj]; exact sigma_moves_a_point

/-! ## Tiles: the Galois-conjugate tiling is the mirror tiling -/

/-- **A tile with `K`-coordinates has the `σ`-conjugated tile as its mirror.**  Composed with
`MirrorGauge.Tri.det_mirror` this says: Galois conjugation reverses the orientation of every tile
whose vertices lie in `K`. -/
theorem Tri.mirror_of_coords (e f : ℚ) (T : Tri) (z : Fin 3 → ℚ × ℚ)
    (h : ∀ k, T.pts k = pt e f (z k)) (k : Fin 3) :
    (MirrorGauge.Tri.mirror T).pts k = pt e f (qconj (z k)) := by
  rw [MirrorGauge.Tri.mirror_pts, h k, pt_qconj]

/-- **Galois conjugation negates the determinant.**  The tile of the `σ`-conjugated coordinates is
`MirrorGauge.Tri.mirror T`, and its determinant is `−T.det`.  There is therefore no `Gal(K/ℚ)`-stable
quantity that can see a tile's orientation: `σ` reverses it while fixing every `σ`-stable datum. -/
theorem conjugate_tile_det (e f : ℚ) (T : Tri) (z : Fin 3 → ℚ × ℚ)
    (h : ∀ k, T.pts k = pt e f (z k)) :
    (∀ k, (MirrorGauge.Tri.mirror T).pts k = pt e f (qconj (z k))) ∧
      (MirrorGauge.Tri.mirror T).det = - T.det :=
  ⟨fun k => Tri.mirror_of_coords e f T z h k, MirrorGauge.Tri.det_mirror T⟩

/-! ## The dichotomy -/

/-- A predicate on plane points is **Galois-stable** if it does not distinguish a `K`-coordinate
from its conjugate.  Every invariant built from the arithmetic of `K` — norm, trace, ideal class,
unit, the unordered pair of valuations at a split prime — has this form, because `Gal(K/ℚ)` permutes
the data those invariants are computed from. -/
def GaloisStable (e f : ℚ) (Q : Plane → Prop) : Prop :=
  ∀ z : ℚ × ℚ, Q (pt e f z) ↔ Q (pt e f (qconj z))

/-- **Galois-stable = mirror-invariant.**  The two notions coincide on the coordinate plane, which
is why no arithmetic invariant of `K` escapes `MirrorGauge.mirror_invariant_forces_mixed`: it is
already in that theorem's hypothesis class. -/
theorem galoisStable_iff_mirrorInvariant (e f : ℚ) (Q : Plane → Prop) :
    GaloisStable e f Q ↔ ∀ z : ℚ × ℚ, Q (pt e f z) ↔ Q (mirrorPt (pt e f z)) := by
  constructor
  · intro h z; rw [← pt_qconj]; exact h z
  · intro h z; rw [pt_qconj]; exact h z

/-- The norm form is Galois-stable — the concrete instance of the dichotomy's left-hand side, and
the reason `NormForm`-style arithmetic (`prop:norm`) cannot locate an edge. -/
theorem norm_qconj (e f : ℚ) (z : ℚ × ℚ) :
    qmul e f (qconj z) (qconj (qconj z)) = qmul e f z (qconj z) := by
  simp only [qmul, qconj, Prod.mk.injEq]
  constructor <;> ring

end Erdos634.GaloisMirror
