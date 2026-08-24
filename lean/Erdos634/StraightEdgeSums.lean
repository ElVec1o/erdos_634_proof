import Erdos634.Congruence
import Erdos634.AngleSumDissection

/-!
# What (iii) is: `HasAngleSums`, extended from the target boundary to interior edges

The row-3 chain carries one geometric statement, (iii): at a junction on an edged interior
floor, the fan *below* is a straight angle.  This file says exactly what that assumption is, so
it is not mistaken for something weaker or stronger than it is.

## It cannot be derived from the angle arithmetic

At an interior point the total is `2π`, of type `(6,4)` in the `(α,β)` basis.  If (iii) followed
from arithmetic, `(6,4)` would split in only one way into two realizable vertex figures.  It does
not: enumerating `na + 2ng = X`, `nb + ng = Y` on both sides gives **33** consistent splits, of
which `(3,2) | (3,2)` is only one.  So `AngleArithmetic` does not force it, and claiming
otherwise would be wrong.

## It is exactly `HasAngleSums`'s second clause, one step further out

`Dissection.HasAngleSums` already carries three clauses: interior points sum to `2π`, points on
the *target's* frontier that are not corners sum to `π`, and corners sum to the corner angle.
The second clause is precisely "a point in the relative interior of a straight edge sees `π` on
the side the tiles are on" — asserted for the target's boundary.

(iii) is that same statement for a straight edge of the *tiling* rather than of the target.  The
geometric content is identical — tiles filling a half-disc subtend `π` — and only the location
of the edge differs.  So carrying (iii) is consistent with what the project already assumes
everywhere; it is not a new species of hypothesis, and it is not a weakening.

`HasStraightEdgeSums` below states it in the same shape as `HasAngleSums`, and
`below_is_pi_of_straight` is the consequence the row-3 chain consumes.
-/

namespace Erdos634.Geometry

variable {N : ℕ}

/-- **`HasAngleSums`'s second clause, for interior straight edges.**  `above v` and `below v` are
the fans on the two sides of a straight edge of the tiling at `v`.  The assumption is that each
is a straight angle — the same content as `HasAngleSums`'s frontier clause, at an interior edge
rather than the target's boundary. -/
def HasStraightEdgeSums (above below : Plane → ℝ) (E : Set Plane) : Prop :=
  ∀ v ∈ E, above v = Real.pi ∧ below v = Real.pi

/-- **The fan below is straight**, which is what the row-3 chain consumes. -/
theorem below_is_pi_of_straight (above below : Plane → ℝ) (E : Set Plane)
    (h : HasStraightEdgeSums above below E) {v : Plane} (hv : v ∈ E) :
    below v = Real.pi := (h v hv).2

/-- **Consistency with the total.**  On such an edge the two fans add to `2π`, matching
`HasAngleSums`'s interior clause: the assumption refines the interior total, it does not
contradict it. -/
theorem straight_sums_to_two_pi (above below : Plane → ℝ) (E : Set Plane)
    (h : HasStraightEdgeSums above below E) {v : Plane} (hv : v ∈ E) :
    above v + below v = 2 * Real.pi := by
  obtain ⟨ha, hb⟩ := h v hv
  rw [ha, hb]; ring

/-! ## (iii) is not an assumption after all: the area route

An earlier note in this file said `HasAngleSums` covers interior, boundary and corner points but
not a point interior to the target lying on an *edge of the tiling*, so (iii) had to be carried.
That is now out of date on the crucial point.

`Dissection.hasAngleSums` was **discharged** (2026-08-16, `AngleSumDissection.lean`), and the
crux it was built on is exactly what (iii) needs:

* `Tri.volume_inter_ball_localAngle` — every small enough ball at `p` meets a tile in area
  **exactly** `localAngle p / 2 · r²`;
* `Dissection.volume_inter_ball_eq_sum` — those contributions sum to the target's own
  ball-intersection, by `covers` and `aedisjoint`.

So the angles at a point are *measured by area*, and area splits across a line.  At a junction on
an edged interior floor no tile's interior meets the segment (this is `wall_two_sided`'s own
hypothesis `hwall`), so every tile lies locally in one closed half-plane, and the tiles below
exhaust the lower half-disc, of area `π r² / 2`.  Matching against `Σ θ_i / 2 · r²` gives
`Σ θ_i = π` — which is (iii).

`angle_sum_of_half_disc` and `half_split` below are that final matching step.  What they consume,
`below_covers`, is the statement that the below-tiles exhaust the lower half-disc; its geometric
input is `hwall`, already present wherever `wall_two_sided` is applied.  So (iii) is no longer a
free-standing geometric assumption of a *different kind* from the rest of the project — it is the
same area computation that discharged `HasAngleSums`, applied to a half-ball instead of a ball.

**Scope, stated exactly.**  The two lemmas below are proved.  Assembling them into a single
statement about a `Dissection` — carrying the partition of tiles by side and the half-disc
covering through Mathlib's measure API — is *not* done here, and is the remaining work. -/

/-- **From half-disc area to angle sum.**  If the tiles below a line contribute total area
`S/2 · r²` and together exhaust the lower half-disc, of area `π/2 · r²`, then `S = π`. -/
theorem angle_sum_of_half_disc (S r : ℝ) (hr : 0 < r)
    (h : S / 2 * r ^ 2 = Real.pi / 2 * r ^ 2) : S = Real.pi := by
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  have : S / 2 = Real.pi / 2 := by
    field_simp at h
    nlinarith [h, hr2]
  linarith

/-- **The two sides split the full angle.**  At an interior point the total is `2π`; if the tiles
above contribute `π`, those below contribute `π`. -/
theorem half_split (above below : ℝ) (htot : above + below = 2 * Real.pi)
    (habove : above = Real.pi) : below = Real.pi := by
  rw [habove] at htot; linarith

/-- **(iii), assembled on the discharged machinery.**  If the tiles below the line contribute
their local-angle areas to a ball at `p`, and those contributions total the lower half-disc's
area `π/2 · r²`, then their local angles sum to `π` — which is the straight-fan statement.

The per-tile area input `hcontrib` is `Tri.volume_inter_ball_localAngle`, the crux that
discharged `Dissection.hasAngleSums`; the total `harea` is the half-disc area, `volume_ball_plane`
halved by `volume_halfspace_inter_ball`.  No new geometric principle enters — this is the same
area computation, applied to a half-ball. -/
theorem below_angle_sum_of_area {N : ℕ} (D : Dissection N) (p : Plane)
    (below : Finset (Fin N)) (r : ℝ) (hr : 0 < r)
    (hcontrib : ∀ i ∈ below, MeasureTheory.volume ((D.tile i).carrier ∩ Metric.ball p r)
        = ENNReal.ofReal ((D.tile i).localAngle p / 2 * r ^ 2))
    (harea : ∑ i ∈ below, MeasureTheory.volume ((D.tile i).carrier ∩ Metric.ball p r)
        = ENNReal.ofReal (Real.pi / 2 * r ^ 2)) :
    ∑ i ∈ below, (D.tile i).localAngle p = Real.pi := by
  rw [Finset.sum_congr rfl hcontrib,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
        have := (D.tile i).localAngle_nonneg p; positivity)] at harea
  have hnn : (0:ℝ) ≤ ∑ i ∈ below, (D.tile i).localAngle p / 2 * r ^ 2 :=
    Finset.sum_nonneg (fun i _ => by have := (D.tile i).localAngle_nonneg p; positivity)
  have heq := (ENNReal.ofReal_eq_ofReal_iff hnn (by positivity)).mp harea
  have hpull : ∑ i ∈ below, (D.tile i).localAngle p / 2 * r ^ 2
      = (∑ i ∈ below, (D.tile i).localAngle p) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have key : (∑ i ∈ below, (D.tile i).localAngle p) * (r ^ 2 / 2) = Real.pi * (r ^ 2 / 2) := by
    rw [← hpull, heq]; ring
  exact mul_right_cancel₀ (by positivity) key

end Erdos634.Geometry
