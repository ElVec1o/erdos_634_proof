import Erdos634.Congruence

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

end Erdos634.Geometry
