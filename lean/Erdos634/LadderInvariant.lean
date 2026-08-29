import Mathlib.Tactic
import Erdos634.PinPlumbing

/-!
# The ladder invariant: flush placement algebra, exact

Erdős #634, the mirrored-branch march.  Verified exactly in `ℚ(√D)` at two members (research log,
2026-08-26): each block's `c`-edge carries the previous block's apex as a `T`-vertex at parameter
exactly `b/c`, with overrun exactly `c - b = 1`.  The geometric content is the flush placement —
the partner lays its `c`-edge along the `a`-tile's `b`-edge direction from the shared pin, which
the pin forcing supplies; the algebra is then one line, banked here.

* `flush_overrun_mem`   — the apex is the parameter-`b/c` point of the `c`-edge: it lies on it.
* `flush_split_lengths` — the split lengths are exactly `b` and `c - b` (times the direction's
  norm; with a unit direction, exactly `b` and `1`).

With `at_most_two_through` (no transversal crossings), `t_vertex_fill` (the forced `{α,β}` pair at
the split point), `wall_run_equation` (whole-edge runs), and `one_is_gap` (the length-`1` stub is
uncoverable by whole edges), these are the step ingredients of the termination induction.  The
induction itself — the bookkeeping that the pattern repeats until the trailing `a`-run is
exhausted and then dies — is the remaining assembly.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LadderInvariant

open Erdos634.Geometry

/-- **The apex lies on the `c`-edge.**  With apex `P + b•u` and tip `P + c•u`, `0 ≤ b ≤ c`, the
apex is on the segment from `P` to the tip. -/
theorem flush_overrun_mem (P : Plane) (u : Plane) (b c : ℝ)
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    P + b • u ∈ segment ℝ P (P + c • u) := by
  rcases eq_or_lt_of_le (hb.trans hbc) with hc0 | hc0
  · -- c = 0 forces b = 0
    have hb0 : b = 0 := le_antisymm (hbc.trans hc0.ge) hb
    simp [hb0, ← hc0]
  · have hcne : c ≠ 0 := ne_of_gt hc0
    refine ⟨1 - b / c, b / c, ?_, by positivity, by ring, ?_⟩
    · have : b / c ≤ 1 := (div_le_one hc0).mpr hbc
      linarith
    · have hexp : (1 - b / c) • P + (b / c) • (P + c • u) = P + ((b / c) * c) • u := by
        module
      rw [hexp, div_mul_cancel₀ b hcne]

/-- **The split lengths.**  `edist (P + b•u) (P + c•u) = (c - b) * ‖u‖` and
`edist P (P + b•u) = b * ‖u‖`. -/
theorem flush_split_lengths (P : Plane) (u : Plane) (b c : ℝ)
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    dist (P + b • u) (P + c • u) = (c - b) * ‖u‖ ∧
    dist P (P + b • u) = b * ‖u‖ := by
  constructor
  · rw [dist_eq_norm]
    have : P + b • u - (P + c • u) = (b - c) • u := by module
    rw [this, norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith : b - c ≤ 0)]
    ring
  · rw [dist_eq_norm]
    have : P - (P + b • u) = (-b) • u := by module
    rw [this, norm_smul]
    simp [abs_of_nonneg hb]

/-- **With a unit direction the overrun is exactly `c - b`** — for the tile, exactly `1`. -/
theorem flush_overrun_unit (P : Plane) (u : Plane) (hu : ‖u‖ = 1) (b c : ℝ)
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    dist (P + b • u) (P + c • u) = c - b := by
  rw [(flush_split_lengths P u b c hb hbc).1, hu, mul_one]

/-! ## The step identity, the march bound, and the assembled conditional

The exact invariant's algebraic core is the law of cosines with the tile's own included angle:
the apex `P + c•w` (with `w` the unit direction of the `a`-tile's `c`-edge, whose cosine against
the base is `(a² + c² - b²)/(2ac)`) lies at distance exactly `b` from the next pin `P + (a,0)`.
So each block's landing is the tile's defining relation, not a coincidence — and the ladder
advances one base letter `a` per block, hence terminates within the trailing `a`-run. -/

/-- **The step identity.**  If `w = (w₁, w₂)` is a unit vector with `w₁ = (a² + c² - b²)/(2ac)`
(the cosine of the tile's angle between sides `a` and `c`), then `‖c•w - (a, 0)‖² = b²`:
the apex lands at distance exactly `b` from the next pin. -/
theorem ladder_step_identity (a b c w₁ w₂ : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hunit : w₁ ^ 2 + w₂ ^ 2 = 1) (hcos : 2 * a * c * w₁ = a ^ 2 + c ^ 2 - b ^ 2) :
    (c * w₁ - a) ^ 2 + (c * w₂) ^ 2 = b ^ 2 := by nlinarith [hunit, hcos]

/-- **The march is bounded.**  Pins advance by `a` per block inside a base of length `L`, so the
block count is at most `L / a`. -/
theorem march_bounded (a L x₀ : ℕ) (ha : 0 < a) (k : ℕ) (hin : x₀ + k * a ≤ L) :
    k ≤ L / a := by
  have h1 : k * a ≤ L := le_trans (Nat.le_add_left _ _) hin
  exact Nat.le_div_iff_mul_le ha |>.mpr h1

/-- **The terminal kill, assembled.**  When the march can no longer continue, the final stub of
length `c - b = 1` must be covered by whole edges, and the run equation then demands
`x·a + y·b + z·c = 1` — impossible.  Stated on the run-equation output form
(`wall_run_equation` supplies it; `one_is_gap` kills it). -/
theorem terminal_kill (f x y z : ℕ) (hf : 2 ≤ f)
    (hcover : x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1) : False :=
  Erdos634.FanKill.one_is_gap f x y z hf hcover

/-! ## WITHDRAWN (2026-08-29): `uniform_bp2_conditional` was circular

That theorem's `march` hypothesis was `∃ x y z, x·f + y·(f²-1) + z·f² = 1` — verbatim the
negation of `FanKill.one_is_gap`'s conclusion — so it read `False → False`, mentioned no
`Dissection`, no word and no junction, and its `f` was a bare natural.  Adversarial review caught
it; it is deleted.  `terminal_kill` above is retained only as the named endpoint of the intended
argument, and is itself a direct alias of `one_is_gap`. -/

end Erdos634.LadderInvariant
