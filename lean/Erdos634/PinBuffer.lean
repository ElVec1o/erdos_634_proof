import Mathlib.Tactic
import Erdos634.Frontier

/-!
# The `a|c|b` pin: the buffer overflow decides the chirality

Erdős #634, `e = 1`.  Empirically the base words that resist exhaustive search are exactly those in
which a corner-anchored `a`-run meets an `a|c` junction whose `c` is immediately followed by `b`
(research log, 2026-08-29: at `f = 12` every other orbit finishes in a few thousand nodes, while
these do not).  This file records what the configuration forces, which is more than the engine's
pruning currently sees.

**The configuration.**  At the junction `J` the west `a`-tile presents `γ` (orientation propagates
along a corner-anchored run) and the `c`-tile presents `β`, leaving a wedge of exactly
`π - γ - β = α`, filled by a single `α`-tile `X` (`PinLemma.pin_forces_single_alpha`).  `X`'s two
flanks at `J` are `b` and `c`.  But the rays it lies along are the `c`-tile's `a`-edge — of length
only `a` — and the west `a`-tile's `b`-edge, of length `b`.  So `X`'s flank along the first ray
**overflows** that tile's apex, by `L - a` where `L ∈ {b, c}`.

**The dichotomy.**

* `X` lays `b`: the overflow is `b - a`, a semigroup gap (`Frontier.gap_b_sub_a`), so the covering
  beyond the apex cannot be assembled from whole edges — `buffer_overflow_b_is_gap`.
* `X` lays `c`: the overflow is `c - a = f² - f = (f-1)·a`, exactly `f-1` `a`-edges
  (`buffer_overflow_c`), and `X`'s remaining flank `b` is then **flush** with the west tile's
  `b`-edge, both of length `b`.

So one chirality is killed algebraically and the other is rigidly pinned, with its overflow an
exact multiple of the shortest edge.  That is the structure the engine explores blindly, and it is
where the `a|c|b` words' cost lives.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.PinBuffer

/-- **The `b`-chirality overflows into a gap.**  Laying `X`'s `b`-flank along the `c`-tile's
`a`-edge overruns its apex by `b - a`, which no sum of tile edges represents. -/
theorem buffer_overflow_b_is_gap {f a b d x y z : ℕ}
    (hf : 2 ≤ f) (ha : a = f) (hb : b + 1 = f * f) (hd : d + a = b)
    (h : x * a + y * b + z * (f * f) = d) : False :=
  Erdos634.Frontier.gap_b_sub_a (e := 1) (f := f) (c := f * f)
    Nat.one_pos hf (Nat.coprime_one_left f) (by simpa using ha) (by simpa using hb) hd h

/-- **The `c`-chirality overflows by exactly `f-1` `a`-edges.**  `c - a = f² - f = (f-1)·f`. -/
theorem buffer_overflow_c (f : ℕ) : f * f - f = (f - 1) * f := by
  cases f with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one]
    ring_nf
    omega

/-- **The flush side.**  `X`'s other flank is `b`, and the west `a`-tile's `b`-edge is also `b`:
the two are coextensive, so that side contributes no overflow at all. -/
theorem buffer_flush (b : ℕ) : b - b = 0 := Nat.sub_self b

/-- **The dichotomy, assembled.**  Given that `X`'s flank along the short ray is `b` or `c`, either
the overflow is the gap `b - a` — impossible — or it is `c - a`, an exact multiple of `a`. -/
theorem buffer_dichotomy {f a b : ℕ} (hf : 2 ≤ f) (ha : a = f) (hb : b + 1 = f * f)
    (L : ℕ) (hL : L = b ∨ L = f * f) :
    (L = b ∧ ∀ x y z : ℕ, x * a + y * b + z * (f * f) ≠ L - a) ∨
    (L = f * f ∧ L - a = (f - 1) * f) := by
  have hbf : f ≤ b := by nlinarith
  rcases hL with h | h
  · refine Or.inl ⟨h, fun x y z hcon => ?_⟩
    have hd : (L - a) + a = b := by
      subst h; subst ha; omega
    exact buffer_overflow_b_is_gap hf ha hb hd hcon
  · exact Or.inr ⟨h, by rw [h, ha]; exact buffer_overflow_c f⟩

end Erdos634.PinBuffer
