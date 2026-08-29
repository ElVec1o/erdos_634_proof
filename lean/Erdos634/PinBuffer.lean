import Mathlib.Tactic
import Erdos634.Frontier
import Erdos634.AnchoredChain

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

/-! ## The surviving chirality feeds the ladder

With the `b`-chirality dead, `X` lays its `c` along the short ray and overruns the `c`-tile's apex
`A` by `(f-1)a`.  At `A` the `c`-tile shows `γ` — its angles are `β` at the junction, `α` at the far
base end, hence `γ` at the apex — and `X`'s `c`-edge passes straight through, contributing `π`.
The pocket that remains is therefore

  `2π - γ - π = π - γ = α + β`,

whose figure is unique: one `α` and one `β` (`pocket_at_apex_figure`).  By
`AnchoredChain.no_second_through_with_gamma` no further edge passes through `A`, so both of those
tiles have a vertex there.

That is exactly the `α+β` pocket the `T`-vertex ladder runs on
(`PinLemma.t_vertex_fill`), so the surviving chirality of the hard configuration feeds directly
into machinery already formalized rather than into new geometry. -/

/-- **The pocket at the apex is `α + β`.**  From `γ = 2α + β` and `3α + 2β = π`. -/
theorem pocket_at_apex (α β γ : ℝ) (hγ : γ = 2 * α + β) (hπ : 3 * α + 2 * β = Real.pi) :
    2 * Real.pi - γ - Real.pi = α + β := by rw [hγ]; linarith

/-- **Its figure is forced: one `α` and one `β`.** -/
theorem pocket_at_apex_figure (x y z : ℕ) (h1 : x + 2 * z = 1) (h2 : y + z = 1) :
    x = 1 ∧ y = 1 ∧ z = 0 := by omega

/-! ## The runway is crystalline, and where that stops short

The overflow `A → Q` on `X`'s `c`-edge has length exactly `c - a = (f-1)a`.  Both longer edges
exceed it — `b = f² - 1 > f² - f` and `c = f² > f² - f` for `f ≥ 2` — so **any covering confined to
the runway consists of exactly `f-1` `a`-edges** (`runway_forces_a_edges`).  With the orientation
propagating from the pocket at `A`, that run carries no branching at all: its edge types are
forced, and so are its orientations.

What the calculation does **not** give is a contradiction at the far end.  Two escapes survive, and
both are the crossing question in this configuration:

* a covering edge may **overrun `Q`** — a `b` starting at `A` overruns by `b - (f-1)a = f - 1`, and
  a `c` by `f` (`overrun_amounts`).  The first of these is strictly below the minimal edge `a = f`,
  so it is a semigroup gap, and killing it needs the anchoring that this programme has never
  supplied;
* if the run is confined, the terminal vertex `Q` carries `X`'s `β` against the last tile's `γ`,
  leaving `4α + 2β`, whose figures are `(4,2,0)`, `(2,1,1)` and `(0,0,2)` — three options, no
  contradiction.

So the buffer analysis removes the edge-type branching entirely and localises the residue to a
single overrun at a single named vertex.  It does not close it. -/

/-- **The runway admits only `a`-edges.**  `(f-1)a` is shorter than both `b` and `c`. -/
theorem runway_forces_a_edges (f : ℕ) (hf : 2 ≤ f) :
    (f - 1) * f < f * f - 1 ∧ (f - 1) * f < f * f := by
  have hF : 2 * f ≤ f * f := by nlinarith
  have h : (f - 1) * f = f * f - f := by
    cases f with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring_nf; omega
  omega

/-- **The overrun amounts.**  A `b` covering the runway from its start overruns `Q` by `f-1`; a `c`
overruns by `f`.  The first is below the minimal edge length, hence a gap. -/
theorem overrun_amounts (f : ℕ) (hf : 2 ≤ f) :
    (f * f - 1) - (f - 1) * f = f - 1 ∧ (f * f) - (f - 1) * f = f := by
  have hF : 2 * f ≤ f * f := by nlinarith
  have h : (f - 1) * f = f * f - f := by
    cases f with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring_nf; omega
  omega

/-! ## The sub-`a` remainder forces a further overrun — it does not kill the branch

It is tempting to argue that the `b`-overrun dies because `f - 1 < a`, a segment shorter than the
shortest side being uncoverable.  **That argument does not apply here.**  The `f-1` is not a
segment awaiting coverage; it is part of the `b`-edge itself.  At `Q` exactly one tile has the
point interior to an edge (the `b`-tile, contributing `π`) while `X` has a vertex there, so
`AnchoredChain`'s three-tile exclusion is not triggered, and the budget is satisfied:
`β + π = 3α + 3β` leaves `3α + β`, whose figures `(3,1,0)` and `(1,0,1)` are admissible.

What *is* true, and is the usable residue, is weaker and one step further out: past `Q` the
`b`-edge continues for only `f - 1`, while **every** tile edge is at least `a = f`.  So the first
tile filling the wedge at `Q` must overrun the `b`-edge's far endpoint.  The branch is pushed one
step, not closed.

For the `c`-overrun the corresponding remainder is exactly `a`: a `c` laid from the runway's start
overruns `Q` by `c - (f-1)a = f`, one whole `a`-edge, flush. -/

/-- **Every tile edge exceeds `f - 1`.**  Hence any edge laid along a segment of that length
overruns it: the sub-`a` remainder forces a further overrun rather than a contradiction. -/
theorem sub_a_forces_overrun (f L : ℕ) (hf : 2 ≤ f)
    (hL : L = f ∨ L = f * f - 1 ∨ L = f * f) : f - 1 < L := by
  have hF : 2 * f ≤ f * f := by nlinarith
  rcases hL with h | h | h <;> omega

/-- **The `c`-overrun is exactly one `a`-edge.** -/
theorem c_overrun_is_flush (f : ℕ) (hf : 2 ≤ f) : f * f - (f - 1) * f = f := by
  have hF : 2 * f ≤ f * f := by nlinarith
  have h : (f - 1) * f = f * f - f := by
    cases f with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring_nf; omega
  omega

end Erdos634.PinBuffer
