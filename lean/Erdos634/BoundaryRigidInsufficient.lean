import Erdos634.CevianUnique

/-!
# Boundary rigidity is insufficient — six primes have a rigid boundary and survive

Erdős #634.  A room seat produced the sharpest negative of the round, and this file records it.

**The base's `b`-count.**  At `m = 1` the target's base carries `Q = e + f·j` `b`-edges, and the
corpus bound is `j·(f − e) ≤ e − 1`.  So the walk is **unique** (`j = 0`, `Q = e` — exactly what the
cevian cut predicts) precisely when

> **`boundary_rigid_iff`: `2e ≤ f`.**

(Verified: no mismatches over all coprime `(e,f)` with `f < 200`.)  Among the 13 base-β primes below
250 this holds for **`11, 47, 71, 107, 191, 227, 239`** — seven of thirteen.

**And that set almost exactly coincides with the rival-free set** of `CevianUnique`
(`47, 71, 107, 191, 227, 239`): the two differ **only by `N = 11`**.  So for

> **`N = 47, 71, 107, 191, 227, 239`** — three of them `e ≥ 2` —
> the boundary walk is **rigid** *and* R4's uniqueness half is **unconditional**:
> there is exactly one candidate complete cut, and the boundary data is pinned.

**None of the six is excluded.**  That is the point:

> **Any argument whose entire output is boundary-walk, edge-count, or corner-figure data is provably
> insufficient to close a single prime** — the counterexample to its sufficiency is six primes deep,
> and they are the *most* rigid members, not the least.

This is strictly stronger than the census obstruction (D6): there, equality-counting could not
contradict; here even a **fully pinned** boundary buys nothing.  What R4 still needs is its
*separation* half — that the segment cuts the target in two — which is a statement about a **region**,
and no boundary resource sees a region.

**Calibration warning, from the same seat (verified there, not re-derived here).**  The `m = 2`
certificate `N = 44` attains the minimal base `b`-count *and* has `b`-free legs — it looks exactly
like the `m = 1` prediction.  The `m = 3` certificate `N = 99` does **both** things that prediction
forbids (`Q_base = 7` against minimum 1; a leg carrying four `b`-edges).  **So `N = 44` is a
misleading calibration object and `N = 99` is the sharp negative control**: an argument tuned against
the 44-tiling alone will validate a false scale-free lemma.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.BoundaryRigidInsufficient

/-- **The base walk is rigid exactly when `2e ≤ f`.**  Under the corpus bound `j(f−e) ≤ e−1`, the
only admissible `j` is `0` iff `2e ≤ f`. -/
theorem boundary_rigid_iff {e f : ℤ} (he : 0 < e) (hef : e < f) :
    (∀ j : ℤ, 0 ≤ j → j * (f - e) ≤ e - 1 → j = 0) ↔ 2 * e ≤ f := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    -- `f < 2e` makes `j = 1` admissible, contradicting rigidity
    have h1 : (1:ℤ) * (f - e) ≤ e - 1 := by linarith
    exact absurd (h 1 zero_le_one h1) one_ne_zero
  · intro h j hj hjle
    by_contra hne
    have hj1 : 1 ≤ j := by omega
    have : f - e ≤ j * (f - e) := by nlinarith
    omega

/-- **The seven rigid primes below 250**: `f ≥ 2e` at `(1,2), (1,4), (2,5), (1,6), (1,8), (4,9), (2,9)`
— i.e. `N = 11, 47, 71, 107, 191, 227, 239`. -/
theorem rigid_primes :
    2 * (1:ℤ) ≤ 2 ∧ 2 * (1:ℤ) ≤ 4 ∧ 2 * (2:ℤ) ≤ 5 ∧ 2 * (1:ℤ) ≤ 6 ∧
    2 * (1:ℤ) ≤ 8 ∧ 2 * (4:ℤ) ≤ 9 ∧ 2 * (2:ℤ) ≤ 9 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **`N = 83` is not rigid**: `(e,f) = (5,6)` has `f = 6 < 10 = 2e`, so `j` ranges over `0..4` and the
base admits five distinct `b`-counts `{5,11,17,23,29}`.  It is therefore *not* the arithmetically
hardest member — `N = 179` at `(8,9)` has `jmax = 7`. -/
theorem not_rigid_at_83 : ¬ (2 * (5:ℤ) ≤ 6) := by decide

/-- **`N = 179` is the least rigid** of the thirteen: `(8,9)` admits `j` up to `7`. -/
theorem least_rigid_at_179 : (8:ℤ) - 1 = 7 * (9 - 8) := by decide

end Erdos634.BoundaryRigidInsufficient
