import Erdos634.Inflation

/-!
# Draft: A1 — a corner-anchored base a-run is all-BG (agent session 2026-08-29)

`orient_monotone` (S5) says an admissible run is `GB^j BG^k`.  The corner fill pins the FIRST
tile to `BG` (`corner_beta_unique`: the corner tile presents `β` at the target corner, hence
`γ` at its east end).  Composition: the whole run is `BG^L`, so every interior junction of the
run carries `{γ west, β east}` and the run's east end — the flank WEST of the following
`c`-junction in any word `a…a c …` — is `γ`.  Consequence for the cp≥3 escape orbits: the
four-flank case analysis at the a|c junction collapses to the cp=2 pin dichotomy
(`(γ,α)` / `(γ,β)`); the `(β,·)` combinations never occur at the representative word
(mirror-normalize so the `c` precedes the `b`).
-/

namespace Erdos634.RunOrientation

open Erdos634.Inflation Erdos634.Inflation.Orient

/-- **A1.**  An admissible orientation run that STARTS with `BG` is constantly `BG`. -/
theorem corner_anchored_run_all_BG (L : List Orient)
    (h : L.Chain' (fun l r => admissiblePair l r = true))
    (hhead : L.head? = some Orient.BG) :
    L = List.replicate L.length Orient.BG := by
  obtain ⟨j, k, hjk⟩ := orient_monotone L h
  cases j with
  | zero =>
      subst hjk
      simp
  | succ j' =>
      exfalso
      subst hjk
      rw [List.replicate_succ] at hhead
      simp [List.head?] at hhead

/-- The east end of a corner-anchored run presents `γ`: its last orientation is `BG`. -/
theorem corner_anchored_run_last (L : List Orient)
    (h : L.Chain' (fun l r => admissiblePair l r = true))
    (hhead : L.head? = some Orient.BG) (hne : L ≠ []) :
    L.getLast hne = Orient.BG := by
  have hall := corner_anchored_run_all_BG L h hhead
  have hforall : ∀ x ∈ L, x = Orient.BG := by
    intro x hx
    rw [hall] at hx
    exact List.eq_of_mem_replicate hx
  exact hforall _ (List.getLast_mem hne)

end Erdos634.RunOrientation

#print axioms Erdos634.RunOrientation.corner_anchored_run_all_BG
#print axioms Erdos634.RunOrientation.corner_anchored_run_last
