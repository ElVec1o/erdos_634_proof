import Erdos634.Tiling44Bridge
import Erdos634.Tiling99Bridge

/-!
# `cor:elevenm`'s `N = 11m²` consequence

Erdős #634. "`N = 11m²` is a number of congruent triangles for every `m` divisible by 2 or 3" —
the paper's stated consequence, given `2, 3 ∈ S`. If `2 ∣ m`, write `m = 2j`, so `11m² = 44j²`, a
tile count by `Tiling44Bridge.exists_dissection_44_mul_sq`. If `3 ∣ m`, write `m = 3j`, so
`11m² = 99j²`, by `Tiling99Bridge.exists_dissection_99_mul_sq`.

Not a paper-row flip: `cor:elevenm` needs `1 ∉ S` and primitivity too, neither built.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.ElevenMBridge

open Erdos634.Tiling44Bridge Erdos634.Tiling99Bridge Erdos634.Geometry

/-- **`N = 11m²` is a tile count for every `m ≥ 1` divisible by 2 or 3** — the consequence
`cor:elevenm` states, given `2, 3 ∈ S(1,2)`. -/
theorem exists_dissection_11_mul_sq {m : ℕ} (hm : 0 < m) (h : 2 ∣ m ∨ 3 ∣ m) :
    ∃ N, N = 11 * m ^ 2 ∧ Nonempty (CongruentDissection N) := by
  rcases h with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hjpos : 0 < j := by omega
    obtain ⟨E, _⟩ := Erdos634.Tiling44Bridge.exists_dissection_44_mul_sq j hjpos
    refine ⟨44 * j ^ 2, ?_, ⟨E⟩⟩
    subst hj; ring
  · have hjpos : 0 < j := by omega
    obtain ⟨E, _⟩ := Erdos634.Tiling99Bridge.exists_dissection_99_mul_sq j hjpos
    refine ⟨99 * j ^ 2, ?_, ⟨E⟩⟩
    subst hj; ring

end Erdos634.ElevenMBridge
