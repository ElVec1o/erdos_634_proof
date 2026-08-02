/-
Collar.lean — arithmetic and induction skeleton of the Collar Lemma and the
Realizability Theorem, base-β family (Erdős #634).
No imports, no axioms: kernel-checked with the core toolchain only.

GEOMETRY (paper, Companion §realizability). For a base-β shape with unit cell
N₁ = 3f²−e², the m-target decomposes for every m ≥ 3 as the (m−2)-target anchored
at the apex plus a base collar; the collar assembles as
    [up-2-cell] + (m−3)·[parallelogram column] + [mirror column],
where the up-2-cell carries the 2-target tiling (4 unit cells), each column two
unit parallelograms (2 unit cells each ⇒ 4), and the mirror column its reflection.
Kernel-verified witnesses for the (e,f) = (1,2) member: Tiling44.lean (m = 2),
Tiling99.lean (m = 3), PgramTiling22.lean (the unit parallelogram, 22 tiles).

This file pins every counting step and the induction glue:
  · `collar_cells`     — (k+2)² = k² + 4(k+1): the collar is 4(m−1) unit cells (shape-free);
  · `collar_assembly`  — 4 + 4(m−3) + 4 = 4(m−1) for m ≥ 3: the three blocks fill it exactly;
  · `collar_count_12`  — the (1,2) member in tiles: 11(k+2)² = 11k² + 44(k+1);
  · seed counts        — 44 = 11·2², 99 = 11·3², 22 = 2·11 by kernel computation;
  · `two_step`         — bases 2, 3 + step m → m+2 reach every m ≥ 2.
With P m := "the m-target admits a tiling", the certificates give P 2 and P 3, the
collar gives the step, and `two_step` yields the REALIZABILITY THEOREM: N = 11m²
is realizable for every m ≥ 2 — with the m = 1 exclusion, the (1,2) spectrum is
complete: tileable iff m ≠ 1.
-/

namespace Erdos634.Collar

/-- The collar in unit cells, shape-free: (k+2)² − k² = 4(k+1).  With m = k+2 ≥ 2:
the band between the m-target and the apex-anchored (m−2)-target is 4(m−1) cells,
hence 4(m−1)·N₁ tiles for every base-β shape. -/
theorem collar_cells (k : Nat) : (k+2)*(k+2) = k*k + 4*(k+1) := by
  have h : (k+2)*(k+2) = k*k + 4*k + 4 := by
    simp [Nat.add_mul, Nat.mul_add]; omega
  omega

/-- The assembly fills the collar exactly: up-2-cell (4) + (m−3) columns (4 each)
+ mirror column (4) = 4(m−1) unit cells, for every m ≥ 3. -/
theorem collar_assembly (m : Nat) (h : 3 ≤ m) : 4 + 4*(m-3) + 4 = 4*(m-1) := by omega

/-- The (1,2) member in tiles (N₁ = 11): the collar carries 44(m−1) tiles. -/
theorem collar_count_12 (k : Nat) : 11*((k+2)*(k+2)) = 11*(k*k) + 44*(k+1) := by
  have h := collar_cells k
  rw [h]; omega

/-- **The collar count for an arbitrary member.** With unit cell `N₁ = 3f²−e²` tiles, the collar
between the `(k+2)`-target and the apex-anchored `k`-target carries `4N₁(k+1)` tiles — the
member-free form of `collar_count_12`, valid for every base-β shape. -/
theorem collar_count (N₁ k : Nat) : N₁ * ((k+2)*(k+2)) = N₁ * (k*k) + 4*N₁*(k+1) := by
  have h := collar_cells k
  rw [h, Nat.mul_add]
  have h4 : N₁ * (4*(k+1)) = 4*N₁*(k+1) := by
    rw [← Nat.mul_assoc, Nat.mul_comm N₁ 4]
  rw [h4]

/-- The same in the `(e,f)` parameters: `N₁ = 3f² − e²`. -/
theorem collar_count_ef (e f k : Nat) :
    (3*(f*f) - e*e) * ((k+2)*(k+2))
      = (3*(f*f) - e*e) * (k*k) + 4*(3*(f*f) - e*e)*(k+1) :=
  collar_count (3*(f*f) - e*e) k

/-- Seed counts, kernel-computed: the three certificates carry the right numbers. -/
theorem seed_m2 : 11*(2*2) = 44 := by decide
theorem seed_m3 : 11*(3*3) = 99 := by decide
theorem seed_pgram : 2*11 = 22 := by decide

/-- Induction skeleton: bases 2 and 3 with a two-step ladder reach every m ≥ 2. -/
def two_step (P : Nat → Prop) (h2 : P 2) (h3 : P 3)
    (hstep : ∀ m, 2 ≤ m → P m → P (m+2)) : ∀ m, 2 ≤ m → P m
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | 2, _ => h2
  | 3, _ => h3
  | (m+4), _ => hstep (m+2) (by omega) (two_step P h2 h3 hstep (m+2) (by omega))

/-- The reached set is exactly {m : 2 ≤ m}: the m = 1 exclusion (the prime theorem's
m = 1 case) is consistent with the ladder never visiting 1. -/
theorem ladder_misses_one : ¬ (2 ≤ 1) := by decide

end Erdos634.Collar
