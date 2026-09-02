import Erdos634.TileAt
import Erdos634.Congruence

/-!
# `lem:ccornerside`'s core, for a real tile of a real `CongruentDissection`

Erdős #634. `TilePlacement.c_corner_side_a` is the abstract `Tri`-level fact: a triangle laying
`b` and `c` at a vertex lays `a` on the remaining edge. Connecting it to a *real* tile of a real
`CongruentDissection` needs the tile's own three side lengths matched to the model's `a`/`b`/`c` —
`Congruence.Tri.Congruent.sideMultiset_eq` (already landed) gives this as an unordered multiset;
`Tri.sideMultiset_shift` below removes the remaining gap, that the multiset doesn't depend on
which vertex index the caller starts listing pairs from.

Axiom-clean; no `sorry`.
-/

open Erdos634.Geometry Erdos634.Geometry.Dissection Erdos634.TilePlacement

/-- The pairwise-distance multiset of a `Tri`'s three sides, independent of the starting vertex
index used to list them. -/
theorem Tri.sideMultiset_shift (T : Tri) (j : Fin 3) :
    ({dist (T.pts j) (T.pts (j+1)), dist (T.pts (j+2)) (T.pts j),
      dist (T.pts (j+1)) (T.pts (j+2))} : Multiset ℝ)
    = {dist (T.pts 0) (T.pts 1), dist (T.pts 2) (T.pts 0), dist (T.pts 1) (T.pts 2)} := by
  fin_cases j
  · rfl
  · show ({dist (T.pts 1) (T.pts 2), dist (T.pts 0) (T.pts 1), dist (T.pts 2) (T.pts 0)}
      : Multiset ℝ) = _
    show ({_, _, _} : Multiset ℝ) = {_, _, _}
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    simp only [add_comm, add_assoc, add_left_comm]
  · show ({dist (T.pts 2) (T.pts 0), dist (T.pts 1) (T.pts 2), dist (T.pts 0) (T.pts 1)}
      : Multiset ℝ) = _
    show ({_, _, _} : Multiset ℝ) = {_, _, _}
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    simp only [add_comm, add_assoc, add_left_comm]

/-- **`lem:ccornerside`'s core, for a real `CongruentDissection`'s tile.** If a tile congruent to
the model lays the model's `b`-side and `c`-side at a vertex `j` (`hopp`, `hbase`), it lays the
`a`-side on the remaining edge. Real content about an actual tile of an actual dissection, not
merely the abstract `Tri`-level `c_corner_side_a` — this is `lem:ccornerside`'s "a corner tile
laying `c` on the base lays `a` on the side", stated for any real edge of a real dissection's
tile, not tied to a base corner specifically. -/
theorem congruentDissection_lays_a {N : ℕ} (D : CongruentDissection N)
    (hac : sideOpp D.model 2 ≠ sideOpp D.model 1)
    (i : Fin N) (j : Fin 3)
    (hopp : dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 0)
    (hbase : dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 1) :
    dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 2 := by
  have hcong := D.tiles_congruent i
  have hmulti := hcong.sideMultiset_eq
  have hshift := Tri.sideMultiset_shift (D.tile i) j
  apply c_corner_side_a (D.tile i) j (sideOpp D.model 2) (sideOpp D.model 0) (sideOpp D.model 1)
  · have : (0:ℝ) < sideOpp D.model 0 :=
      dist_pos.mpr (Erdos634.TilePlacement.pts_ne D.model (by decide : (1:Fin 3) ≠ 2))
    exact this.ne'
  · exact hac
  · exact hopp
  · rw [hshift, hmulti]
    simp only [sideOpp, show (2:Fin 3)+1=0 from rfl, show (2:Fin 3)+2=1 from rfl,
      show (0:Fin 3)+1=1 from rfl, show (0:Fin 3)+2=2 from rfl,
      show (1:Fin 3)+1=2 from rfl, show (1:Fin 3)+2=0 from rfl]
    show ({_,_,_}:Multiset ℝ) = {_,_,_}
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    simp only [add_comm, add_assoc, add_left_comm]
  · exact hbase
