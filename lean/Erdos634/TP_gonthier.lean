import Erdos634.Tiling44

set_option maxRecDepth 40000

/-!
# A combinatorial (hypermap) model of the certified 44-tiling

Erdős #634, room `tileplace`, mode GONTHIER.  The Four Colour Theorem was made tractable by
replacing point-set topology with a **combinatorial** structure — darts with an edge involution and
a face permutation — entering the geometry once, at the boundary.  This file tests that programme
on the corpus's smallest certified instance, `(e,f)=(1,2)`, `m=2`, `N=44` (`Tiling44.lean`, exact
`ℤ[√15]` coordinates).

## The obstacle a naive hypermap hits, and the fix

The tiling is **not edge-to-edge** (`rem:noedgetoedge`; `PAPER_MAP.md` records a T-junction, tile
14's vertex `(138, 6√15)` strictly inside tile 28's edge `(122,6√15)–(154,6√15)`).  So "darts = tile
edges" is *not* a hypermap: 13 vertex-inside-edge incidences occur, and under the strict full-edge
adjacency the dual graph is disconnected.

The fix is the **arrangement refinement**: split every tile edge at each tiling vertex lying in its
relative interior.  That is a finite, definable operation on any `Dissection` (the vertex set has at
most `3N` points).  On the certified 44-tiling the refinement is a genuine hypermap, and this file
verifies it by `decide` in exact integer arithmetic.

## What is verified here (all by `decide`, axiom-clean, no `sorry`)

With the outer face adjoined:

* `darts` — 162 directed refined segments (145 tile-side, 17 outer-face);
* `alphaT` — the edge involution: fixed-point free, reverses the segment, and **always changes
  face**.  Hence exactly two faces meet along every refined segment: `81` edge orbits;
* `sigmaT` — the face permutation: `45` orbits (`44` tiles and the outer face), each the closed
  boundary walk of its face, head-to-tail, in the order the certificate's own vertices give;
* `nodeCyc` — the node orbits of `σ∘α`: exactly `38`, and each has a **constant source point**,
  which is the corresponding tiling vertex.  So the combinatorial node count *is* the geometric
  vertex count;
* `bfsOrder` — the map is connected;
* Euler: `V − E + F = 38 − 81 + 45 = 2`.

## The one geometric input, isolated

`chart_faithful` is where the plane is entered, and it is entered once: every vertex of every tile
of `Tiling44.tiles` has the shape `(x, y√15)` with `x, y ∈ ℤ` (its `Pt` fields `xb` and `ya`
vanish).  In that chart collinearity and betweenness are decided by integer arithmetic — `cr` is
the cross product in units of `√15`, `dt` the metric form `u₁v₁ + 15u₂v₂` — so every incidence
statement below is exact and no real number appears.

## Honest scope

This is a **positive control and a substrate**, not a flip of any paper row.  It shows the
combinatorial layer is well-posed and non-vacuous on a real dissection; it does not by itself prove
anything about a general dissection, and the Euler relation it establishes is provably useless for
the crossing question (`prop:ninetools` closes Euler and angle-sum counting).  See
`private/ROOM/tileplace/report_gonthier.md` for the labels and the named obstruction.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.TPGonthier

/-! ## The chart, and the one place geometry is entered -/

/-- A point of the plane in the `√15` chart: `(x, y)` means `(x, y√15)`. -/
abbrev Pt2 := Int × Int

/-- A dart: `(face, edgeIndex, source, target)`.  Faces `0…43` are the tiles, face `44` is the
outer face (the target's boundary, traversed with the opposite orientation). -/
abbrev Dart := Nat × Nat × Pt2 × Pt2

/-- The chart map on `Tiling44.Pt = (xa, xb, ya, yb)`. -/
def chart (p : Tiling44.Pt) : Pt2 := (p.1, p.2.2.2)

/-- The chart is faithful on a point when its `xb` and `ya` fields vanish. -/
def chartOK (p : Tiling44.Pt) : Bool := (p.2.1 == 0) && (p.2.2.1 == 0)

def tilesChartOK : Bool :=
  Tiling44.tiles.all fun t =>
    chartOK (Tiling44.t1 t) && chartOK (Tiling44.t2 t) && chartOK (Tiling44.t3 t)

/-- **The geometry, entered once.**  Every vertex of every certified tile has the exact form
`(x, y√15)` with `x, y ∈ ℤ`.  Everything after this line is integer arithmetic. -/
theorem chart_faithful : tilesChartOK = true := by decide

/-! ## Exact predicates in the chart -/

def sub2 (a b : Pt2) : Pt2 := (a.1 - b.1, a.2 - b.2)

/-- Cross product, in units of `√15`: zero exactly when the three points are collinear. -/
def cr (o a b : Pt2) : Int := (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

/-- The metric form: `dt u v` is the true inner product of `(u₁, u₂√15)` and `(v₁, v₂√15)`. -/
def dt (u v : Pt2) : Int := u.1 * v.1 + 15 * u.2 * v.2

/-- `p` lies on the closed segment `[a,b]`. -/
def onClosed (p a b : Pt2) : Bool :=
  (cr a b p == 0) && (0 ≤ dt (sub2 p a) (sub2 b a))
    && (dt (sub2 p a) (sub2 b a) ≤ dt (sub2 b a) (sub2 b a))

/-- `v` lies strictly inside the open segment `(p,q)`. -/
def strictBetween (v p q : Pt2) : Bool :=
  (cr p q v == 0) && (0 < dt (sub2 v p) (sub2 q p))
    && (dt (sub2 v p) (sub2 q p) < dt (sub2 q p) (sub2 q p))

def verts : List Pt2 := [
  (0,0), (16,0), (22,6), (32,0), (38,6), (44,12), (48,0), (54,6),
  (60,12), (64,0), (66,18), (70,6), (72,8), (76,12), (78,2), (80,16),
  (82,18), (85,3), (86,10), (88,24), (92,4), (94,18), (96,0), (100,12),
  (106,6), (110,18), (111,9), (116,12), (117,3), (122,6), (128,0), (132,12),
  (138,6), (143,9), (149,3), (154,6), (160,0), (176,0)]

def darts : List Dart := [
  (0,0,(0,0),(16,0)), (0,1,(16,0),(22,6)), (0,2,(22,6),(0,0)), (1,0,(16,0),(32,0)),
  (1,1,(32,0),(38,6)), (1,2,(38,6),(16,0)), (2,0,(16,0),(38,6)), (2,1,(38,6),(22,6)),
  (2,2,(22,6),(16,0)), (3,0,(32,0),(48,0)), (3,1,(48,0),(54,6)), (3,2,(54,6),(32,0)),
  (4,0,(32,0),(54,6)), (4,1,(54,6),(38,6)), (4,2,(38,6),(32,0)), (5,0,(48,0),(64,0)),
  (5,1,(64,0),(70,6)), (5,2,(70,6),(48,0)), (6,0,(48,0),(70,6)), (6,1,(70,6),(54,6)),
  (6,2,(54,6),(48,0)), (7,0,(64,0),(96,0)), (7,1,(96,0),(85,3)), (7,2,(85,3),(78,2)),
  (7,2,(78,2),(64,0)), (8,0,(64,0),(78,2)), (8,1,(78,2),(72,8)), (8,2,(72,8),(70,6)),
  (8,2,(70,6),(64,0)), (9,0,(96,0),(128,0)), (9,1,(128,0),(117,3)), (9,2,(117,3),(96,0)),
  (10,0,(96,0),(117,3)), (10,1,(117,3),(85,3)), (10,2,(85,3),(96,0)), (11,0,(128,0),(160,0)),
  (11,1,(160,0),(149,3)), (11,2,(149,3),(128,0)), (12,0,(128,0),(149,3)), (12,1,(149,3),(117,3)),
  (12,2,(117,3),(128,0)), (13,0,(160,0),(176,0)), (13,1,(176,0),(154,6)), (13,2,(154,6),(160,0)),
  (14,0,(160,0),(154,6)), (14,1,(154,6),(138,6)), (14,2,(138,6),(149,3)), (14,2,(149,3),(160,0)),
  (15,0,(78,2),(85,3)), (15,0,(85,3),(92,4)), (15,1,(92,4),(86,10)), (15,2,(86,10),(78,2)),
  (16,0,(78,2),(86,10)), (16,1,(86,10),(72,8)), (16,2,(72,8),(78,2)), (17,0,(85,3),(117,3)),
  (17,1,(117,3),(106,6)), (17,2,(106,6),(92,4)), (17,2,(92,4),(85,3)), (18,0,(117,3),(149,3)),
  (18,1,(149,3),(138,6)), (18,2,(138,6),(117,3)), (19,0,(117,3),(138,6)), (19,1,(138,6),(122,6)),
  (19,1,(122,6),(106,6)), (19,2,(106,6),(117,3)), (20,0,(92,4),(106,6)), (20,1,(106,6),(100,12)),
  (20,2,(100,12),(92,4)), (21,0,(92,4),(100,12)), (21,1,(100,12),(86,10)), (21,2,(86,10),(92,4)),
  (22,0,(22,6),(38,6)), (22,1,(38,6),(44,12)), (22,2,(44,12),(22,6)), (23,0,(38,6),(54,6)),
  (23,1,(54,6),(60,12)), (23,2,(60,12),(38,6)), (24,0,(38,6),(60,12)), (24,1,(60,12),(44,12)),
  (24,2,(44,12),(38,6)), (25,0,(54,6),(70,6)), (25,1,(70,6),(72,8)), (25,1,(72,8),(76,12)),
  (25,2,(76,12),(54,6)), (26,0,(54,6),(76,12)), (26,1,(76,12),(60,12)), (26,2,(60,12),(54,6)),
  (27,0,(106,6),(122,6)), (27,1,(122,6),(111,9)), (27,1,(111,9),(100,12)), (27,2,(100,12),(106,6)),
  (28,0,(122,6),(138,6)), (28,0,(138,6),(154,6)), (28,1,(154,6),(143,9)), (28,2,(143,9),(122,6)),
  (29,0,(122,6),(143,9)), (29,1,(143,9),(111,9)), (29,2,(111,9),(122,6)), (30,0,(72,8),(86,10)),
  (30,1,(86,10),(80,16)), (30,2,(80,16),(76,12)), (30,2,(76,12),(72,8)), (31,0,(111,9),(143,9)),
  (31,1,(143,9),(132,12)), (31,2,(132,12),(111,9)), (32,0,(111,9),(132,12)), (32,1,(132,12),(116,12)),
  (32,1,(116,12),(100,12)), (32,2,(100,12),(111,9)), (33,0,(86,10),(100,12)), (33,1,(100,12),(94,18)),
  (33,2,(94,18),(86,10)), (34,0,(86,10),(94,18)), (34,1,(94,18),(80,16)), (34,2,(80,16),(86,10)),
  (35,0,(44,12),(60,12)), (35,1,(60,12),(66,18)), (35,2,(66,18),(44,12)), (36,0,(60,12),(76,12)),
  (36,1,(76,12),(80,16)), (36,1,(80,16),(82,18)), (36,2,(82,18),(60,12)), (37,0,(60,12),(82,18)),
  (37,1,(82,18),(66,18)), (37,2,(66,18),(60,12)), (38,0,(100,12),(116,12)), (38,1,(116,12),(94,18)),
  (38,2,(94,18),(100,12)), (39,0,(116,12),(132,12)), (39,1,(132,12),(110,18)), (39,2,(110,18),(116,12)),
  (40,0,(116,12),(110,18)), (40,1,(110,18),(94,18)), (40,2,(94,18),(116,12)), (41,0,(80,16),(94,18)),
  (41,1,(94,18),(88,24)), (41,2,(88,24),(82,18)), (41,2,(82,18),(80,16)), (42,0,(66,18),(82,18)),
  (42,1,(82,18),(88,24)), (42,2,(88,24),(66,18)), (43,0,(94,18),(110,18)), (43,1,(110,18),(88,24)),
  (43,2,(88,24),(94,18)), (44,0,(0,0),(22,6)), (44,0,(22,6),(44,12)), (44,0,(44,12),(66,18)),
  (44,0,(66,18),(88,24)), (44,1,(88,24),(110,18)), (44,1,(110,18),(132,12)), (44,1,(132,12),(143,9)),
  (44,1,(143,9),(154,6)), (44,1,(154,6),(176,0)), (44,2,(176,0),(160,0)), (44,2,(160,0),(128,0)),
  (44,2,(128,0),(96,0)), (44,2,(96,0),(64,0)), (44,2,(64,0),(48,0)), (44,2,(48,0),(32,0)),
  (44,2,(32,0),(16,0)), (44,2,(16,0),(0,0))]

def alphaT : List Nat := [
  161, 8, 145, 160, 14, 6, 5, 72, 1, 159, 20, 12, 11, 75, 4, 158, 28, 18, 17, 81,
  10, 157, 34, 48, 25, 24, 54, 82, 16, 156, 40, 32, 31, 55, 22, 155, 47, 38, 37, 59,
  30, 154, 153, 44, 43, 93, 60, 36, 23, 58, 71, 52, 51, 99, 26, 33, 65, 66, 49, 39,
  46, 62, 61, 92, 88, 56, 57, 91, 69, 68, 110, 50, 7, 80, 146, 13, 87, 78, 77, 116,
  73, 19, 27, 102, 85, 84, 119, 76, 64, 98, 109, 67, 63, 45, 152, 96, 95, 103, 89, 53,
  115, 120, 83, 97, 151, 106, 105, 129, 126, 90, 70, 128, 113, 112, 135, 100, 79, 125, 147, 86,
  101, 138, 123, 122, 139, 117, 108, 134, 111, 107, 150, 132, 131, 142, 127, 114, 144, 140, 121, 124,
  137, 148, 133, 149, 136, 2, 74, 118, 141, 143, 130, 104, 94, 42, 41, 35, 29, 21, 15, 9,
  3, 0]

def sigmaT : List Nat := [
  1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9, 13, 14, 12, 16, 17, 15, 19, 20,
  18, 22, 23, 24, 21, 26, 27, 28, 25, 30, 31, 29, 33, 34, 32, 36, 37, 35, 39, 40,
  38, 42, 43, 41, 45, 46, 47, 44, 49, 50, 51, 48, 53, 54, 52, 56, 57, 58, 55, 60,
  61, 59, 63, 64, 65, 62, 67, 68, 66, 70, 71, 69, 73, 74, 72, 76, 77, 75, 79, 80,
  78, 82, 83, 84, 81, 86, 87, 85, 89, 90, 91, 88, 93, 94, 95, 92, 97, 98, 96, 100,
  101, 102, 99, 104, 105, 103, 107, 108, 109, 106, 111, 112, 110, 114, 115, 113, 117, 118, 116, 120,
  121, 122, 119, 124, 125, 123, 127, 128, 126, 130, 131, 129, 133, 134, 132, 136, 137, 138, 135, 140,
  141, 139, 143, 144, 142, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
  161, 145]

def faceCyc : List (List Nat) := [
  [0, 1, 2], [3, 4, 5], [6, 7, 8],
  [9, 10, 11], [12, 13, 14], [15, 16, 17],
  [18, 19, 20], [21, 22, 23, 24], [25, 26, 27, 28],
  [29, 30, 31], [32, 33, 34], [35, 36, 37],
  [38, 39, 40], [41, 42, 43], [44, 45, 46, 47],
  [48, 49, 50, 51], [52, 53, 54], [55, 56, 57, 58],
  [59, 60, 61], [62, 63, 64, 65], [66, 67, 68],
  [69, 70, 71], [72, 73, 74], [75, 76, 77],
  [78, 79, 80], [81, 82, 83, 84], [85, 86, 87],
  [88, 89, 90, 91], [92, 93, 94, 95], [96, 97, 98],
  [99, 100, 101, 102], [103, 104, 105], [106, 107, 108, 109],
  [110, 111, 112], [113, 114, 115], [116, 117, 118],
  [119, 120, 121, 122], [123, 124, 125], [126, 127, 128],
  [129, 130, 131], [132, 133, 134], [135, 136, 137, 138],
  [139, 140, 141], [142, 143, 144], [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]]

def nodeCyc : List (List Nat) := [
  [0, 145], [1, 6, 3, 161], [2, 146, 72, 8],
  [4, 12, 9, 160], [5, 7, 73, 78, 75, 14], [10, 18, 15, 159],
  [11, 13, 76, 85, 81, 20], [16, 25, 21, 158], [17, 19, 82, 28],
  [22, 32, 29, 157], [23, 49, 55, 34], [24, 26, 52, 48],
  [27, 83, 99, 54], [30, 38, 35, 156], [31, 33, 56, 62, 59, 40],
  [36, 44, 41, 155], [37, 39, 60, 47], [42, 154],
  [43, 45, 94, 153], [46, 61, 63, 93], [50, 69, 66, 58],
  [51, 53, 100, 113, 110, 71], [57, 67, 88, 65], [64, 89, 96, 92],
  [68, 70, 111, 126, 109, 91], [74, 147, 116, 80], [77, 79, 117, 123, 119, 87],
  [84, 86, 120, 102], [90, 106, 103, 98], [95, 97, 104, 152],
  [101, 121, 135, 115], [105, 107, 130, 151], [108, 127, 132, 129],
  [112, 114, 136, 142, 134, 128], [118, 148, 139, 125], [122, 124, 140, 138],
  [131, 133, 143, 150], [137, 141, 149, 144]]

def faceTri : List (Pt2 × Pt2 × Pt2) := [
  ((0,0),(16,0),(22,6)), ((16,0),(32,0),(38,6)), ((16,0),(38,6),(22,6)),
  ((32,0),(48,0),(54,6)), ((32,0),(54,6),(38,6)), ((48,0),(64,0),(70,6)),
  ((48,0),(70,6),(54,6)), ((64,0),(96,0),(85,3)), ((64,0),(78,2),(72,8)),
  ((96,0),(128,0),(117,3)), ((96,0),(117,3),(85,3)), ((128,0),(160,0),(149,3)),
  ((128,0),(149,3),(117,3)), ((160,0),(176,0),(154,6)), ((160,0),(154,6),(138,6)),
  ((78,2),(92,4),(86,10)), ((78,2),(86,10),(72,8)), ((85,3),(117,3),(106,6)),
  ((117,3),(149,3),(138,6)), ((117,3),(138,6),(106,6)), ((92,4),(106,6),(100,12)),
  ((92,4),(100,12),(86,10)), ((22,6),(38,6),(44,12)), ((38,6),(54,6),(60,12)),
  ((38,6),(60,12),(44,12)), ((54,6),(70,6),(76,12)), ((54,6),(76,12),(60,12)),
  ((106,6),(122,6),(100,12)), ((122,6),(154,6),(143,9)), ((122,6),(143,9),(111,9)),
  ((72,8),(86,10),(80,16)), ((111,9),(143,9),(132,12)), ((111,9),(132,12),(100,12)),
  ((86,10),(100,12),(94,18)), ((86,10),(94,18),(80,16)), ((44,12),(60,12),(66,18)),
  ((60,12),(76,12),(82,18)), ((60,12),(82,18),(66,18)), ((100,12),(116,12),(94,18)),
  ((116,12),(132,12),(110,18)), ((116,12),(110,18),(94,18)), ((80,16),(94,18),(88,24)),
  ((66,18),(82,18),(88,24)), ((94,18),(110,18),(88,24)), ((0,0),(88,24),(176,0))]

def bfsOrder : List Nat := [
  0, 1, 2, 161, 8, 145, 160, 6, 7, 146, 3, 159, 5, 72, 74, 147, 4, 9, 158, 73,
  118, 148, 14, 10, 11, 15, 157, 80, 116, 117, 141, 149, 12, 13, 20, 16, 17, 21, 156, 78,
  79, 125, 139, 140, 143, 150, 75, 18, 19, 28, 22, 24, 29, 155, 77, 123, 124, 137, 142, 144,
  130, 151, 76, 81, 25, 27, 23, 34, 30, 31, 35, 154, 122, 136, 138, 133, 129, 131, 104, 152,
  87, 82, 84, 26, 48, 32, 33, 40, 36, 37, 41, 153, 119, 121, 135, 132, 134, 107, 103, 105,
  94, 85, 86, 83, 54, 49, 51, 55, 38, 39, 47, 42, 43, 120, 114, 127, 106, 108, 97, 93,
  95, 102, 52, 53, 50, 58, 56, 59, 44, 46, 101, 113, 115, 126, 128, 109, 96, 98, 45, 92,
  99, 71, 57, 65, 60, 61, 100, 112, 111, 90, 89, 63, 69, 70, 66, 62, 64, 110, 91, 88,
  68, 67]

/-! ## Accessors -/

def nD : Nat := 162

def dget (n : Nat) : Dart := darts.getD n (0, 0, (0, 0), (0, 0))
def dface (n : Nat) : Nat := (dget n).1
def dedge (n : Nat) : Nat := (dget n).2.1
def dsrc (n : Nat) : Pt2 := (dget n).2.2.1
def dtgt (n : Nat) : Pt2 := (dget n).2.2.2

/-- The edge involution `α`. -/
def ag (n : Nat) : Nat := alphaT.getD n 0
/-- The face permutation `σ`. -/
def sg (n : Nat) : Nat := sigmaT.getD n 0
/-- The node permutation `σ ∘ α`. -/
def na (n : Nat) : Nat := sg (ag n)

def triPt (T : Pt2 × Pt2 × Pt2) (k : Nat) : Pt2 :=
  if k == 0 then T.1 else if k == 1 then T.2.1 else T.2.2

def fTri (f : Nat) : Pt2 × Pt2 × Pt2 := faceTri.getD f ((0,0),(0,0),(0,0))

/-! ## The checks -/

/-- All `132` tile vertices, in the chart. -/
def tileVerts : List Pt2 :=
  Tiling44.tiles.foldl
    (fun acc t => chart (Tiling44.t1 t) :: chart (Tiling44.t2 t) :: chart (Tiling44.t3 t) :: acc) []

def nodupB (l : List Pt2) : Bool := l.all fun p => (l.filter (fun q => q == p)).length == 1

/-- (V) `verts` is exactly the set of tiling vertices, without repetition. -/
def vertsOK : Bool :=
  (verts.length == 38) && nodupB verts
    && verts.all (fun v => tileVerts.contains v)
    && tileVerts.all (fun v => verts.contains v)

/-- (D) Every dart is a *maximal* refined segment of its face's `k`-th edge: both endpoints on the
closed edge, oriented with it, distinct, and with no tiling vertex strictly inside. -/
def dartsOK : Bool :=
  (darts.length == nD) &&
  (List.range nD).all fun n =>
    let T := fTri (dface n)
    let a := triPt T (dedge n)
    let b := triPt T ((dedge n + 1) % 3)
    (dedge n < 3) && (dsrc n != dtgt n)
      && onClosed (dsrc n) a b && onClosed (dtgt n) a b
      && (0 < dt (sub2 (dtgt n) (dsrc n)) (sub2 b a))
      && verts.all (fun v => ! strictBetween v (dsrc n) (dtgt n))

/-- The directed refined segments are pairwise distinct. -/
def dsegs : List (Pt2 × Pt2) := darts.map fun d => d.2.2

def segsDistinct : Bool := dsegs.all fun s => (dsegs.filter (fun t => t == s)).length == 1

/-- (α) The edge involution: fixed-point free, segment-reversing, and **face-changing**. -/
def alphaOK : Bool :=
  (alphaT.length == nD) &&
  (List.range nD).all fun n =>
    (ag n < nD) && (ag (ag n) == n) && (ag n != n)
      && (dsrc (ag n) == dtgt n) && (dtgt (ag n) == dsrc n)
      && (dface (ag n) != dface n)

/-- (σ) The face permutation follows the face's boundary head-to-tail. -/
def sigmaOK : Bool :=
  (sigmaT.length == nD) &&
  (List.range nD).all fun n =>
    (sg n < nD) && (dface (sg n) == dface n) && (dsrc (sg n) == dtgt n)

/-- A list of cycles is exactly the orbit decomposition of `p` on `{0,…,nD-1}`. -/
def cyclesOK (cyc : List (List Nat)) (p : Nat → Nat) : Bool :=
  cyc.all (fun c => c.length != 0)
    && ((List.range nD).all fun n =>
          (cyc.foldl (fun acc c => acc + (c.filter (fun m => m == n)).length) 0) == 1)
    && (cyc.foldl (fun acc c => acc + c.length) 0 == nD)
    && cyc.all fun c =>
        (List.range c.length).all fun m =>
          p (c.getD m 0) == c.getD ((m + 1) % c.length) 0

/-- Each node orbit has a single source point — the combinatorial node *is* a tiling vertex. -/
def nodesArePoints : Bool :=
  nodeCyc.all fun c => c.all fun m => dsrc m == dsrc (c.getD 0 0)

/-- The map is connected: `bfsOrder` enumerates the darts so that each is `σ`- or `α`-adjacent to
an earlier one. -/
def connectedOK : Bool :=
  (bfsOrder.length == nD)
    && ((List.range nD).all fun n => (bfsOrder.filter (fun m => m == n)).length == 1)
    && (bfsOrder.getD 0 1 == 0)
    && (List.range nD).all fun i =>
        (i == 0) ||
          (let x := bfsOrder.getD i 0
           let pre := bfsOrder.take i
           pre.contains (ag x) || pre.contains (sg x)
             || pre.any (fun y => (ag y == x) || (sg y == x)))

/-! ### The kernel checks, one `decide` each -/

theorem vertsOK_true : vertsOK = true := by decide
theorem dartsOK_true : dartsOK = true := by decide
theorem segsDistinct_true : segsDistinct = true := by decide
theorem alphaOK_true : alphaOK = true := by decide
theorem sigmaOK_true : sigmaOK = true := by decide
theorem faceCyc_true : cyclesOK faceCyc sg = true := by decide
theorem nodeCyc_true : cyclesOK nodeCyc na = true := by decide
theorem nodesArePoints_true : nodesArePoints = true := by decide
theorem connectedOK_true : connectedOK = true := by decide

/-- **The refined arrangement of the certified 44-tiling is a hypermap.** Kernel-checked in exact
integer arithmetic; no axioms beyond Lean's own. -/
def checkAll : Bool :=
  tilesChartOK && vertsOK && dartsOK && segsDistinct && alphaOK && sigmaOK
    && cyclesOK faceCyc sg && cyclesOK nodeCyc na && nodesArePoints && connectedOK
    && (faceCyc.length == 45) && (nodeCyc.length == 38)
    && (nodeCyc.length + faceCyc.length == nD / 2 + 2)

theorem hypermap44 : checkAll = true := by
  simp only [checkAll, chart_faithful, vertsOK_true, dartsOK_true, segsDistinct_true,
    alphaOK_true, sigmaOK_true, faceCyc_true, nodeCyc_true, nodesArePoints_true,
    connectedOK_true, Bool.and_self, Bool.true_and]
  decide

/-! ## Consequences, as propositions -/

/-- **Exactly two faces meet along every refined segment.**  `α` is a fixed-point-free involution
which reverses the segment and **changes the face** — so the two sides of a refined segment belong
to two distinct faces, and the assignment is symmetric.  This is
`Dissection.two_tiles_at_edge_point` made a *total* combinatorial function carrying **no** point-set
hypotheses: the corpus's `TileAdjacency.otherTile` needs three (`hxv`, a radius `R`, and a witness
ball `Metric.ball x R ⊆ target.carrier`). -/
theorem otherFace_total : ∀ n ∈ List.range nD,
    ag n < nD ∧ ag (ag n) = n ∧ ag n ≠ n ∧ dface (ag n) ≠ dface n
      ∧ dsrc (ag n) = dtgt n ∧ dtgt (ag n) = dsrc n := by decide

theorem otherFace_total' (n : Nat) (hn : n < nD) :
    ag n < nD ∧ ag (ag n) = n ∧ ag n ≠ n ∧ dface (ag n) ≠ dface n
      ∧ dsrc (ag n) = dtgt n ∧ dtgt (ag n) = dsrc n :=
  otherFace_total n (List.mem_range.mpr hn)

/-- **The face walk is closed and head-to-tail**: `σ` stays inside the face and moves the source to
the previous dart's target. -/
theorem sigma_head_to_tail : ∀ n ∈ List.range nD,
    sg n < nD ∧ dface (sg n) = dface n ∧ dsrc (sg n) = dtgt n := by decide

/-- **Maximality of the refinement**: no tiling vertex lies strictly inside a dart's segment.  This
is the property that makes the two faces of `otherFace_total` *constant along the segment*, and it
is exactly what a non-edge-to-edge dissection destroys for unrefined tile edges. -/
theorem dart_has_no_interior_vertex : ∀ n ∈ List.range nD, ∀ v ∈ verts,
    strictBetween v (dsrc n) (dtgt n) = false := by decide

/-- **The refinement is genuinely finer than the tiling**: `13` tiling vertices lie strictly inside
some tile's edge, so the naive "darts = tile edges" hypermap does not exist. -/
def tJunctionCount : Nat :=
  Tiling44.tiles.foldl (fun acc t =>
    acc + (List.range 3).foldl (fun a k =>
      let p := chart (if k == 0 then Tiling44.t1 t else
                      if k == 1 then Tiling44.t2 t else Tiling44.t3 t)
      let q := chart (if k == 0 then Tiling44.t2 t else
                      if k == 1 then Tiling44.t3 t else Tiling44.t1 t)
      a + (verts.filter (fun v => strictBetween v p q)).length) 0) 0

theorem tJunctions_13 : tJunctionCount = 13 := by decide

/-- **Euler's relation for the refinement.**  `V − E + F = 38 − 81 + 45 = 2`: `V` is the number of
`σ∘α` orbits (each a single tiling vertex, `nodesArePoints`), `E = nD/2` because `α` is a
fixed-point-free involution, and `F` counts the `44` tiles together with the outer face.  The map is
connected (`connectedOK`), so this is the sphere relation. -/
theorem euler_44 : nodeCyc.length = 38 ∧ faceCyc.length = 45 ∧ nD / 2 = 81
    ∧ nodeCyc.length + faceCyc.length = nD / 2 + 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Non-vacuity.**  Every hypothesis above is satisfied by concrete data: `nD > 0`, dart `0`
belongs to tile `0`, its `α`-partner belongs to a different face, and there are strictly more darts
than `3` per face — i.e. some face walk is longer than a triangle, which is precisely the T-junction
refinement at work.  (The corpus has shipped two vacuous theorems; this is the required witness.) -/
theorem witnesses : 0 < nD ∧ dface 0 = 0 ∧ dface (ag 0) ≠ dface 0 ∧ darts.length = 162
    ∧ 3 * faceCyc.length < darts.length := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end Erdos634.TPGonthier

-- Axiom audit (Rule: every theorem here must be kernel-only).
#print axioms Erdos634.TPGonthier.chart_faithful
#print axioms Erdos634.TPGonthier.hypermap44
#print axioms Erdos634.TPGonthier.otherFace_total
#print axioms Erdos634.TPGonthier.sigma_head_to_tail
#print axioms Erdos634.TPGonthier.dart_has_no_interior_vertex
#print axioms Erdos634.TPGonthier.tJunctions_13
#print axioms Erdos634.TPGonthier.euler_44
#print axioms Erdos634.TPGonthier.witnesses
