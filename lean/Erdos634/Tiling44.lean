-- Tiling44.lean — machine verification of the 44-tiling certificate (Erdos #634).
-- THEOREM (paper): the isosceles triangle (16,16,22) is tiled by 44 congruent (2,3,4) triangles.
-- This file kernel-checks the certificate, scaled by 8 into Z[sqrt 15] (integer pairs a+b*sqrt15):
--   (C1) each of the 44 triangles has squared side multiset {256, 576, 1024} = (8*(2,3,4))^2;
--   (C2) each triangle is positively oriented and its vertices lie in the closed target
--        triangle (0,0), (176,0), (88, 24*sqrt15)  [containment: 3 half-plane checks/vertex];
--   (C3) every pair of the 44 triangles admits a separating edge-line (closed half-planes),
--        certified by an explicit witness edge per pair -> pairwise disjoint interiors;
--   (C4) the signed 2-areas sum exactly to the target's (4224*sqrt15).
-- (C1)-(C4) imply the union of the 44 closed triangles IS the target (finite measure argument:
-- disjoint interiors + containment + exact total area force the complement to be empty).
-- No imports, no axioms beyond the Lean kernel: the final theorems are proved by `decide`.

namespace Tiling44

/-- a + b*sqrt(15), as an integer pair -/
abbrev Z15 := Int × Int
/-- a point of the plane over Z[sqrt15] -/
abbrev Pt := Int × Int × Int × Int   -- (xa, xb, ya, yb)

def zmul (u v : Z15) : Z15 := (u.1*v.1 + 15*u.2*v.2, u.1*v.2 + u.2*v.1)
def zsub (u v : Z15) : Z15 := (u.1 - v.1, u.2 - v.2)
def zadd (u v : Z15) : Z15 := (u.1 + v.1, u.2 + v.2)

/-- exact: is a + b*sqrt15 >= 0 ? -/
def znonneg (z : Z15) : Bool :=
  if 0 <= z.1 then
    if 0 <= z.2 then true else 15*z.2*z.2 <= z.1*z.1
  else
    if z.2 < 0 then false else z.1*z.1 <= 15*z.2*z.2
def znonpos (z : Z15) : Bool := znonneg (-z.1, -z.2)
def zpos (z : Z15) : Bool := !(znonpos z)

def px (p : Pt) : Z15 := (p.1, p.2.1)
def py (p : Pt) : Z15 := (p.2.2.1, p.2.2.2)

/-- z-component of (a-o) x (b-o) -/
def cross (o a b : Pt) : Z15 :=
  zsub (zmul (zsub (px a) (px o)) (zsub (py b) (py o)))
       (zmul (zsub (py a) (py o)) (zsub (px b) (px o)))

/-- squared distance, an element of Z[sqrt15] -/
def dist2 (p q : Pt) : Z15 :=
  zadd (zmul (zsub (px q) (px p)) (zsub (px q) (px p)))
       (zmul (zsub (py q) (py p)) (zsub (py q) (py p)))

abbrev Tri := Pt × Pt × Pt
def t1 (t : Tri) : Pt := t.1
def t2 (t : Tri) : Pt := t.2.1
def t3 (t : Tri) : Pt := t.2.2

/-- (C1): squared sides are {256,576,1024} in some order -/
def congOK (t : Tri) : Bool :=
  let d1 := dist2 (t1 t) (t2 t); let d2 := dist2 (t2 t) (t3 t); let d3 := dist2 (t3 t) (t1 t)
  let s : List Z15 := [d1, d2, d3]
  (s.contains ((256:Int),(0:Int)) && s.contains ((576:Int),(0:Int)) && s.contains ((1024:Int),(0:Int)))
  && d1.2 == 0 && d2.2 == 0 && d3.2 == 0
  && (d1.1 + d2.1 + d3.1 == 256 + 576 + 1024)

def target : Tri := ((0,0,0,0), (176,0,0,0), (88,0,0,24))

/-- (C2): CCW and inside the closed target -/
def insideOK (t : Tri) : Bool :=
  zpos (cross (t1 t) (t2 t) (t3 t)) &&
  [t1 t, t2 t, t3 t].all (fun v =>
    znonneg (cross (t1 target) (t2 target) v) &&
    znonneg (cross (t2 target) (t3 target) v) &&
    znonneg (cross (t3 target) (t1 target) v))

/-- (C3): the edge (P,Q) separates triangles A and B (closed sides) -/
def sepBy (P Q : Pt) (A B : Tri) : Bool :=
  let sA := [t1 A, t2 A, t3 A].map (fun v => cross P Q v)
  let sB := [t1 B, t2 B, t3 B].map (fun v => cross P Q v)
  (sA.all znonneg && sB.all znonpos) || (sA.all znonpos && sB.all znonneg)

def edgeOf (t : Tri) (e : Nat) : Pt × Pt :=
  if e == 0 then (t1 t, t2 t) else if e == 1 then (t2 t, t3 t) else (t3 t, t1 t)

/-- 2*area (signed) -/
def area2 (t : Tri) : Z15 := cross (t1 t) (t2 t) (t3 t)

def tiles : List Tri := [
  ((0,0,0,0), (16,0,0,0), (22,0,0,6)),
  ((16,0,0,0), (32,0,0,0), (38,0,0,6)),
  ((16,0,0,0), (38,0,0,6), (22,0,0,6)),
  ((32,0,0,0), (48,0,0,0), (54,0,0,6)),
  ((32,0,0,0), (54,0,0,6), (38,0,0,6)),
  ((48,0,0,0), (64,0,0,0), (70,0,0,6)),
  ((48,0,0,0), (70,0,0,6), (54,0,0,6)),
  ((64,0,0,0), (96,0,0,0), (85,0,0,3)),
  ((64,0,0,0), (78,0,0,2), (72,0,0,8)),
  ((96,0,0,0), (128,0,0,0), (117,0,0,3)),
  ((96,0,0,0), (117,0,0,3), (85,0,0,3)),
  ((128,0,0,0), (160,0,0,0), (149,0,0,3)),
  ((128,0,0,0), (149,0,0,3), (117,0,0,3)),
  ((160,0,0,0), (176,0,0,0), (154,0,0,6)),
  ((160,0,0,0), (154,0,0,6), (138,0,0,6)),
  ((78,0,0,2), (92,0,0,4), (86,0,0,10)),
  ((78,0,0,2), (86,0,0,10), (72,0,0,8)),
  ((85,0,0,3), (117,0,0,3), (106,0,0,6)),
  ((117,0,0,3), (149,0,0,3), (138,0,0,6)),
  ((117,0,0,3), (138,0,0,6), (106,0,0,6)),
  ((92,0,0,4), (106,0,0,6), (100,0,0,12)),
  ((92,0,0,4), (100,0,0,12), (86,0,0,10)),
  ((22,0,0,6), (38,0,0,6), (44,0,0,12)),
  ((38,0,0,6), (54,0,0,6), (60,0,0,12)),
  ((38,0,0,6), (60,0,0,12), (44,0,0,12)),
  ((54,0,0,6), (70,0,0,6), (76,0,0,12)),
  ((54,0,0,6), (76,0,0,12), (60,0,0,12)),
  ((106,0,0,6), (122,0,0,6), (100,0,0,12)),
  ((122,0,0,6), (154,0,0,6), (143,0,0,9)),
  ((122,0,0,6), (143,0,0,9), (111,0,0,9)),
  ((72,0,0,8), (86,0,0,10), (80,0,0,16)),
  ((111,0,0,9), (143,0,0,9), (132,0,0,12)),
  ((111,0,0,9), (132,0,0,12), (100,0,0,12)),
  ((86,0,0,10), (100,0,0,12), (94,0,0,18)),
  ((86,0,0,10), (94,0,0,18), (80,0,0,16)),
  ((44,0,0,12), (60,0,0,12), (66,0,0,18)),
  ((60,0,0,12), (76,0,0,12), (82,0,0,18)),
  ((60,0,0,12), (82,0,0,18), (66,0,0,18)),
  ((100,0,0,12), (116,0,0,12), (94,0,0,18)),
  ((116,0,0,12), (132,0,0,12), (110,0,0,18)),
  ((116,0,0,12), (110,0,0,18), (94,0,0,18)),
  ((80,0,0,16), (94,0,0,18), (88,0,0,24)),
  ((66,0,0,18), (82,0,0,18), (88,0,0,24)),
  ((94,0,0,18), (110,0,0,18), (88,0,0,24))
]
/-- separating-line witnesses for every pair i<j, canonical order -/
def wit : List (Bool × Nat) := [
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,0), (true,0),
  (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0),
  (true,0), (true,0), (true,0), (true,0), (true,1), (true,0), (true,1), (true,0), (true,0), (true,0),
  (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,1), (true,0), (true,1),
  (true,0), (true,0), (true,0), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,0),
  (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0),
  (true,0), (true,0), (true,0), (true,1), (true,1), (true,1), (true,0), (true,1), (true,0), (true,0),
  (true,0), (true,1), (true,0), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,0), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1),
  (true,1), (true,2), (true,1), (true,0), (false,2), (true,0), (true,0), (true,0), (true,0), (true,0),
  (true,0), (true,0), (false,2), (true,0), (true,0), (true,0), (true,0), (true,0), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,1), (true,0), (true,0), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,0),
  (true,0), (true,0), (true,1), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,1), (true,0), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,1),
  (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1),
  (true,1), (true,2), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,0), (false,0),
  (false,0), (true,1), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1),
  (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,2), (true,2), (true,1),
  (false,2), (false,2), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,2), (true,0), (true,0), (true,0), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,1), (true,0), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,2),
  (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,0), (true,0),
  (true,0), (true,0), (true,0), (true,1), (true,1), (true,1), (false,1), (true,1), (true,0), (true,0),
  (true,0), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1), (true,1), (true,1), (true,0),
  (true,0), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (false,0), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,1), (true,1), (true,2), (true,2), (true,1), (false,0), (false,0), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,0), (true,1), (true,2),
  (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1),
  (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,0), (true,0),
  (true,0), (true,1), (true,0), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (false,0),
  (true,0), (false,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,0),
  (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,1), (true,0), (true,1), (true,0),
  (true,0), (true,0), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1),
  (true,1), (true,2), (true,1), (true,0), (true,0), (true,0), (false,2), (true,0), (true,0), (false,2),
  (false,2), (true,1), (true,1), (true,1), (true,1), (true,0), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,2), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,1), (true,1), (true,1), (true,2), (true,2), (true,1), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,1), (true,1), (true,2),
  (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (false,0), (false,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1), (true,2), (true,2),
  (true,1), (true,2), (false,1), (false,0), (true,0), (true,0), (true,0), (true,1), (true,1), (false,0),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,1), (true,0), (true,0), (true,0), (false,2), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,2), (true,1), (true,2), (true,2), (true,2), (true,2),
  (false,0), (true,1), (true,1), (true,2), (true,1), (true,1)
]

def pairSep (A B : Tri) (w : Bool × Nat) : Bool :=
  let pq := edgeOf (if w.1 then A else B) w.2
  sepBy pq.1 pq.2 A B

/-- walk all pairs i<j consuming witnesses -/
def checkPairs : List Tri → List (Bool × Nat) → Bool
  | [], ws => ws.isEmpty
  | t :: rest, ws =>
      let n := rest.length
      let (wsHead, wsTail) := (ws.take n, ws.drop n)
      wsHead.length == n
      && (List.zip rest wsHead).all (fun (u, w) => pairSep t u w)
      && checkPairs rest wsTail

def zsum (l : List Z15) : Z15 := l.foldl zadd ((0:Int),(0:Int))

def checkAll : Bool :=
  tiles.length == 44
  && tiles.all congOK
  && tiles.all insideOK
  && checkPairs tiles wit
  && zsum (tiles.map area2) == area2 target

set_option maxRecDepth 8192 in
theorem tiling44_certificate : checkAll = true := by decide

end Tiling44


#print axioms Tiling44.tiling44_certificate
