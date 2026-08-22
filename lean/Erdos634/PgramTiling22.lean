-- PgramTiling22.lean — zero-axiom kernel verification of the UNIT-PARALLELOGRAM certificate
-- (Erdos #634, collar lemma). The tile (2,3,4) tiles the parallelogram with vertices
-- (0,0), (11,0), (33/2,(3/2)sqrt15), (11/2,(3/2)sqrt15) into 22 congruent copies.
-- Scaled by 4 into Z[sqrt15]. Kernel checks: (C1) each tile has squared side multiset
-- {64,144,256} = (4*(2,3,4))^2; (C2) CCW + vertices in the closed QUAD (4 half-planes);
-- (C3) an explicit separating edge-line per pair (231 pairs) => disjoint interiors;
-- (C4) signed 2-areas sum to 528*sqrt15 = twice the parallelogram area. No imports, no axioms.
namespace PgramTiling22
abbrev Z15 := Int × Int
abbrev Pt := Int × Int × Int × Int
def zmul (u v : Z15) : Z15 := (u.1*v.1 + 15*u.2*v.2, u.1*v.2 + u.2*v.1)
def zsub (u v : Z15) : Z15 := (u.1 - v.1, u.2 - v.2)
def zadd (u v : Z15) : Z15 := (u.1 + v.1, u.2 + v.2)
def znonneg (z : Z15) : Bool :=
  if 0 <= z.1 then (if 0 <= z.2 then true else 15*z.2*z.2 <= z.1*z.1)
  else (if z.2 < 0 then false else z.1*z.1 <= 15*z.2*z.2)
def znonpos (z : Z15) : Bool := znonneg (-z.1, -z.2)
def zpos (z : Z15) : Bool := !(znonpos z)
def px (p : Pt) : Z15 := (p.1, p.2.1)
def py (p : Pt) : Z15 := (p.2.2.1, p.2.2.2)
def cross (o a b : Pt) : Z15 :=
  zsub (zmul (zsub (px a) (px o)) (zsub (py b) (py o))) (zmul (zsub (py a) (py o)) (zsub (px b) (px o)))
def dist2 (p q : Pt) : Z15 :=
  zadd (zmul (zsub (px q) (px p)) (zsub (px q) (px p))) (zmul (zsub (py q) (py p)) (zsub (py q) (py p)))
abbrev Tri := Pt × Pt × Pt
def t1 (t : Tri) : Pt := t.1
def t2 (t : Tri) : Pt := t.2.1
def t3 (t : Tri) : Pt := t.2.2
def congOK (t : Tri) : Bool :=
  let d1 := dist2 (t1 t) (t2 t); let d2 := dist2 (t2 t) (t3 t); let d3 := dist2 (t3 t) (t1 t)
  let s : List Z15 := [d1, d2, d3]
  s.contains ((64:Int),(0:Int)) && s.contains ((144:Int),(0:Int)) && s.contains ((256:Int),(0:Int))
  && d1.2 == 0 && d2.2 == 0 && d3.2 == 0 && (d1.1 + d2.1 + d3.1 == 464)
def q1 : Pt := (0,0,0,0)
def q2 : Pt := (44,0,0,0)
def q3 : Pt := (66,0,0,6)
def q4 : Pt := (22,0,0,6)
def insideOK (t : Tri) : Bool :=
  zpos (cross (t1 t) (t2 t) (t3 t)) &&
  [t1 t, t2 t, t3 t].all (fun v =>
    znonneg (cross q1 q2 v) && znonneg (cross q2 q3 v) &&
    znonneg (cross q3 q4 v) && znonneg (cross q4 q1 v))
def sepBy (P Q : Pt) (A B : Tri) : Bool :=
  let sA := [t1 A, t2 A, t3 A].map (fun v => cross P Q v)
  let sB := [t1 B, t2 B, t3 B].map (fun v => cross P Q v)
  (sA.all znonneg && sB.all znonpos) || (sA.all znonpos && sB.all znonneg)
def edgeOf (t : Tri) (e : Nat) : Pt × Pt :=
  if e == 0 then (t1 t, t2 t) else if e == 1 then (t2 t, t3 t) else (t3 t, t1 t)
def area2 (t : Tri) : Z15 := cross (t1 t) (t2 t) (t3 t)
-- twice the parallelogram area, scaled: 2 * 16 * (33/2)sqrt15 = 528*sqrt15
def area2target : Z15 := ((0:Int), (528:Int))
def tiles : List Tri := [
  ((0,0,0,0), (8,0,0,0), (11,0,0,3)),
  ((8,0,0,0), (16,0,0,0), (19,0,0,3)),
  ((8,0,0,0), (19,0,0,3), (11,0,0,3)),
  ((16,0,0,0), (28,0,0,0), (30,0,0,2)),
  ((16,0,0,0), (23,0,0,1), (20,0,0,4)),
  ((28,0,0,0), (36,0,0,0), (39,0,0,3)),
  ((28,0,0,0), (39,0,0,3), (31,0,0,3)),
  ((36,0,0,0), (44,0,0,0), (47,0,0,3)),
  ((36,0,0,0), (47,0,0,3), (39,0,0,3)),
  ((44,0,0,0), (55,0,0,3), (47,0,0,3)),
  ((23,0,0,1), (30,0,0,2), (27,0,0,5)),
  ((23,0,0,1), (27,0,0,5), (20,0,0,4)),
  ((30,0,0,2), (34,0,0,6), (27,0,0,5)),
  ((11,0,0,3), (19,0,0,3), (22,0,0,6)),
  ((31,0,0,3), (39,0,0,3), (42,0,0,6)),
  ((31,0,0,3), (42,0,0,6), (34,0,0,6)),
  ((39,0,0,3), (47,0,0,3), (50,0,0,6)),
  ((39,0,0,3), (50,0,0,6), (42,0,0,6)),
  ((47,0,0,3), (55,0,0,3), (58,0,0,6)),
  ((47,0,0,3), (58,0,0,6), (50,0,0,6)),
  ((55,0,0,3), (66,0,0,6), (58,0,0,6)),
  ((20,0,0,4), (34,0,0,6), (22,0,0,6))
]
def wit : List (Bool × Nat) := [
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (false,2), (true,0), (true,0), (true,0), (true,0), (true,0),
  (true,0), (false,2), (true,0), (true,1), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,1),
  (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,0), (true,1), (true,0), (true,0), (true,0), (true,1),
  (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,0), (true,1), (true,0), (true,1), (true,2),
  (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,2), (true,0), (true,0), (true,0), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1),
  (true,0), (true,1), (true,0), (true,0), (true,0), (true,1), (true,2), (true,1), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1), (true,2), (true,0), (true,2), (true,2), (true,2),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,1), (true,0), (true,1), (true,2), (true,2), (true,2),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,2),
  (true,1), (true,1), (true,1), (true,1), (true,0), (true,1), (true,0), (false,0), (true,0), (false,1), (true,0), (true,0),
  (true,0), (true,0), (true,0), (true,0), (true,0), (true,1), (true,2), (true,0), (true,0), (true,0), (true,0), (true,0),
  (true,0), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,0), (true,0), (true,0), (true,0), (true,0), (true,2),
  (true,2), (true,1), (true,1), (true,1), (true,2), (true,0), (true,0), (true,0), (true,2), (true,2), (true,1), (true,2),
  (true,0), (true,2), (true,2)
]
def pairSep (A B : Tri) (w : Bool × Nat) : Bool :=
  let pq := edgeOf (if w.1 then A else B) w.2
  sepBy pq.1 pq.2 A B
def checkPairs : List Tri → List (Bool × Nat) → Bool
  | [], ws => ws.isEmpty
  | t :: rest, ws =>
      let n := rest.length
      (ws.take n).length == n
      && (List.zip rest (ws.take n)).all (fun (u, w) => pairSep t u w)
      && checkPairs rest (ws.drop n)
def zsum (l : List Z15) : Z15 := l.foldl zadd ((0:Int),(0:Int))
def checkAll : Bool :=
  tiles.length == 22 && tiles.all congOK && tiles.all insideOK
  && checkPairs tiles wit && zsum (tiles.map area2) == area2target
set_option maxRecDepth 8192 in
theorem pgram22_certificate : checkAll = true := by decide
end PgramTiling22
