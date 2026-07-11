-- Tiling28.lean — zero-axiom kernel verification of the 28-tiling certificate (Erdos #634).
-- The tile (2,3,4) tiles the target triangle into 28 congruent copies. Scaled by 16 into Z[sqrt15].
-- Kernel checks: (C1) each tile has squared side multiset {1024,2304,4096} = (16*(2,3,4))^2;
-- (C2) CCW + vertices in closed target (half-planes); (C3) an explicit separating edge-line per pair
-- (378 pairs) => disjoint interiors; (C4) signed 2-areas sum to the target's. No imports, no axioms.
namespace Tiling28
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
  s.contains ((1024:Int),(0:Int)) && s.contains ((2304:Int),(0:Int)) && s.contains ((4096:Int),(0:Int))
  && d1.2 == 0 && d2.2 == 0 && d3.2 == 0 && (d1.1 + d2.1 + d3.1 == 7424)
def target : Tri := ((0,0,0,0), (256,0,0,0), (102,0,0,42))
def insideOK (t : Tri) : Bool :=
  zpos (cross (t1 t) (t2 t) (t3 t)) &&
  [t1 t, t2 t, t3 t].all (fun v =>
    znonneg (cross (t1 target) (t2 target) v) && znonneg (cross (t2 target) (t3 target) v) &&
    znonneg (cross (t3 target) (t1 target) v))
def sepBy (P Q : Pt) (A B : Tri) : Bool :=
  let sA := [t1 A, t2 A, t3 A].map (fun v => cross P Q v)
  let sB := [t1 B, t2 B, t3 B].map (fun v => cross P Q v)
  (sA.all znonneg && sB.all znonpos) || (sA.all znonpos && sB.all znonneg)
def edgeOf (t : Tri) (e : Nat) : Pt × Pt :=
  if e == 0 then (t1 t, t2 t) else if e == 1 then (t2 t, t3 t) else (t3 t, t1 t)
def area2 (t : Tri) : Z15 := cross (t1 t) (t2 t) (t3 t)
def tiles : List Tri := [
  ((0,0,0,0), (64,0,0,0), (42,0,0,6)),
  ((0,0,0,0), (42,0,0,6), (34,0,0,14)),
  ((64,0,0,0), (128,0,0,0), (106,0,0,6)),
  ((64,0,0,0), (106,0,0,6), (42,0,0,6)),
  ((128,0,0,0), (192,0,0,0), (170,0,0,6)),
  ((128,0,0,0), (170,0,0,6), (106,0,0,6)),
  ((192,0,0,0), (256,0,0,0), (234,0,0,6)),
  ((192,0,0,0), (234,0,0,6), (170,0,0,6)),
  ((42,0,0,6), (106,0,0,6), (84,0,0,12)),
  ((42,0,0,6), (84,0,0,12), (76,0,0,20)),
  ((42,0,0,6), (76,0,0,20), (34,0,0,14)),
  ((106,0,0,6), (170,0,0,6), (148,0,0,12)),
  ((106,0,0,6), (148,0,0,12), (84,0,0,12)),
  ((170,0,0,6), (234,0,0,6), (212,0,0,12)),
  ((170,0,0,6), (212,0,0,12), (148,0,0,12)),
  ((84,0,0,12), (148,0,0,12), (126,0,0,18)),
  ((84,0,0,12), (126,0,0,18), (118,0,0,26)),
  ((84,0,0,12), (101,0,0,19), (68,0,0,28)),
  ((148,0,0,12), (212,0,0,12), (190,0,0,18)),
  ((148,0,0,12), (190,0,0,18), (126,0,0,18)),
  ((34,0,0,14), (76,0,0,20), (68,0,0,28)),
  ((126,0,0,18), (158,0,0,18), (114,0,0,30)),
  ((158,0,0,18), (190,0,0,18), (146,0,0,30)),
  ((158,0,0,18), (146,0,0,30), (114,0,0,30)),
  ((101,0,0,19), (118,0,0,26), (85,0,0,35)),
  ((101,0,0,19), (85,0,0,35), (68,0,0,28)),
  ((118,0,0,26), (102,0,0,42), (85,0,0,35)),
  ((114,0,0,30), (146,0,0,30), (102,0,0,42))
]
def wit : List (Bool × Nat) := [
  (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,1), (true,1),
  (true,0), (true,0), (true,0), (true,0), (true,0), (true,1), (true,1), (true,0), (true,0), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2),
  (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,0), (true,1), (true,1),
  (true,1), (true,0), (true,1), (true,0), (true,0), (true,1), (true,1), (true,1), (true,0), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,1), (true,1), (true,2), (true,2), (true,2), (true,1), (true,1), (true,2), (true,1), (true,1),
  (true,1), (true,2), (true,2), (true,1), (true,1), (true,0), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,0), (true,0), (true,0), (true,0), (true,0), (true,1), (true,1), (true,0),
  (true,0), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0),
  (true,0), (true,0), (true,0), (false,2), (true,0), (true,0), (true,1), (true,0), (true,0), (true,0), (false,2), (false,2),
  (true,1), (true,1), (true,2), (true,1), (true,1), (true,2), (true,2), (true,2), (true,1), (true,1), (true,2), (true,1),
  (true,1), (true,1), (true,2), (true,2), (true,1), (true,1), (true,0), (true,0), (true,1), (true,1), (true,1), (true,0),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,2), (true,2), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,2), (true,2), (true,1), (true,1),
  (true,2), (true,0), (true,0), (true,2), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,1), (true,0),
  (true,0), (true,2), (true,1), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2),
  (true,2), (true,2), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (false,0), (true,1),
  (true,2), (true,1), (true,1), (true,0), (true,0), (true,0)
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
  tiles.length == 28 && tiles.all congOK && tiles.all insideOK
  && checkPairs tiles wit && zsum (tiles.map area2) == area2 target
set_option maxRecDepth 8192 in
theorem tiling28_certificate : checkAll = true := by decide
end Tiling28
