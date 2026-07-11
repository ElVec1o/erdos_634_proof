# Generate a self-contained, zero-axiom Lean certificate for a found D=15 tiling.
import sys
from fractions import Fraction as F
from math import lcm

fn, out, ns = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(fn).read().strip().split('\n')
N, D = int(lines[0].split()[1]), int(lines[0].split()[2]); assert D == 15
raw, dens = [], set()
for ln in lines[1:]:
    v = [int(t) for t in ln.split()]; pts=[]
    for k in range(3):
        xp,xq,xd,yp,yq,yd = v[6*k:6*k+6]; dens |= {xd,yd}
        pts.append((F(xp,xd),F(xq,xd),F(yp,yd),F(yq,yd)))
    raw.append(pts)
L = lcm(*dens)
S = [[(int(a*L),int(b*L),int(c*L),int(d*L)) for (a,b,c,d) in tri] for tri in raw]
sys.path.insert(0,'.'); from engine import qd; import run_all
_,tgt,_ = run_all.make_instance(ns.replace('Tiling','T'))
def q2(x): return (int(x.pn*L//x.den), int(x.qn*L//x.den))
T = [ (q2(px)[0],q2(px)[1],q2(py)[0],q2(py)[1]) for (px,py) in tgt ]
def sgn(a,b):
    if a==0 and b==0: return 0
    if a>=0 and b>=0: return 1
    if a<=0 and b<=0: return -1
    t=a*a-15*b*b
    return (1 if t>0 else -1 if t<0 else 0) if a>0 else (-1 if t>0 else 1 if t<0 else 0)
def crossz(o,a,b):
    ux,uy=(a[0]-o[0],a[1]-o[1]),(a[2]-o[2],a[3]-o[3]); vx,vy=(b[0]-o[0],b[1]-o[1]),(b[2]-o[2],b[3]-o[3])
    m1=(ux[0]*vy[0]+15*ux[1]*vy[1], ux[0]*vy[1]+ux[1]*vy[0]); m2=(uy[0]*vx[0]+15*uy[1]*vx[1], uy[0]*vx[1]+uy[1]*vx[0])
    return (m1[0]-m2[0], m1[1]-m2[1])
def d2(p,q):
    dxa,dxb,dya,dyb=q[0]-p[0],q[1]-p[1],q[2]-p[2],q[3]-p[3]
    return (dxa*dxa+15*dxb*dxb+dya*dya+15*dyb*dyb, 2*(dxa*dxb+dya*dyb))
S=[tri if sgn(*crossz(tri[0],tri[1],tri[2]))>0 else [tri[0],tri[2],tri[1]] for tri in S]
sq=sorted([4*L*L,9*L*L,16*L*L]); ssum=sum(sq)
for tri in S: assert sorted(d2(tri[i],tri[(i+1)%3])[0] for i in range(3))==sq and all(d2(tri[i],tri[(i+1)%3])[1]==0 for i in range(3))
for tri in S:
    for X in tri:
        for e in range(3): assert sgn(*crossz(T[e],T[(e+1)%3],X))>=0
pairs=[]
for i in range(N):
    for j in range(i+1,N):
        f=None
        for (src,tri) in (('a',S[i]),('b',S[j])):
            for e in range(3):
                P,Q=tri[e],tri[(e+1)%3]; sa=[sgn(*crossz(P,Q,X)) for X in S[i]]; sb=[sgn(*crossz(P,Q,X)) for X in S[j]]
                if max(sb)<=0<=min(sa) or max(sa)<=0<=min(sb): f=(src,e);break
            if f: break
        assert f; pairs.append(f)
ta=crossz(T[0],T[1],T[2]); tot=(0,0)
for tri in S:
    a=crossz(tri[0],tri[1],tri[2]); tot=(tot[0]+a[0],tot[1]+a[1])
assert tot==ta
tgtstr=", ".join(f"({t[0]},{t[1]},{t[2]},{t[3]})" for t in T)
Ln=[]
Ln.append(f"""-- {ns}.lean — zero-axiom kernel verification of the {N}-tiling certificate (Erdos #634).
-- The tile (2,3,4) tiles the target triangle into {N} congruent copies. Scaled by {L} into Z[sqrt15].
-- Kernel checks: (C1) each tile has squared side multiset {{{sq[0]},{sq[1]},{sq[2]}}} = ({L}*(2,3,4))^2;
-- (C2) CCW + vertices in closed target (half-planes); (C3) an explicit separating edge-line per pair
-- ({len(pairs)} pairs) => disjoint interiors; (C4) signed 2-areas sum to the target's. No imports, no axioms.
namespace {ns}
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
  s.contains (({sq[0]}:Int),(0:Int)) && s.contains (({sq[1]}:Int),(0:Int)) && s.contains (({sq[2]}:Int),(0:Int))
  && d1.2 == 0 && d2.2 == 0 && d3.2 == 0 && (d1.1 + d2.1 + d3.1 == {ssum})
def target : Tri := ({tgtstr})
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
def area2 (t : Tri) : Z15 := cross (t1 t) (t2 t) (t3 t)""")
Ln.append("def tiles : List Tri := [")
for k,tri in enumerate(S):
    Ln.append("  (%s, %s, %s)%s"%(*(f"({p[0]},{p[1]},{p[2]},{p[3]})" for p in tri), ',' if k<N-1 else ''))
Ln.append("]")
Ln.append("def wit : List (Bool × Nat) := [")
row=[f"({'true' if s=='a' else 'false'},{e})" for (s,e) in pairs]
for k in range(0,len(row),12): Ln.append("  "+", ".join(row[k:k+12])+("," if k+12<len(row) else ""))
Ln.append("]")
Ln.append(f"""def pairSep (A B : Tri) (w : Bool × Nat) : Bool :=
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
  tiles.length == {N} && tiles.all congOK && tiles.all insideOK
  && checkPairs tiles wit && zsum (tiles.map area2) == area2 target
set_option maxRecDepth 8192 in
theorem tiling{N}_certificate : checkAll = true := by decide
end {ns}""")
open(out,'w').write("\n".join(Ln))
print(f"{out}: N={N}, L={L}, sq={sq}, {len(pairs)} witnesses -- python checks all pass")
