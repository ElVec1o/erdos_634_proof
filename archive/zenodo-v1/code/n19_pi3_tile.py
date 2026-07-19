#!/usr/bin/env python3
"""
The remaining checkpoint: a non-isosceles PI/3 (60 degree) tile.  Same elementary area test.

Tile angles (alpha,beta,gamma=pi/3), alpha+beta=2pi/3.  Law of cosines at gamma=pi/3:
   c^2 = a^2 + b^2 - a b,   integer (a,b,c), gcd=1.
   sin alpha = a*sqrt3/(2c),  cos alpha = (2b-a)/(2c);  sin beta=b*sqrt3/(2c), cos beta=(2a-b)/(2c).
Corner angle = P*alpha+Q*beta+R*gamma = (P-Q)alpha + (2Q+R)(pi/3) = m*alpha + k*(pi/3),
   m=P-Q, k=2Q+R.   ABC corners: sum(m)=0, sum(k)=3.
Tile area = (sqrt3/4) a b  (pi/3 between sides a,b).
"""
import math
from itertools import product
from fractions import Fraction
from math import isqrt, gcd
import sympy as sp

def feas(m,k):
    # exists P,Q,R>=0, P+Q+R>=1, P-Q=m, 2Q+R=k
    for Q in range(0, k//2+1):
        R = k-2*Q
        if R<0: continue
        P = Q+m
        if P>=0 and P+Q+R>=1: return True
    return False

al=(2*math.pi/3)*0.41  # generic irrational alpha in (0,2pi/3); use 0.41 fraction
def angle(m,k): return m*al + k*math.pi/3

shapes=set()
for ms in product(range(-6,7),repeat=3):
    if sum(ms)!=0: continue
    for ks in product(range(0,4),repeat=3):
        if sum(ks)!=3: continue
        cor=list(zip(ms,ks))
        if not all(feas(m,k) for m,k in cor): continue
        angs=[angle(m,k) for m,k in cor]
        if any(a<=1e-9 or a>=math.pi-1e-9 for a in angs): continue
        shapes.add(tuple(sorted(cor)))

def cls(cor):
    angs=sorted(round(angle(m,k),6) for m,k in cor)
    if all(abs(a-math.pi/3)<1e-6 for a in angs): return 'EQU'
    if any(abs(angs[i]-angs[j])<1e-6 for i in range(3) for j in range(i+1,3)): return 'ISO'
    return 'SCA'

print("PI/3 tile: structurally-valid ABC shapes (m,k per corner):")
scal=[]
for s in sorted(shapes):
    c=cls(s)
    # (alpha,beta) form: angle m*alpha+k*pi/3 = m*alpha + k*(alpha+beta)/2*... ; beta=2pi/3-alpha
    # m*alpha + k*pi/3 = m*alpha + (k/2)(alpha+beta) => coeff alpha = m+k/2, beta=k/2 (k even) else half-int
    desc=", ".join(f"{m}a+{k}(p/3)" for m,k in s)
    print(f"  [{c}] {s}  angles: {desc}")
    if c=='SCA': scal.append(s)
print(f"\nscalene shapes for pi/3 tile: {len(scal)}")

# For each scalene shape, compute N0 = area(Dp)/area(tile) exactly over primitive 60-triples,
# and test whether N=19 can occur (19 = k^2 * N0).
a_,b_,c_ = sp.symbols('a b c', positive=True)
S3=sp.sqrt(3)
subs_trig = {}
sin_al=a_*S3/(2*c_); cos_al=(2*b_-a_)/(2*c_)
sin_be=b_*S3/(2*c_); cos_be=(2*a_-b_)/(2*c_)
def sincomb(m,k):
    # sin(m*alpha + k*pi/3); expand
    A,B=sp.symbols('A B')
    e=sp.sin(m*A + k*sp.pi/3).expand(trig=True)
    e=e.rewrite(sp.cos).expand(trig=True)
    e=e.subs({sp.sin(A):sin_al, sp.cos(A):cos_al})
    # k*pi/3 is constant; m may be 0; handle residual
    return sp.simplify(e)

def is60(a,b):
    if gcd(a,b)!=1: return None
    s=a*a+b*b-a*b
    c=isqrt(s)
    return c if c*c==s and c>0 else None

def N0(shape,a,b,c):
    D=[sp.nsimplify(sincomb(m,k)) for (m,k) in shape]
    Dv=[sp.simplify(d.subs({a_:a,b_:b,c_:c})*2*c**2/S3) for d in D]
    try:
        Dv=[int(sp.nsimplify(x)) for x in Dv]
    except Exception:
        return None
    if any(x<=0 for x in Dv): return None
    g=gcd(gcd(abs(Dv[0]),abs(Dv[1])),abs(Dv[2]))
    s1,s2,s3=(x//g for x in Dv)
    # triangle inequality
    if not (s1+s2>s3 and s1+s3>s2 and s2+s3>s1): return None
    p=Fraction(s1+s2+s3,2)
    area2=p*(p-s1)*(p-s2)*(p-s3)
    tile2=Fraction(3,16)*a*a*b*b
    r2=area2/tile2
    rn,rd=isqrt(r2.numerator),isqrt(r2.denominator)
    if rn*rn!=r2.numerator or rd*rd!=r2.denominator: return None
    return Fraction(rn,rd)

print("\nScanning primitive 60-triples (c^2=a^2+b^2-ab) for N=19 feasibility per scalene shape:")
hits=[]; mins={}
for a in range(1,300):
    for b in range(1,300):
        c=is60(a,b)
        if not c: continue
        for sh in scal:
            n0=N0(sh,a,b,c)
            if n0 is None: continue
            mins[sh]=min(mins.get(sh,n0),n0)
            k2=Fraction(19)/n0
            if k2.denominator==1 and isqrt(k2.numerator)**2==k2.numerator:
                hits.append((sh,a,b,c,n0))
for sh in scal:
    print(f"   shape {sh}: min N0 = {mins.get(sh,'(no integer ABC)')}")
print(f"\nN=19 hits for pi/3 tile scalene shapes: {hits if hits else 'NONE -> N=19 excluded for pi/3 scalene too'}")
