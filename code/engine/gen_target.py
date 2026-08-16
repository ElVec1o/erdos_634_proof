#!/usr/bin/env python3
"""Generate the base-beta target instance at (e,f), m=1:
   tile (ef, f^2-e^2, f^2), target (f^3, f^3, e(3f^2-e^2)), N = 3f^2-e^2."""
import sys
from math import gcd
def sqfree(D):
    s=1; d=2
    while d*d<=D:
        while D%(d*d)==0: D//=d*d; s*=d
        d+=1
    return D,s
def qd(p,q,d):
    g=gcd(gcd(abs(p),abs(q)),abs(d))
    if g: p,q,d=p//g,q//g,d//g
    if d<0: p,q,d=-p,-q,-d
    return f"{p} {q} {d}"
def inst(e,f):
    a,b,c=e*f,f*f-e*e,f*f
    N=3*f*f-e*e
    D,S=sqfree(4*f*f-e*e)
    L=[f"{D}", f"{a} {b} {c}"]
    L.append(f"{qd(2*f*f-e*e,0,2*f*f)}  {qd(0,e*S,2*f*f)}")                 # alpha
    L.append(f"{qd(e*(3*f*f-e*e),0,2*f**3)}  {qd(0,(f*f-e*e)*S,2*f**3)}")   # beta
    L.append(f"{qd(-e,0,2*f)}  {qd(0,S,2*f)}")                              # gamma
    L.append(qd(0,e*(f*f-e*e)*S,2))                                         # tile area2
    L.append(f"{N}")
    base=e*N
    L.append(f"{qd(0,0,1)}  {qd(0,0,1)}")
    L.append(f"{qd(base,0,1)}  {qd(0,0,1)}")
    # apex: x = base/2, y = (f^2-e^2)*sqrt(D)/2  (checked: y^2 = f^6 - base^2/4)
    L.append(f"{qd(base,0,2)}  {qd(0,(f*f-e*e)*S,2)}")
    return "\n".join(L)+"\n"
if __name__=="__main__":
    e,f=int(sys.argv[1]),int(sys.argv[2])
    sys.stdout.write(inst(e,f))
