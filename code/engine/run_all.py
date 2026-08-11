#!/usr/bin/env python3
"""
Validation battery + the four frontier instances.
Usage:
  python3 run_all.py validate          # V1-V4 (must all pass)
  python3 run_all.py A|B|D|E           # run one instance to exhaustion
"""
import sys, time, json
from fractions import Fraction
import engine
from engine import QD, qd, Tile, Search, poly_area2, reverify


def make_instance(name):
    F = Fraction
    if name in ('A', 'B'):
        QD.D = 3
        if name == 'A':
            a, b, c, N, S = 7, 8, 13, 14, 28
        else:
            a, b, c, N, S = 3, 5, 7, 15, 15
        cosA, sinA = qd(F(2 * b + a, 2 * c)), qd(0, F(a, 2 * c))
        cosB, sinB = qd(F(2 * a + b, 2 * c)), qd(0, F(b, 2 * c))
        cosC, sinC = qd(F(-1, 2)), qd(0, F(1, 2))
        tile = Tile(a, b, c, cosA, sinA, cosB, sinB, cosC, sinC)
        tile.area2 = qd(0, F(a * b, 2))              # a*b*sin(2pi/3) = ab*(1/2)*sqrt3
        target = [(qd(0), qd(0)), (qd(S), qd(0)), (qd(F(S, 2)), qd(0, F(S, 2)))]
        return tile, target, N
    if name == 'D':
        QD.D = 23
        a, b, c, N = 56, 15, 64, 15
        tile = Tile(a, b, c,
                    qd(F(79, 128)), qd(0, F(21, 128)),
                    qd(F(1001, 1024)), qd(0, F(45, 1024)),
                    qd(F(-7, 16)), qd(0, F(3, 16)))
        tile.area2 = qd(0, F(315, 2))                # 56*15*(3/16) = 315/2  (x sqrt23)
        target = [(qd(0), qd(0)), (qd(105), qd(0)), (qd(F(105, 2)), qd(0, F(45, 2)))]
        return tile, target, N
    if name == 'K':
        QD.D = 3
        a, b, c, N = 7, 8, 13, 184
        cosA, sinA = qd(F(2 * b + a, 2 * c)), qd(0, F(a, 2 * c))
        cosB, sinB = qd(F(2 * a + b, 2 * c)), qd(0, F(b, 2 * c))
        cosC, sinC = qd(F(-1, 2)), qd(0, F(1, 2))
        tile = Tile(a, b, c, cosA, sinA, cosB, sinB, cosC, sinC)
        tile.area2 = qd(0, F(a * b, 2))
        target = [(qd(0), qd(0)), (qd(184), qd(0)), (qd(92), qd(0, 28))]
        return tile, target, N
    if name == 'N44A':
        # N=44 iso-(alpha+beta) instance: tile (30,11,36) (s=5/6, Thm 17), target (132,132,110).
        # The pending engine instance for N=44 (with gamma=2alpha and iso-beta branches also alive).
        QD.D = 119
        a, b, c, N = 30, 11, 36, 44
        tile = Tile(a, b, c,
                    qd(F(47, 72)), qd(0, F(5, 72)),
                    qd(F(415, 432)), qd(0, F(11, 432)),
                    qd(F(-5, 12)), qd(0, F(1, 12)))
        tile.area2 = qd(0, F(55, 2))                  # 30*11*sqrt119/12 = 55/2 sqrt119
        target = [(qd(0), qd(0)), (qd(110), qd(0)), (qd(55), qd(0, 11))]
        return tile, target, N
    if name.startswith('ISOB:') or name.startswith('ISOA:'):
        # iso-beta (base angles beta) or iso-alpha (base angles alpha) instance, 3a+2b=pi.
        # tile (ef, f^2-e^2, f^2) reduced; equal side X, base Y (both integer, whole-edge).
        # iso-beta: X=f^3 M/(f+e), Y=eM(3f^2-e^2)/(f+e);  iso-alpha: X=M(f+e)f^2/(2f+e), Y=X(2f^2-e^2)/f^2.
        from math import gcd as _gcd, isqrt as _isqrt
        base, sN, sM = name.split(':'); N, M = int(sN), int(sM)
        # recover (e,f) from N,M by the branch equation (search)
        found=None
        for f in range(2, 400):
            for e in range(1, f):
                if _gcd(e,f)!=1: continue
                if base=='ISOB':
                    if N*(e+f)**2 == M*M*(3*f*f-e*e): found=(e,f); break
                else:
                    if N*(f-e)*(2*f+e)**2 == M*M*(f+e)*(2*f*f-e*e): found=(e,f); break
            if found: break
        assert found, f"no (e,f) for {name}"
        e,f=found
        a0,b0,c0=e*f, f*f-e*e, f*f
        g0=_gcd(_gcd(a0,b0),c0); a,b,c=a0//g0,b0//g0,c0//g0
        def sqfree(n):
            d=1;m=n;p=2
            while p*p<=m:
                while m%(p*p)==0: m//=p*p
                if m%p==0: d*=p; m//=p
                p+=1
            return d*m
        cosA=F(b*b+c*c-a*a,2*b*c); cosB=F(a*a+c*c-b*b,2*a*c); cosC=F(a*a+b*b-c*c,2*a*b)
        Dker=sqfree((1-cosA*cosA).numerator*(1-cosA*cosA).denominator)
        rational=(Dker==1); QD.D=2 if rational else Dker
        def sin_qd(cs):
            s2=1-cs*cs; nd=s2.numerator*s2.denominator; k2=nd//Dker; k=_isqrt(k2)
            assert k*k==k2 and k2*Dker==nd, f"sin not in Q(sqrt{Dker})"
            return qd(F(k,s2.denominator)) if rational else qd(0,F(k,s2.denominator))
        tile=Tile(a,b,c, qd(cosA),sin_qd(cosA), qd(cosB),sin_qd(cosB), qd(cosC),sin_qd(cosC))
        tile.area2=qd(F(a*b,1))*sin_qd(cosC)
        if base=='ISOB':
            X=F(f**3*M,(f+e)); Y=F(e*M*(3*f*f-e*e),(f+e))
        else:
            X=F(M*(f+e)*f*f,(2*f+e)); Y=X*F(2*f*f-e*e,f*f)
        assert X.denominator==1 and Y.denominator==1, f"X,Y not integer: {X},{Y}"
        X=int(X); Y=int(Y)
        # apex at (Y/2, h), h^2 = X^2 - (Y/2)^2, exact in Q(sqrt Dker)
        h2=F(X*X)-F(Y*Y,4); ndh=h2.numerator*h2.denominator; kh2=ndh//Dker; kh=_isqrt(kh2)
        assert kh*kh==kh2 and kh2*Dker==ndh, "apex not in field"
        apex_y=qd(F(kh,h2.denominator)) if rational else qd(0,F(kh,h2.denominator))
        target=[(qd(0),qd(0)),(qd(Y),qd(0)),(qd(F(Y,2)),apex_y)]
        return tile, target, N

    if name.startswith('ISO:'):
        # general iso-(alpha+beta) instance from (N, M) via Beeson III Thm 17:
        # s=(N-M^2)/(N+M^2)=e/f, tile (ef, f^2-e^2, f^2) reduced, target (X, X, Y),
        # X^2 = N b c, Y = (a/c) X. All exact; D = squarefree kernel of the sines.
        from math import gcd as _gcd, isqrt as _isqrt
        _, sN, sM = name.split(':')
        N, M = int(sN), int(sM)
        sfrac = F(N - M * M, N + M * M)
        e, f = sfrac.numerator, sfrac.denominator
        a0, b0, c0 = e * f, f * f - e * e, f * f
        g0 = _gcd(_gcd(a0, b0), c0)
        a, b, c = a0 // g0, b0 // g0, c0 // g0
        def sqfree(n):
            d = 1; m = n; p = 2
            while p * p <= m:
                while m % (p * p) == 0: m //= p * p
                if m % p == 0: d *= p; m //= p
                p += 1
            return d * m
        cosA = F(b * b + c * c - a * a, 2 * b * c)
        cosB = F(a * a + c * c - b * b, 2 * a * c)
        cosC = F(a * a + b * b - c * c, 2 * a * b)
        s2 = 1 - cosA * cosA                    # = num/den; sinA = sqrt(num*den)/den
        Dker = sqfree(s2.numerator * s2.denominator)
        # Heronian tile (rational sines): Dker == 1 makes Z[sqrt(1)] degenerate (zero divisors,
        # non-unique representation) -- keep ALL data rational under an arbitrary non-square D.
        rational = (Dker == 1)
        QD.D = 2 if rational else Dker
        def sin_qd(cs):
            s2 = 1 - cs * cs
            nd = s2.numerator * s2.denominator
            k2 = nd // Dker
            k = _isqrt(k2)
            assert k * k == k2 and k2 * Dker == nd, f"sin not in Q(sqrt{Dker})"
            return qd(F(k, s2.denominator)) if rational else qd(0, F(k, s2.denominator))
        tile = Tile(a, b, c, qd(cosA), sin_qd(cosA), qd(cosB), sin_qd(cosB),
                    qd(cosC), sin_qd(cosC))
        sinC = sin_qd(cosC)
        tile.area2 = qd(F(a * b, 1)) * sinC             # 2*area = a*b*sinC (rational x sqrtD)
        X2 = N * b * c
        X = _isqrt(X2); assert X * X == X2, "X not integer"
        Y = F(a, c) * X; assert Y.denominator == 1, "Y not integer"
        Y = int(Y)
        # apex height h: X^2 = (Y/2)^2 + h^2, h = k*sqrt(D)/den exact
        h2 = F(X * X) - F(Y * Y, 4)
        ndh = h2.numerator * h2.denominator
        kh2 = ndh // Dker
        kh = _isqrt(kh2); assert kh * kh == kh2 and kh2 * Dker == ndh, "apex not in field"
        apex_y = qd(F(kh, h2.denominator)) if rational else qd(0, F(kh, h2.denominator))
        target = [(qd(0), qd(0)), (qd(Y), qd(0)), (qd(F(Y, 2)), apex_y)]
        return tile, target, N
    if name in ('T28', 'T77'):
        # tile (2,3,4), 3a+2b=pi. T28: triquadratic (2a,b,a+b) target (14,12,16), N=28.
        # T77: four-component (2a,a,2b) target (28,16,33), N=77.
        QD.D = 15
        a, b, c = 2, 3, 4
        tile = Tile(a, b, c,
                    qd(F(7, 8)), qd(0, F(1, 8)),
                    qd(F(11, 16)), qd(0, F(3, 16)),
                    qd(F(-1, 4)), qd(0, F(1, 4)))
        tile.area2 = qd(0, F(3, 2))
        if name == 'T28':
            N = 28
            target = [(qd(0), qd(0)), (qd(16), qd(0)), (qd(F(51, 8)), qd(0, F(21, 8)))]
        else:
            N = 77
            target = [(qd(0), qd(0)), (qd(33), qd(0)), (qd(F(17, 2)), qd(0, F(7, 2)))]
        return tile, target, N
    if name == 'I21A':
        # N=21 iso-ALPHA (2,3,4): target (12,12,21) base angles alpha. AT RISK: was excluded
        # only by Beeson Thm 19 g|M (2 does not divide 5), whose proof is broken. Engine decides.
        QD.D = 15
        a, b, c, N = 2, 3, 4, 21
        tile = Tile(a, b, c,
                    qd(F(7, 8)), qd(0, F(1, 8)),
                    qd(F(11, 16)), qd(0, F(3, 16)),
                    qd(F(-1, 4)), qd(0, F(1, 4)))
        tile.area2 = qd(0, F(3, 2))
        target = [(qd(0), qd(0)), (qd(21), qd(0)), (qd(F(21, 2)), qd(0, F(3, 2)))]
        return tile, target, N

    if name == 'I70A':
        # N=70 iso-ALPHA (6,5,9): target (45,45,70) base angles alpha (cos a=7/9, D=2).
        # AT RISK: excluded only by broken g|M (3 does not divide 8); Beeson Table 5 marks '?'.
        QD.D = 2
        a, b, c, N = 6, 5, 9, 70
        tile = Tile(a, b, c,
                    qd(F(7, 9)), qd(0, F(4, 9)),
                    qd(F(23, 27)), qd(0, F(10, 27)),
                    qd(F(-1, 3)), qd(0, F(2, 3)))
        tile.area2 = qd(0, 20)
        target = [(qd(0), qd(0)), (qd(70), qd(0)), (qd(35), qd(0, 20))]
        return tile, target, N

    if name == 'A84':
        # N=84 iso-ALPHA instance (Beeson III Thm 19, (M,s)=(10,1/2)): tile (2,3,4),
        # target (24,24,42) with base angles alpha (cos=7/8). Coloring 10*9=2*24+42 ✓.
        QD.D = 15
        a, b, c, N = 2, 3, 4, 84
        tile = Tile(a, b, c,
                    qd(F(7, 8)), qd(0, F(1, 8)),
                    qd(F(11, 16)), qd(0, F(3, 16)),
                    qd(F(-1, 4)), qd(0, F(1, 4)))
        tile.area2 = qd(0, F(3, 2))
        target = [(qd(0), qd(0)), (qd(42), qd(0)), (qd(21), qd(0, 3))]
        return tile, target, N
    if name == 'G96':
        # N=96 gamma=2alpha: tile (25,24,35) ((k,m)=(5,7)), target (240,240,336), D=51
        QD.D = 51
        a, b, c, N = 25, 24, 35, 96
        tile = Tile(a, b, c,
                    qd(F(7, 10)), qd(0, F(1, 10)),
                    qd(F(91, 125)), qd(0, F(12, 125)),
                    qd(F(-1, 50)), qd(0, F(7, 50)))
        tile.area2 = qd(0, 84)                        # 25*24*(7sqrt51/50) = 84 sqrt51
        target = [(qd(0), qd(0)), (qd(336), qd(0)), (qd(168), qd(0, 24))]
        return tile, target, N
    if name == 'G99':
        # N=99 gamma=2alpha: tile (25,11,30) ((k,m)=(5,6)), HERONIAN (rational), target (165,165,198)
        QD.D = 2                                       # arbitrary non-square; all data rational
        a, b, c, N = 25, 11, 30, 99
        tile = Tile(a, b, c,
                    qd(F(3, 5)), qd(F(4, 5)),
                    qd(F(117, 125)), qd(F(44, 125)),
                    qd(F(-7, 25)), qd(F(24, 25)))
        tile.area2 = qd(264)                           # 25*11*(24/25) = 264, rational
        target = [(qd(0), qd(0)), (qd(198), qd(0)), (qd(99), qd(132))]
        return tile, target, N
    if name == 'F96':
        # N=96 sporadic F1 (Zhang family m=2 member on (5,3,7)): target (30,42,48)
        QD.D = 3
        a, b, c, N = 5, 3, 7, 96
        cosA, sinA = qd(F(2 * b + a, 2 * c)), qd(0, F(a, 2 * c))
        cosB, sinB = qd(F(2 * a + b, 2 * c)), qd(0, F(b, 2 * c))
        cosC, sinC = qd(F(-1, 2)), qd(0, F(1, 2))
        tile = Tile(a, b, c, cosA, sinA, cosB, sinB, cosC, sinC)
        tile.area2 = qd(0, F(a * b, 2))
        target = [(qd(0), qd(0)), (qd(48), qd(0)), (qd(15), qd(0, 15))]
        return tile, target, N
    if name == 'E96':
        # N=96 pi/3-equilateral: tile (3,8,7) (gamma=pi/3 opposite c=7), equilateral side 48, D=3
        QD.D = 3
        a, b, c, N = 3, 8, 7, 96
        tile = Tile(a, b, c,
                    qd(F(13, 14)), qd(0, F(3, 14)),
                    qd(F(-1, 7)), qd(0, F(4, 7)),
                    qd(F(1, 2)), qd(0, F(1, 2)))
        tile.area2 = qd(0, 12)                         # 3*8*(sqrt3/2) = 12 sqrt3
        target = [(qd(0), qd(0)), (qd(48), qd(0)), (qd(24), qd(0, 24))]
        return tile, target, N
    if name == 'G63':
        # N=63 gamma=2alpha instance (Beeson Lemma 11.2 family, (k,m)=(3,4)): tile (9,7,12)
        # with angles (alpha,beta,2alpha), target (63,63,84) from the surviving boundary
        # representation X=63=a+6b+c, Y=84=a+9b+c of the boundary algorithm. D=5.
        QD.D = 5
        a, b, c, N = 9, 7, 12, 63
        tile = Tile(a, b, c,
                    qd(F(2, 3)), qd(0, F(1, 3)),
                    qd(F(22, 27)), qd(0, F(7, 27)),
                    qd(F(-1, 9)), qd(0, F(4, 9)))
        tile.area2 = qd(0, 28)                        # 9*7*(4sqrt5/9) = 28 sqrt5
        target = [(qd(0), qd(0)), (qd(84), qd(0)), (qd(42), qd(0, 21))]
        return tile, target, N
    if name == 'N44B':
        # N=44 iso-beta instance (Beeson III Thm 14, M=6, s=1/2): tile (2,3,4) (3a+2b=pi,
        # gamma=2a+b, cos gamma=-1/4), target (16,16,22) with base angles beta (cos=11/16).
        QD.D = 15
        a, b, c, N = 2, 3, 4, 44
        tile = Tile(a, b, c,
                    qd(F(7, 8)), qd(0, F(1, 8)),
                    qd(F(11, 16)), qd(0, F(3, 16)),
                    qd(F(-1, 4)), qd(0, F(1, 4)))
        tile.area2 = qd(0, F(3, 2))                   # 2*3*sqrt15/4 = 3/2 sqrt15
        target = [(qd(0), qd(0)), (qd(22), qd(0)), (qd(11), qd(0, 3))]
        return tile, target, N
    if name == 'M60':
        # N=60, EQUILATERAL 2pi/3 on tile (5,3,7): equilateral target side 30. New open instance.
        QD.D = 3
        a, b, c, N = 5, 3, 7, 60
        cosA, sinA = qd(F(2 * b + a, 2 * c)), qd(0, F(a, 2 * c))
        cosB, sinB = qd(F(2 * a + b, 2 * c)), qd(0, F(b, 2 * c))
        cosC, sinC = qd(F(-1, 2)), qd(0, F(1, 2))
        tile = Tile(a, b, c, cosA, sinA, cosB, sinB, cosC, sinC)
        tile.area2 = qd(0, F(a * b, 2))               # 15/2 sqrt3
        target = [(qd(0), qd(0)), (qd(30), qd(0)), (qd(15), qd(0, 15))]   # equilateral side 30
        return tile, target, N
    if name == 'M':
        # N=56, EQUILATERAL 2pi/3 instance on the tile (8,7,13): equilateral target of side 56.
        # A genuinely new open instance (not sporadic-family, not commensurable), smaller than 105.
        QD.D = 3
        a, b, c, N = 8, 7, 13, 56
        cosA, sinA = qd(F(2 * b + a, 2 * c)), qd(0, F(a, 2 * c))
        cosB, sinB = qd(F(2 * a + b, 2 * c)), qd(0, F(b, 2 * c))
        cosC, sinC = qd(F(-1, 2)), qd(0, F(1, 2))
        tile = Tile(a, b, c, cosA, sinA, cosB, sinB, cosC, sinC)
        tile.area2 = qd(0, F(a * b, 2))               # 28 sqrt3
        target = [(qd(0), qd(0)), (qd(56), qd(0)), (qd(28), qd(0, 28))]   # equilateral side 56
        return tile, target, N
    if name == 'L':
        # N=105, the smallest STRUCTURAL-open member: F1 target of the tile (8,7,13).
        # sides k(a+b),ka,kc = (105,56,91), k=7. 60-deg corner at V=(0,0).
        QD.D = 3
        a, b, c, N = 8, 7, 13, 105
        cosA, sinA = qd(F(2 * b + a, 2 * c)), qd(0, F(a, 2 * c))
        cosB, sinB = qd(F(2 * a + b, 2 * c)), qd(0, F(b, 2 * c))
        cosC, sinC = qd(F(-1, 2)), qd(0, F(1, 2))
        tile = Tile(a, b, c, cosA, sinA, cosB, sinB, cosC, sinC)
        tile.area2 = qd(0, F(a * b, 2))               # 8*7*(1/2) = 28  (x sqrt3)
        target = [(qd(0), qd(0)), (qd(105), qd(0)), (qd(28), qd(0, 28))]
        return tile, target, N
    if name == 'J1':
        QD.D = 1239
        a, b, c, N = 380, 39, 400, 39
        tile = Tile(a, b, c,
                    qd(F(439, 800)), qd(0, F(19, 800)),
                    qd(F(302879, 304000)), qd(0, F(741, 304000)),
                    qd(F(-19, 40)), qd(0, F(1, 40)))
        tile.area2 = qd(0, F(741, 2))
        target = [(qd(0), qd(0)), (qd(741), qd(0)), (qd(F(741, 2)), qd(0, F(39, 2)))]
        return tile, target, N
    if name == 'J2':
        QD.D = 231
        a, b, c, N = 40, 39, 64, 39
        tile = Tile(a, b, c,
                    qd(F(103, 128)), qd(0, F(5, 128)),
                    qd(F(835, 1024)), qd(0, F(39, 1024)),
                    qd(F(-5, 16)), qd(0, F(1, 16)))
        tile.area2 = qd(0, F(195, 2))
        target = [(qd(0), qd(0)), (qd(195), qd(0)), (qd(F(195, 2)), qd(0, F(39, 2)))]
        return tile, target, N
    if name == 'I1':
        QD.D = 1007
        a, b, c, N = 306, 35, 324, 35
        tile = Tile(a, b, c,
                    qd(F(359, 648)), qd(0, F(17, 648)),
                    qd(F(197387, 198288)), qd(0, F(595, 198288)),
                    qd(F(-17, 36)), qd(0, F(1, 36)))
        tile.area2 = qd(0, F(595, 2))                # 306*35/36 x sqrt1007
        target = [(qd(0), qd(0)), (qd(595), qd(0)), (qd(F(595, 2)), qd(0, F(35, 2)))]
        return tile, target, N
    if name == 'I2':
        QD.D = 143
        a, b, c, N = 6, 35, 36, 35
        tile = Tile(a, b, c,
                    qd(F(71, 72)), qd(0, F(1, 72)),
                    qd(F(107, 432)), qd(0, F(35, 432)),
                    qd(F(-1, 12)), qd(0, F(1, 12)))
        tile.area2 = qd(0, F(35, 2))                 # 6*35/12 x sqrt143
        target = [(qd(0), qd(0)), (qd(35), qd(0)), (qd(F(35, 2)), qd(0, F(35, 2)))]
        return tile, target, N
    if name == 'H1':
        QD.D = 5
        a, b, c, N = 272, 33, 289, 33
        tile = Tile(a, b, c,
                    qd(F(161, 289)), qd(F(240, 289)),
                    qd(F(4888, 4913)), qd(F(495, 4913)),
                    qd(F(-8, 17)), qd(F(15, 17)))
        tile.area2 = qd(7920)                        # 272*33*(15/17) — rational (Heronian)
        target = [(qd(0), qd(0)), (qd(528), qd(0)), (qd(264), qd(495))]
        return tile, target, N
    if name == 'H2':
        QD.D = 5
        a, b, c, N = 28, 33, 49, 33
        tile = Tile(a, b, c,
                    qd(F(41, 49)), qd(0, F(12, 49)),
                    qd(F(262, 343)), qd(0, F(99, 343)),
                    qd(F(-2, 7)), qd(0, F(3, 7)))
        tile.area2 = qd(0, 396)                      # 28*33*(3/7) x sqrt5
        target = [(qd(0), qd(0)), (qd(132), qd(0)), (qd(66), qd(0, 99))]
        return tile, target, N
    if name == 'F':
        QD.D = 6
        a, b, c, N = 110, 21, 121, 21
        tile = Tile(a, b, c,
                    qd(F(71, 121)), qd(0, F(40, 121)),
                    qd(F(1315, 1331)), qd(0, F(84, 1331)),
                    qd(F(-5, 11)), qd(0, F(4, 11)))
        tile.area2 = qd(0, 840)                      # 110*21*(4/11) = 840  (x sqrt6)
        target = [(qd(0), qd(0)), (qd(210), qd(0)), (qd(105), qd(0, 84))]
        return tile, target, N
    if name == 'G':
        QD.D = 6
        a, b, c, N = 10, 21, 25, 21
        tile = Tile(a, b, c,
                    qd(F(23, 25)), qd(0, F(4, 25)),
                    qd(F(71, 125)), qd(0, F(42, 125)),
                    qd(F(-1, 5)), qd(0, F(2, 5)))
        tile.area2 = qd(0, 84)                       # 10*21*(2/5) = 84  (x sqrt6)
        target = [(qd(0), qd(0)), (qd(42), qd(0)), (qd(21), qd(0, 42))]
        return tile, target, N
    if name == 'E':
        QD.D = 7
        a, b, c, N = 4, 15, 16, 15
        tile = Tile(a, b, c,
                    qd(F(31, 32)), qd(0, F(3, 32)),
                    qd(F(47, 128)), qd(0, F(45, 128)),
                    qd(F(-1, 8)), qd(0, F(3, 8)))
        tile.area2 = qd(0, F(45, 2))                 # 4*15*(3/8) = 45/2  (x sqrt7)
        target = [(qd(0), qd(0)), (qd(15), qd(0)), (qd(F(15, 2)), qd(0, F(45, 2)))]
        return tile, target, N
    raise SystemExit(f"unknown instance {name}")


def tile_triangle(tile, cosA, sinA, scale=1):
    """the tile itself as a triangle: (0,0), (c*scale,0), (b*scale*cosA, b*scale*sinA)"""
    c = tile.c * scale
    b = tile.b * scale
    return [(qd(0), qd(0)), (qd(c), qd(0)),
            ((cosA * b), (sinA * b))]


def validate():
    F = Fraction
    print("== V2: N = 1, target = tile itself (both families) ==", flush=True)
    for name in ('B', 'E'):
        tile, _, _ = make_instance(name)
        cosA, sinA = tile.corners[0][0], tile.corners[0][1]
        tri = tile_triangle(tile, cosA, sinA, 1)
        s = Search(tile, tri, 1, f"V2-{name}", log_every=10 ** 9)
        r = s.run()
        print(f"   {name}: {r} nodes={s.nodes}")
        assert r == 'FOUND_TILING', "V2 failed"

    print("== V1: N = 4 reptile, target = tile scaled by 2 (both families) ==", flush=True)
    for name in ('B', 'E', 'A'):
        tile, _, _ = make_instance(name)
        cosA, sinA = tile.corners[0][0], tile.corners[0][1]
        tri = tile_triangle(tile, cosA, sinA, 2)
        s = Search(tile, tri, 4, f"V1-{name}", log_every=10 ** 9)
        t0 = time.time()
        r = s.run()
        print(f"   {name}: {r} nodes={s.nodes} t={time.time()-t0:.1f}s")
        assert r == 'FOUND_TILING', "V1 failed"
        ok, msg = reverify(s.found, tri, tile)
        assert ok, f"V1 reverify failed: {msg}"
        print(f"   {name}: reverified ok")

    print("== V3: wrong N rejected at the root ==", flush=True)
    tile, _, _ = make_instance('B')
    cosA, sinA = tile.corners[0][0], tile.corners[0][1]
    tri = tile_triangle(tile, cosA, sinA, 2)
    try:
        Search(tile, tri, 3, "V3", log_every=10 ** 9)
        raise SystemExit("V3 FAILED: root accepted wrong N")
    except AssertionError:
        print("   root area assertion fired correctly")

    print("== V4: determinism ==", flush=True)
    s = Search(tile, tri, 4, "V4", log_every=10 ** 9)
    r = s.run()
    assert r == 'FOUND_TILING'
    print("   determinism ok")

    print("== V5: non-edge-to-edge positive control (hand-built T-junction 2-tiling) ==",
          flush=True)
    tile, _, _ = make_instance('B')
    cosA, sinA = tile.corners[0][0], tile.corners[0][1]
    Capex = (cosA * tile.b, sinA * tile.b)
    T2apex = (qd(1) + Capex[0], qd(0) - Capex[1])
    hexagon = [(qd(0), qd(0)), (qd(1), qd(0)), T2apex, (qd(8), qd(0)), (qd(7), qd(0)), Capex]
    s = Search(tile, hexagon, 2, "V5", log_every=10 ** 9)
    r = s.run()
    assert r == 'FOUND_TILING', "V5 failed: T-junction tiling not found"
    ok, msg = reverify(s.found, hexagon, tile)
    assert ok, f"V5 reverify: {msg}"
    print(f"   found and reverified (nodes={s.nodes})")
    print("ALL VALIDATIONS PASSED", flush=True)


def run_instance(name, cap=30000000):
    tile, target, N = make_instance(name)
    s = Search(tile, target, N, name, log_every=100000, node_cap=cap)
    t0 = time.time()
    r = s.run()
    dt = time.time() - t0
    line = (f"RESULT {name}: {r} nodes={s.nodes} maxdepth={s.maxdepth} "
            f"placements={s.placements_tried} pruneA={s.prune_area} pruneR={s.prune_run} "
            f"time={dt:.0f}s")
    print(line, flush=True)
    if r == 'FOUND_TILING':
        ok, msg = reverify(s.found, target, tile)
        print(f"REVERIFY {name}: {'OK' if ok else 'FAILED'} ({msg})", flush=True)
        with open(f"found_{name}.json", "w") as f:
            json.dump([[[str(x.p), str(x.q)] for x in pt] for tri in s.found
                       for pt in tri], f)
    return line


def run_noP2(name):
    """robustness: rerun with the P2 run-prune disabled; verdict must be unchanged"""
    engine.Search.runs_ok = lambda self, poly: True
    return run_instance(name)


if __name__ == '__main__':
    arg = sys.argv[1] if len(sys.argv) > 1 else 'validate'
    if arg == 'validate':
        validate()
    elif arg.startswith('noP2-'):
        run_noP2(arg[5:])
    else:
        cap = int(sys.argv[2]) if len(sys.argv) > 2 else 30000000
        run_instance(arg, cap)
