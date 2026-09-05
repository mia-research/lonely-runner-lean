"""De-risk BHK Part 6 Claim 21, p=1 diagonal case.
p=1 speeds: w0=g, w1=g(q-1), w2=gq, w3=g(q+1), w4=g(2q+1) [the squeezed s=2q+1].
Construction: witness m with m/q in (57)=[1/3+1/(6q), 5/12-1/(6q)];
              qe=(m+1/6)/w2 should be a LONELY point (all 5 runners circDist>=1/6).
Also check the wider range [1/3+d, 2/3-d] claim and the gap edges pe,qe 1234-safety.
"""
import math
from fractions import Fraction as F

def circdist(x):
    f = x - math.floor(x)
    return min(f, 1-f)

def frac(x):
    return x - math.floor(x)

bad = 0
checked = 0
no_witness = 0
for q in range(18, 121):
    for g in range(1, 6):
        w0, w1, w2, w3, w4 = g, g*(q-1), g*q, g*(q+1), g*(2*q+1)
        # sanity: diagonal w3=w0+w2, sum w0+w1=w2, s=2q+1
        assert w3 == w0+w2 and w0+w1 == w2
        d = F(1, 6*q)
        lo = F(1,3) + d
        hi = F(5,12) - d
        # find witness m: m/q in [lo, hi]
        m = None
        for mm in range(0, q+1):
            if lo <= F(mm, q) <= hi:
                m = mm
                break
        if m is None:
            no_witness += 1
            continue
        checked += 1
        # edges
        pe = F(m, w2) - F(1, 6*w2)   # (m-1/6)/w2
        qe = F(m, w2) + F(1, 6*w2)   # (m+1/6)/w2
        # check w2*pe = m-1/6, w2*qe=m+1/6
        assert w2*pe == F(m)-F(1,6) and w2*qe == F(m)+F(1,6)
        # 1234-safety (runners 0,1,2,3) at BOTH edges
        for edge in (pe, qe):
            for r in (w0, w1, w2, w3):
                cd = circdist(float(r*edge))
                if cd < 1/6 - 1e-12:
                    print(f"FAIL 1234-safe q={q} g={g} m={m} r={r} edge={edge} cd={cd}")
                    bad += 1
        # LONELY at qe: ALL FIVE runners circDist >= 1/6
        cds = [circdist(float(r*qe)) for r in (w0,w1,w2,w3,w4)]
        if min(cds) < 1/6 - 1e-12:
            print(f"FAIL lonely-qe q={q} g={g} m={m} cds={[round(c,4) for c in cds]}")
            bad += 1
        # runner4 specifically should be ~ 2/3 - m/q - d
        cd4 = circdist(float(w4*qe))
        expect = float(F(2,3) - F(m,q) - d)
        if abs(cd4 - expect) > 1e-9:
            print(f"FAIL runner4 q={q} m={m} cd4={cd4} expect={expect}")
            bad += 1

print(f"checked={checked} no_witness(q<16 only?)={no_witness} bad={bad}")
