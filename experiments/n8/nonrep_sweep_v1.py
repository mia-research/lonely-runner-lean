"""
nonrep_sweep_v1  --  exhaustive exact sweep for tuples with |S| <= 1/2.

|S| > 1/2  =>  union bound against B_{m1} u B_{m2} (total measure <= 1/2) closes
the case immediately.  So the whole difficulty is the set  {E_non : |S| <= 1/2}.

Exact arithmetic: breakpoints are Fractions j/e; on a cell (a,b) we have
floor(e*x) = floor(e*a) exactly, computed as (e*a.numerator)//a.denominator.
"""
from fractions import Fraction as F
import itertools, sys, json
from collections import Counter

FULL = frozenset(range(8))
BAD = {(rho, t): frozenset(r for r in range(8) if (rho * r + t) % 8 in (0, 7))
       for rho in range(1, 8) for t in range(8)}
# precompute bad as an 8-bit mask
MASK = {k: sum(1 << r for r in v) for k, v in BAD.items()}
ALL = 255

def safe_measure(speeds, rhos):
    pts = set()
    for e in speeds:
        for j in range(e):
            pts.add(F(j, e))
    p = sorted(pts); p.append(F(1))
    meas = F(0)
    for a, b in zip(p, p[1:]):
        an, ad = a.numerator, a.denominator
        cov = 0
        for e, rho in zip(speeds, rhos):
            cov |= MASK[(rho, ((e * an) // ad) % 8)]
        if cov != ALL:
            meas += b - a
    return meas

def windows(speeds, rhos):
    pts = set()
    for e in speeds:
        for j in range(e):
            pts.add(F(j, e))
    p = sorted(pts); p.append(F(1))
    out = []
    for a, b in zip(p, p[1:]):
        an, ad = a.numerator, a.denominator
        cov = 0
        for e, rho in zip(speeds, rhos):
            cov |= MASK[(rho, ((e * an) // ad) % 8)]
        if cov != ALL:
            if out and out[-1][1] == a: out[-1][1] = b
            else: out.append([a, b])
    return out

if __name__ == "__main__":
    QMAX = int(sys.argv[1])
    HALF = F(1, 2)
    small = []
    for rho0 in (2, 4, 6):
        rhos = (1, 3, 5, 7, rho0)
        best = None; cnt = 0; le_half = []
        for qs in itertools.product(range(QMAX + 1), repeat=5):
            speeds = tuple(8 * q + r for q, r in zip(qs, rhos))
            if len(set(speeds)) != 5:
                continue
            cnt += 1
            m = safe_measure(speeds, rhos)
            if best is None or m < best[0]:
                best = (m, speeds)
            if m <= HALF:
                le_half.append((m, speeds))
        le_half.sort()
        print(f"rho0={rho0}: {cnt} tuples (q<= {QMAX}, speeds <= {8*QMAX+7}).  "
              f"min |S| = {best[0]} at {best[1]}")
        print(f"   tuples with |S| <= 1/2 : {len(le_half)}")
        for m, s in le_half:
            print(f"      |S| = {m} = {float(m):.6f}   speeds {s}   windows "
                  f"{[(str(a),str(b)) for a,b in windows(s,rhos)]}")
        small.append((rho0, [(str(m), s) for m, s in le_half]))
        sys.stdout.flush()
    json.dump(small, open(sys.path[0] + f"/nonrep_sweep_v1_q{QMAX}.json", "w"), indent=1)
