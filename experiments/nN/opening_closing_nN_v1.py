"""
MANUSCRIPT section 7.2, last line: "the first instant of loneliness, when it exists, is
always an OPENING (8k+1)/(8d) for one of the runner's own differences -- never a closing."

Stated at n = 8 and without proof. This tests it at other orders.

An in-the-way zone of reading s is the OPEN interval ((nk-1)/(ns), (nk+1)/(ns)). Its RIGHT
endpoint (nk+1)/(ns) is an OPENING -- the instant a blocker clears. Its LEFT endpoint
(nk-1)/(ns) is a CLOSING -- the instant a blocker arrives. Both are clear, since zones are
open; the claim is about which kind the FIRST clear instant is.

Three outcomes are possible and are counted separately:
    window-start   the first clear instant is u = 1/n itself, no blocker involved
    opening        it is some zone's right endpoint
    closing        it is some zone's left endpoint  <- the claim says this never happens

A point can be both a left endpoint of one zone and a right endpoint of another. Such a
point IS an opening: the blocker whose zone ends there has cleared, and the one whose zone
begins there has not yet arrived. It is classified as an opening, and only a
left-endpoint-ONLY instant can refute the claim.

*** This ordering is load-bearing and an earlier version of this script had it backwards,
which manufactured a nonzero "closing" column out of coincidences and would have been
reported as a defect in the manuscript. ***

Note also that the window start u = 1/n is itself an opening: it is the right endpoint of
the k = 0 zone of the reading s = 1, the nearest runner's own difference. So all outcomes
below collapse to the claim's "opening".
"""
import sys, itertools
from fractions import Fraction as F
from math import gcd
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from exhaustive_nN_v1 import readings, zones

def classify(v, i, n):
    lo, hi = F(1, n), F(n - 1, n)
    Z = []
    for s in readings(v, i, n):
        Z.extend(zones(s, n, lo, hi))
    lefts = {a for a, _ in Z if lo <= a <= hi}
    rights = {b for _, b in Z if lo <= b <= hi}
    cands = sorted({lo, hi} | lefts | rights)
    for u in cands:
        if any(a < u < b for a, b in Z):
            continue
        if u == lo:
            return "window-start"
        if u in rights:
            return "opening"          # an opening even when also a left endpoint
        if u in lefts:
            return "closing"          # left endpoint ONLY -- the refuting case
        return "other"
    return "none"

if __name__ == "__main__":
    print("first clear instant, classified. 'closing' is the column that would refute\n")
    print(f"{'n':>3} {'V':>4} {'instances':>10} {'window-start':>13} {'opening':>9} "
          f"{'closing':>9} {'other':>7}")
    print("-" * 62)
    for n, V in [(5, 22), (6, 19), (7, 17), (8, 16), (9, 15), (10, 14), (11, 14)]:
        c = {"window-start": 0, "opening": 0, "closing": 0, "other": 0, "none": 0}
        tot = 0
        for v in itertools.combinations(range(1, V + 1), n):
            g = 0
            for x in v:
                g = gcd(g, x)
            if g != 1:
                continue
            for i in range(n):
                tot += 1
                c[classify(list(v), i, n)] += 1
        print(f"{n:>3} {V:>4} {tot:>10} {c['window-start']:>13} {c['opening']:>9} "
              f"{c['closing']:>9} {c['other']:>7}", flush=True)
        if c["none"]:
            print(f"        NO CLEAR INSTANT in {c['none']} cases", flush=True)
