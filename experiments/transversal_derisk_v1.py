"""
De-risk the transversal |j|>=2 cone pairs (BHK Case 5.2.3) before formalizing.

Setup identical to antidiag: S-points P_m=(frac(r*m/2q), frac(p*m/2q)), m odd;
R-window x in [1/6,1/2], y in [1/6,1/3]; C∩R=∅ = h_nogood.
Exceptional cone pair (i,j): (i/q,j/q) ∈ G = {(frac(m r/q),frac(m p/q))}, with
0<=i<6, -3-i/2<j<3+i/2; the EXCEPTIONAL one is the minimal (smallest i, then |j|).

Questions:
 Q1. For each (p,q,r) [bounds, q>=18], minimal cone pair → bucket transversals (|j|>=2).
 Q2. Among transversal tuples, which have C∩R=∅ (survivors)?  Does q<6|j| hold then?
 Q3. Survivor v1=p/q: is it >1/6 (⟹ would need P\R / pentagon) or <=1/6 (R suffices)?
 Q4. Apply BHK's extra bound (50) v4<(6+i)/(2|j|): does it kill the survivors?
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x - (x.numerator // x.denominator)
def S(l, p, q, r):
    u = 2*l + 1
    return frac(F(r*u, 2*q)), frac(F(p*u, 2*q))
XLO, XHI = F(1,6), F(1,2)
YLO, YHI = F(1,6), F(1,3)
def inR(X, Y): return XLO <= X <= XHI and YLO <= Y <= YHI

def cap_R_empty(p, q, r):
    for l in range(q):
        if inR(*S(l, p, q, r)):
            return False
    return True

def cone_pairs(p, q, r):
    """All nonzero cone pairs (i,j) with (i/q,j/q) in G, 0<=i<6, -3-i/2<j<3+i/2."""
    out = set()
    for m in range(q):
        i = (m*r) % q
        if i >= 6:
            continue
        j = (m*p) % q
        if j > q//2:
            j -= q
        # cone: -3 - i/2 < j < 3 + i/2  (use 2*: -6-i < 2j < 6+i)
        if -6 - i < 2*j < 6 + i and not (i == 0 and j == 0):
            out.add((i, j))
    return out

def minimal_pair(pairs):
    # exceptional = smallest i, then smallest |j| (approx BHK box-minimality)
    return min(pairs, key=lambda ij: (ij[0], abs(ij[1]), ij[1]))

def bound50_ok(i, j, p, q, r):
    # v4 < (6+i)/(2|j|)  <=>  2|j|*r < (6+i)*q   (only for j != 0)
    if j == 0:
        return True
    return 2*abs(j)*r < (6+i)*q

QMAX = 80
from collections import defaultdict
tot = defaultdict(int)      # (i,j) -> count of tuples whose minimal pair is (i,j), transversal
empty = defaultdict(list)   # (i,j) -> list of survivor tuples (C∩R empty)
empty50 = defaultdict(list) # same but also passing (50)
grid_viol = []              # survivors with q >= 6|j| (would break grid reduction)

for q in range(18, QMAX+1):
    for p in range(1, q):
        if 3*p >= q or gcd(p, q) != 1:
            continue
        for r in range(q+1, (3*q)//2 + 1):
            if 2*r >= 3*q:
                continue
            pairs = cone_pairs(p, q, r)
            if not pairs:
                continue
            i, j = minimal_pair(pairs)
            if abs(j) < 2:        # only transversal |j|>=2
                continue
            if i == 0:            # i=0 family handled separately
                continue
            tot[(i, j)] += 1
            if cap_R_empty(p, q, r):
                empty[(i, j)].append((p, q, r, F(p, q)))
                if q >= 6*abs(j):
                    grid_viol.append((i, j, p, q, r))
                if bound50_ok(i, j, p, q, r):
                    empty50[(i, j)].append((p, q, r, F(p, q)))

print(f"=== transversal minimal-pair census (q<= {QMAX}) ===")
print(f"{'pair':>8} {'#tuples':>8} {'#C∩R=∅':>8} {'#∅&(50)':>9}   survivor v1 range (with 50)")
for ij in sorted(tot):
    e = empty.get(ij, [])
    e50 = empty50.get(ij, [])
    v1s = [t[3] for t in e50]
    vr = f"{min(v1s)}..{max(v1s)}" if v1s else "-"
    over16 = sum(1 for v in v1s if v > F(1,6))
    print(f"{str(ij):>8} {tot[ij]:>8} {len(e):>8} {len(e50):>9}   {vr}  (v1>1/6: {over16})")

print(f"\nQ2 grid-reduction violations (C∩R=∅ but q>=6|j|): {len(grid_viol)}")
for t in grid_viol[:20]:
    print("   ", t)

# overall survivors passing (50)
allsurv = sum(len(v) for v in empty50.values())
print(f"\ntotal transversal survivors C∩R=∅ AND passing (50): {allsurv}")
print(f"total transversal survivors C∩R=∅ (no (50) filter): {sum(len(v) for v in empty.values())}")
