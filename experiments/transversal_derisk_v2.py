"""
v2: faithful BHK (13)-box-minimality + extended range.
(13)-minimal: (i,j) in G-cone, nonzero, with NO nonzero G-element (k,l) in
[-|i|,|i|] x [-|j|,|j|] except the corners (±i,±j). This is what Corollary 6 yields.

Re-run the transversal census with box-minimality to see if (1,±2)'s mass survival
is real (i.e. (1,2) genuinely minimal) or an artifact. Extend q to 120 to see if
survivors persist (unbounded ⟹ genuine pentagon need) or are bounded small-q.
"""
from math import gcd
from fractions import Fraction as F
from collections import defaultdict

def frac(x): return x - (x.numerator // x.denominator)
def S(l, p, q, r):
    u = 2*l + 1
    return frac(F(r*u, 2*q)), frac(F(p*u, 2*q))
XLO, XHI, YLO, YHI = F(1,6), F(1,2), F(1,6), F(1,3)
def inR(X, Y): return XLO <= X <= XHI and YLO <= Y <= YHI
def cap_R_empty(p, q, r):
    return all(not inR(*S(l, p, q, r)) for l in range(q))

def in_G(i, j, p, q, r):
    """is (i/q mod1, j/q mod1) in G = {(m r mod q, m p mod q)/q}?"""
    # need m with m*r ≡ i and m*p ≡ j (mod q)
    ii, jj = i % q, j % q
    for m in range(q):
        if (m*r) % q == ii and (m*p) % q == jj:
            return True
    return False

def minimal_box_pair(p, q, r):
    """The (13)-box-minimal cone pair, or None. cone: 0<=i<6, -3-i/2<j<3+i/2."""
    cands = []
    for m in range(q):
        i = (m*r) % q
        if i >= 6: continue
        j = (m*p) % q
        if j > q//2: j -= q
        if -6 - i < 2*j < 6 + i and not (i == 0 and j == 0):
            cands.append((i, j))
    # filter to box-minimal
    def is_min(i, j):
        for k in range(-abs(i), abs(i)+1):
            for l in range(-abs(j), abs(j)+1):
                if (k, l) == (0, 0): continue
                if abs(k) == abs(i) and abs(l) == abs(j): continue
                if in_G(k, l, p, q, r):
                    return False
        return True
    mins = [(i, j) for (i, j) in cands if is_min(i, j)]
    if not mins: return None
    return min(mins, key=lambda ij: (ij[0], abs(ij[1]), ij[1]))

QMAX = 120
tot = defaultdict(int)
empty = defaultdict(list)
for q in range(18, QMAX+1):
    for p in range(1, q):
        if 3*p >= q or gcd(p, q) != 1: continue
        for r in range(q+1, (3*q)//2 + 1):
            if 2*r >= 3*q: continue
            mp = minimal_box_pair(p, q, r)
            if mp is None: continue
            i, j = mp
            if abs(j) < 2 or i == 0: continue
            tot[(i, j)] += 1
            if cap_R_empty(p, q, r):
                empty[(i, j)].append((p, q, r, F(p, q)))

print(f"=== box-minimal transversal census (q<= {QMAX}) ===")
print(f"{'pair':>8} {'#tuples':>8} {'#C∩R=∅':>8}   survivor q-range   v1-range   (#v1>1/6)")
for ij in sorted(tot):
    e = empty.get(ij, [])
    if e:
        qs = sorted(t[1] for t in e); v1s = [t[3] for t in e]
        info = f"q∈[{qs[0]},{qs[-1]}]  v1∈[{min(v1s)},{max(v1s)}]  (>{1/6:.2f}: {sum(1 for v in v1s if v>F(1,6))})"
    else:
        info = "(none)"
    print(f"{str(ij):>8} {tot[ij]:>8} {len(e):>8}   {info}")

# For (1,2)/(1,-2): are survivors unbounded in q? show count by q.
for pair in [(1,2),(1,-2)]:
    e = empty.get(pair, [])
    byq = defaultdict(int)
    for (p,q,r,v) in e: byq[q]+=1
    qs = sorted(byq)
    print(f"\n{pair} survivors by q: {[(q,byq[q]) for q in qs]}")
