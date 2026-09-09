r"""
ok_mobius_v1 -- exact Mobius decomposition of o over the partition lattice of {1,3,5,7}.

nu_rho = a_rho XOR mu_rho in (Z/2)^2.  "nu_rho = nu_sigma" is an EQUIVALENCE relation, so the
collision structure is a set partition and inclusion-exclusion runs over Pi_4 with
  mu(0hat, pi) = prod_blocks (-1)^{|B|-1} (|B|-1)!  =  1, -1, 2, 1, -6.

  o  =  1  -  sum_{6 pairs} p  +  2 sum_{4 triples} T  +  sum_{3 matchings} Q  -  6 F

p_{rs}=P(nu_r=nu_s), T=P(three equal), Q=P(two disjoint pairs each equal), F=P(all four equal).
Generic (independent uniform nu): p=1/4, T=1/16, Q=1/16, F=1/64  ->  o = 3/32.  Checked.

The identity is a hard self-test: if the cell arithmetic is wrong it will not hold.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations
import sys

MUV = (0, 1, 2, 3)
IDX = (0, 1, 2, 3)
PAIRS = list(combinations(IDX, 2))
TRIPLES = list(combinations(IDX, 3))
MATCHINGS = [((0,1),(2,3)), ((0,2),(1,3)), ((0,3),(1,2))]

def cells(e):
    bps = sorted({F(k, 4*ei) for ei in e for k in range(0, 4*ei)} | {F(1)})
    return [(bps[i], bps[i+1]) for i in range(len(bps)-1)]

def stats(e):
    p = {q: F(0) for q in PAIRS}
    T = {q: F(0) for q in TRIPLES}
    Q = [F(0)]*3
    FF = F(0); o = F(0)
    for lo, hi in cells(e):
        w = hi - lo
        nu = [(int(4*ei*lo) % 4) ^ m for ei, m in zip(e, MUV)]
        for q in PAIRS:
            if nu[q[0]] == nu[q[1]]: p[q] += w
        for q in TRIPLES:
            if nu[q[0]] == nu[q[1]] == nu[q[2]]: T[q] += w
        for k, ((a,b),(c,d)) in enumerate(MATCHINGS):
            if nu[a]==nu[b] and nu[c]==nu[d]: Q[k] += w
        if len(set(nu)) == 1: FF += w
        if len(set(nu)) == 4: o += w
    return o, p, T, Q, FF

def check(e):
    o, p, T, Q, FF = stats(e)
    rhs = 1 - sum(p.values()) + 2*sum(T.values()) + sum(Q) - 6*FF
    return o, rhs, p, T, Q, FF

if __name__ == "__main__":
    LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    tuples = []
    for e1 in range(1, LIM+1, 8):
        for e3 in range(3, LIM+1, 8):
            for e5 in range(5, LIM+1, 8):
                for e7 in range(7, LIM+1, 8):
                    e = (e1,e3,e5,e7)
                    if reduce(gcd, e) == 1: tuples.append(e)
    print(f"# {len(tuples)} primitive tuples, speeds <= {LIM}")
    bad = 0; rows = []
    minp = None; maxT = None; maxQ = None; maxF = None
    for e in tuples:
        o, rhs, p, T, Q, FF = check(e)
        if o != rhs: bad += 1
        rows.append((o, e, p, T, Q, FF))
        mp = min(p.values())
        if minp is None or mp < minp[0]: minp = (mp, e, [k for k,v in p.items() if v==mp])
        mT = max(T.values())
        if maxT is None or mT > maxT[0]: maxT = (mT, e)
        mQ = max(Q)
        if maxQ is None or mQ > maxQ[0]: maxQ = (mQ, e)
        if maxF is None or FF > maxF[0]: maxF = (FF, e)
    print(f"MOBIUS IDENTITY o == 1 - sum p + 2 sum T + sum Q - 6F : "
          f"{len(tuples)-bad}/{len(tuples)} exact  ({bad} failures)")
    print(f"\nmin over ALL tuples of a single pair term p:  {minp[0]} = {float(minp[0]):.6f}"
          f"   at e={minp[1]}, pairs {minp[2]}   (generic 1/4 = 0.25)")
    print(f"max triple term T   : {maxT[0]} = {float(maxT[0]):.6f} at {maxT[1]}  (generic 1/16)")
    print(f"max matching term Q : {maxQ[0]} = {float(maxQ[0]):.6f} at {maxQ[1]}  (generic 1/16)")
    print(f"max all-four term F : {maxF[0]} = {float(maxF[0]):.6f} at {maxF[1]}  (generic 1/64)")
    print(f"\nIs p >= 1/4 for every pair of every tuple? {minp[0] >= F(1,4)}")
    rows.sort(key=lambda r: -r[0])
    print(f"\n{'e':20} {'o':>10} {'sum p':>10} {'2 sum T':>10} {'sum Q':>10} {'6F':>9}")
    for o, e, p, T, Q, FF in rows[:8]:
        print(f"{str(e):20} {float(o):10.6f} {float(sum(p.values())):10.6f} "
              f"{float(2*sum(T.values())):10.6f} {float(sum(Q)):10.6f} {float(6*FF):9.6f}")
    print(f"{'GENERIC':20} {0.09375:10.6f} {1.5:10.6f} {0.5:10.6f} {0.1875:10.6f} {0.09375:9.6f}")
