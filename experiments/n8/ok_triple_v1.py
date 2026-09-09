r"""
ok_triple_v1 -- does the 4-body bound o <= 1/3 follow from a 3-body relaxation?

nu injective on 4 indices ==> nu injective on every 3-subset.  So
      o <= o3(rho,sigma,tau) := P(nu_rho, nu_sigma, nu_tau pairwise distinct)
for each of the 4 triples, hence  o <= min_triples o3.   Generic o3 = 4*3*2/64 = 3/8.

Also tested: the 2-body relaxation o <= min_pairs (1 - p),  generic 3/4.
Question: is min_triples o3 <= 1/3 outside the two known exceptions?
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations
import sys

MUV = (0,1,2,3)
TRIPLES = list(combinations(range(4), 3))

def cells(e):
    bps = sorted({F(k, 4*ei) for ei in e for k in range(0, 4*ei)} | {F(1)})
    return [(bps[i], bps[i+1]) for i in range(len(bps)-1)]

def measures(e):
    o = F(0); o3 = {t: F(0) for t in TRIPLES}; p = {q: F(0) for q in combinations(range(4),2)}
    for lo, hi in cells(e):
        w = hi - lo
        nu = [(int(4*ei*lo) % 4) ^ m for ei, m in zip(e, MUV)]
        if len(set(nu)) == 4: o += w
        for t in TRIPLES:
            if len({nu[i] for i in t}) == 3: o3[t] += w
        for q in p:
            if nu[q[0]] == nu[q[1]]: p[q] += w
    return o, o3, p

if __name__ == "__main__":
    LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    tup = []
    for e1 in range(1, LIM+1, 8):
        for e3 in range(3, LIM+1, 8):
            for e5 in range(5, LIM+1, 8):
                for e7 in range(7, LIM+1, 8):
                    e = (e1,e3,e5,e7)
                    if reduce(gcd, e) == 1: tup.append(e)
    rows = []
    for e in tup:
        o, o3, p = measures(e)
        rows.append((o, min(o3.values()), max(p.values()), e, o3))
    EXC = {(1,3,5,7), (1,11,5,7)}
    ok = [r for r in rows if r[3] not in EXC]
    print(f"# {len(tup)} primitive tuples, speeds <= {LIM};  {len(ok)} non-exceptional")
    print(f"\nDoes the 3-body relaxation suffice?  need min_triples o3 <= 1/3")
    viol = [r for r in ok if r[1] > F(1,3)]
    print(f"  non-exceptional tuples with min_triples o3 > 1/3 : {len(viol)} / {len(ok)}")
    rows.sort(key=lambda r: -r[1])
    print(f"\n  largest min_triples o3 overall:")
    for o, m3, mp, e, o3 in rows[:8]:
        print(f"    {str(e):18} o={float(o):8.6f}  min_triple_o3={str(m3):>12} = {float(m3):8.6f}"
              f"   {'EXC' if e in EXC else ''}")
    print(f"\n  generic o3 = 3/8 = 0.375;  overall max min_triple o3 = {float(rows[0][1]):.6f}")
    # how often is the 3-body relaxation already enough?
    good = sum(1 for r in ok if r[1] <= F(1,3))
    print(f"  3-body relaxation ALONE proves o<=1/3 for {good}/{len(ok)} non-exceptional tuples "
          f"({100*good/len(ok):.1f}%)")
    # 2-body
    good2 = sum(1 for r in ok if 1 - r[2] <= F(1,3))
    print(f"  2-body relaxation alone proves it for {good2}/{len(ok)} ({100*good2/len(ok):.1f}%)")
    # the residual set: which tuples defeat the 3-body relaxation?
    if viol:
        viol.sort(key=lambda r: -r[1])
        print(f"\n  residual (3-body insufficient), worst 10 by min_triple o3:")
        for o, m3, mp, e, o3 in viol[:10]:
            print(f"    {str(e):18} o={float(o):8.6f}  min3={float(m3):8.6f}")
