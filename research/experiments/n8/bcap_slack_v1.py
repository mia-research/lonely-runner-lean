#!/usr/bin/env python3
"""How much slack does  B n I_A != empty  actually have?

The project's own recorded lesson: when tempted to say "A is not the obstruction, here are
witnesses", compute A's EXTREMAL VALUE instead.  So: min |B n I_A| over hard-case tuples.
If the minimum is 1, the statement is tight and a density argument cannot reach it.
If it grows with n L_A, a counting proof has room.

Exact integers and Fraction only.  No float anywhere, reporting included.
"""
import sys
from fractions import Fraction as F
from math import gcd, lcm
from itertools import combinations
sys.path.insert(0, "experiments/n8")
from escape_coverage_v1 import largest_prime
from escape_coverage_v2 import good_idx
from escape_direct_v1 import config
n = 8; CAP = 10**6

def B_set(Gsp, L_G, Asp, L_A, p):
    NLG, NLA, N0, W = n*L_G, n*L_A, n*L_G*L_A, L_A*p
    seen = bytearray(NLA); cnt = 0
    for m in range(NLG):
        if not good_idx(m, Gsp, L_G): continue
        start = (m*W) % N0
        b0, b1 = start//L_G, (start+W-1)//L_G
        span = b1-b0
        rng = range(NLA) if span >= NLA-1 else ((b0+k) % NLA for k in range(span+1))
        for b in rng:
            if not seen[b]: seen[b]=1; cnt+=1
            if cnt==NLA: return cnt, seen
    return cnt, seen

if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv)>1 else 16
    worst = {}
    for T in combinations(range(1,B+1),7):
        if gcd(*T)!=1: continue
        c = config(T)
        if c is None: continue
        arm,Gsp,L_G,Asp,L_A,p = c
        if L_G>CAP or n*L_A>4*CAP: continue
        Bn, seen = B_set(Gsp,L_G,Asp,L_A,p)
        IA = [b for b in range(n*L_A) if good_idx(b,Asp,L_A)]
        inter = sum(1 for b in IA if seen[b])
        d = worst.setdefault(arm, {"min":None,"arg":None,"tot":0,"one":0,
                                   "minratio":None,"ratioarg":None})
        d["tot"] += 1
        if inter == 1: d["one"] += 1
        if d["min"] is None or inter < d["min"]:
            d["min"] = inter; d["arg"] = (T, n*L_A, Bn, len(IA))
        r = F(inter, n*L_A)
        if d["minratio"] is None or r < d["minratio"]:
            d["minratio"] = r; d["ratioarg"] = (T, inter, n*L_A)
    print(f"n=8, speeds <= {B}, gcd=1, hard case.  Exact; ratios as Fraction.")
    for arm in ("10.1","11.1"):
        if arm not in worst: continue
        d = worst[arm]
        T,NLA,Bn,IAn = d["arg"]
        print(f"\n  THEOREM {arm}  ({d['tot']} tuples)")
        print(f"    min |B n I_A| = {d['min']}   at T = {list(T)}")
        print(f"       n L_A = {NLA}   |B| = {Bn}   |I_A| = {IAn}"
              f"   pigeonhole |B|+|I_A| > n L_A ? {Bn+IAn > NLA}")
        print(f"    tuples with |B n I_A| == 1 : {d['one']}")
        T2,i2,N2 = d["ratioarg"]
        print(f"    min density |B n I_A|/(n L_A) = {d['minratio']}"
              f"  ({i2}/{N2})  at T = {list(T2)}")
