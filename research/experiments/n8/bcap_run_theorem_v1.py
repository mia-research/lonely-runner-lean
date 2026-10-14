#!/usr/bin/env python3
"""A PROVED sufficient condition for  B n I_A != empty.

THEOREM (run-length).  Let R := the largest number of CONSECUTIVE elements (cyclically in
Z/(n L_A)) lying in the complement of I_A.  Each alpha_0 in I_G contributes to B the
consecutive block of beta-values floor(start/L_G) .. floor((start + W - 1)/L_G), where
W = L_A p; that block has at least floor((W-1)/L_G) + 1 distinct consecutive values.  So if

        floor((L_A p - 1)/L_G)  >=  R          then   B n I_A != empty,

because a run of R+1 consecutive values cannot lie wholly in the complement.  (I_G is
non-empty by hypothesis, so at least one block exists.)                            [PROVED]

For the Theorem 10.1 arm the A-speed set is the single speed q, so I_A = {beta : beta mod n
in [1, n-2]} and its complement is {beta : beta mod n in {0, n-1}} -- runs of length exactly
2 (the pair n-1, 0 wrapping).  Hence R = 2 there, and the condition reads L_A p >= 2 L_G + 1,
i.e. V >= 2 L_G + 1 since V = p q = p L_A.

Exact integers only; no float anywhere.
"""
import sys
from math import gcd
from fractions import Fraction as F
from itertools import combinations
sys.path.insert(0, "experiments/n8")
from escape_coverage_v1 import escape_ii
from escape_coverage_v2 import good_idx
from escape_direct_v1 import config
from bcap_slack_v1 import B_set
n = 8; CAP = 10**6

def max_complement_run(IAset, NLA):
    """Largest cyclic run of consecutive indices NOT in I_A."""
    best = cur = 0
    for b in range(2 * NLA):                     # two laps handles the wrap
        if (b % NLA) in IAset: cur = 0
        else:
            cur += 1
            if cur > best: best = cur
    return min(best, NLA)

if __name__ == "__main__":
    Bb = int(sys.argv[1]) if len(sys.argv)>1 else 16
    st = {}
    for T in combinations(range(1,Bb+1),7):
        if gcd(*T)!=1: continue
        c = config(T)
        if c is None: continue
        arm,Gsp,L_G,Asp,L_A,p = c
        if L_G>CAP or n*L_A>4*CAP: continue
        d = st.setdefault(arm, {"tot":0,"hasn":0,"thm":0,"thm_or_ii":0,"viol":0,
                                "R":{}, "resid":0})
        d["tot"] += 1
        has_n = any(v % n == 0 for v in T)
        d["hasn"] += has_n
        Bn, seen = B_set(Gsp,L_G,Asp,L_A,p)
        IAset = {b for b in range(n*L_A) if good_idx(b,Asp,L_A)}
        R = max_complement_run(IAset, n*L_A)
        d["R"][R] = d["R"].get(R,0)+1
        thm = ((L_A*p - 1)//L_G) >= R
        inter = any(seen[b] for b in IAset)
        if thm and not inter: d["viol"] += 1          # theorem must never over-claim
        d["thm"] += thm
        if thm or escape_ii(T): d["thm_or_ii"] += 1
        else: d["resid"] += 1
    print(f"n=8, speeds <= {Bb}, gcd=1, hard case.  Exact.")
    for arm in ("10.1","11.1"):
        if arm not in st: continue
        d = st[arm]; t = d["tot"]
        print(f"\n  THEOREM {arm}  arm {t}   (speed divisible by 8: {d['hasn']})")
        print(f"    max-complement-run R values : "
              + "  ".join(f"R={k}:{v}" for k,v in sorted(d['R'].items())[:8]))
        print(f"    run-theorem fires           : {d['thm']}/{t} = {F(d['thm'],t)}")
        print(f"    theorem OVER-CLAIMS (fires but intersection empty) : {d['viol']}")
        print(f"    covered by (run-theorem or Lemma 5.2-D)            : "
              f"{d['thm_or_ii']}/{t} = {F(d['thm_or_ii'],t)}")
        print(f"    residual                                           : {d['resid']}")
