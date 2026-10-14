#!/usr/bin/env python3
"""B n I_A CAN be empty -- min is 0.  Refine: is it empty only when Lemma 5.2-D holds?
If so the true statement is  "5.2-D fails  =>  B n I_A != empty",  and the slack to measure
is min |B n I_A| RESTRICTED to tuples where 5.2-D fails.
Exact integers and Fraction only; no float anywhere."""
import sys
from fractions import Fraction as F
from math import gcd
from itertools import combinations
sys.path.insert(0, "experiments/n8")
from escape_coverage_v1 import escape_ii
from escape_coverage_v2 import good_idx
from escape_direct_v1 import config
from bcap_slack_v1 import B_set
n = 8; CAP = 10**6

if __name__ == "__main__":
    Bb = int(sys.argv[1]) if len(sys.argv)>1 else 16
    st = {}
    for T in combinations(range(1,Bb+1),7):
        if gcd(*T)!=1: continue
        c = config(T)
        if c is None: continue
        arm,Gsp,L_G,Asp,L_A,p = c
        if L_G>CAP or n*L_A>4*CAP: continue
        Bn, seen = B_set(Gsp,L_G,Asp,L_A,p)
        IA = [b for b in range(n*L_A) if good_idx(b,Asp,L_A)]
        inter = sum(1 for b in IA if seen[b])
        e2 = escape_ii(T)
        d = st.setdefault(arm, {"tot":0,"empty":0,"empty_and_no_5_2_D":0,
                                "minD":None,"argD":None,"has8":0,"empty_has8":0})
        d["tot"] += 1
        has8 = any(v % n == 0 for v in T)
        d["has8"] += has8
        if inter == 0:
            d["empty"] += 1
            if not e2: d["empty_and_no_5_2_D"] += 1
            if has8: d["empty_has8"] += 1
        if not e2:                                    # 5.2-D FAILS: the case that matters
            if d["minD"] is None or inter < d["minD"]:
                d["minD"] = inter; d["argD"] = (T, n*L_A, Bn, len(IA))
    print(f"n=8, speeds <= {Bb}, gcd=1, hard case.  Exact.")
    for arm in ("10.1","11.1"):
        if arm not in st: continue
        d = st[arm]
        print(f"\n  THEOREM {arm}  ({d['tot']} tuples)")
        print(f"    tuples with B n I_A EMPTY                     : {d['empty']}")
        print(f"      of those, Lemma 5.2-D also fails (=residual): {d['empty_and_no_5_2_D']}")
        print(f"      of those, some speed divisible by 8         : {d['empty_has8']}")
        print(f"    tuples with some speed divisible by 8         : {d['has8']}")
        if d["argD"]:
            T,NLA,Bn,IAn = d["argD"]
            print(f"    RESTRICTED to 5.2-D failing:")
            print(f"      min |B n I_A| = {d['minD']}   at T = {list(T)}")
            print(f"      n L_A = {NLA}  |B| = {Bn}  |I_A| = {IAn}"
                  f"  density {F(d['minD'], NLA)}")
