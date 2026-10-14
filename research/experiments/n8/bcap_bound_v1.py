#!/usr/bin/env python3
"""CONJECTURE (sharp, quantitative):  if some speed of T is divisible by n, then
       |B n I_A|  >=  L_A.
Both extremal cases at speeds <= 16 attain it exactly: 10.1 arm min 2 with L_A = 2;
11.1 arm min 4 with L_A = 4 -- density exactly 1/n in each.
Also test the contrapositive shape: B n I_A = empty  =>  no speed divisible by n.
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
    tot=viol=emptyv=0; worst=None; margins={}
    for T in combinations(range(1,Bb+1),7):
        if gcd(*T)!=1: continue
        c = config(T)
        if c is None: continue
        arm,Gsp,L_G,Asp,L_A,p = c
        if L_G>CAP or n*L_A>4*CAP: continue
        tot += 1
        Bn, seen = B_set(Gsp,L_G,Asp,L_A,p)
        IA = [b for b in range(n*L_A) if good_idx(b,Asp,L_A)]
        inter = sum(1 for b in IA if seen[b])
        has_n = any(v % n == 0 for v in T)
        if inter == 0 and has_n: emptyv += 1
        if has_n:
            if inter < L_A:
                viol += 1
                if worst is None: worst = (T, inter, L_A, n*L_A, arm)
            k = inter - L_A
            margins[k] = margins.get(k,0)+1
    print(f"n=8, speeds <= {Bb}, gcd=1, hard case, both arms.  Exact.  {tot} tuples.")
    print(f"  CLAIM A  'B n I_A empty => no speed divisible by 8'")
    print(f"     violations (empty AND a speed divisible by 8) : {emptyv}")
    print(f"  CLAIM B  'some speed divisible by 8 => |B n I_A| >= L_A'")
    print(f"     violations : {viol}" + (f"   worst {worst}" if worst else ""))
    print(f"  margin |B n I_A| - L_A, distribution over the divisible-by-8 tuples:")
    for k in sorted(margins)[:12]:
        print(f"     margin {k:>5} : {margins[k]:>6} tuples" + ("   <-- TIGHT" if k==0 else ""))
