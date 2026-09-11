#!/usr/bin/env python3
"""Is K small where it MATTERS (low |G|) in larger boxes?"""
from fractions import Fraction as F
from functools import reduce
from math import gcd, floor
import random
exec(open('ok_k_vs_hardness_v1.py').read().split('rows=[]')[0].split('#!/usr/bin/env python3')[1].split('"""',2)[2])
random.seed(23)
for hi,N in ((40,1200),(90,700),(200,350)):
    rows=[]
    while len(rows)<N:
        E=tuple(sorted(random.sample(range(1,hi+1),7)))
        g=reduce(gcd,E); E=tuple(e//g for e in E)
        if len(set(E))!=7 or all(e%8 for e in E): continue
        K,M=KminG(E)
        if K is not None: rows.append((K,float(M),E))
    rows.sort(key=lambda r:r[1])
    q=max(1,len(rows)//10)
    hard=rows[:q]; easy=rows[-q:]
    print(f"[1..{hi}]  {len(rows)} Case-2 sampled")
    print(f"   hardest decile (|G| {hard[0][1]:.4f}-{hard[-1][1]:.4f}): max K = {max(r[0] for r in hard)}"
          f"   at {max(hard,key=lambda r:r[0])[2]}")
    print(f"   easiest decile (|G| {easy[0][1]:.4f}-{easy[-1][1]:.4f}): max K = {max(r[0] for r in easy)}"
          f"   at {max(easy,key=lambda r:r[0])[2]}")
    print(f"   overall max K = {max(r[0] for r in rows)}  at |G| = "
          f"{max(rows,key=lambda r:r[0])[1]:.4f}")
