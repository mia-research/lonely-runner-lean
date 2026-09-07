"""S12: full profile of a given E: safe fibres in B, in each window, uncovered-set census,
and an independent x_0 check where feasible."""
import sys
from fractions import Fraction as F
from collections import Counter
from n8_fibre_core import L_of, split, safe, div_ok, blocked_non, witness_from_fibre, x0_bruteforce

def profile(E, do_x0=False):
    L=L_of(E); Ed,En=split(E)
    lo,hi=-(-L//8),(7*L)//8
    W=[("[2/7,2/5)",-(-2*L//7),(2*L)//5),("[3/5,5/7)",-(-3*L//5),(5*L)//7)]
    print(f"E={E}  L={L}  N={8*L}  E_div={Ed}  E_non={En}  R_non={sorted(set(e%8 for e in En))}")
    tw={}
    for e in En: tw.setdefault(e%8,[]).append(e)
    print("  classes:", {r:v for r,v in sorted(tw.items())}, " doubled:", [r for r,v in tw.items() if len(v)>1])
    tot=safeB=0; unc=Counter()
    for b in range(lo,hi+1):
        if not div_ok(Ed,b,L): continue
        tot+=1
        if safe(En,b,L): safeB+=1
    print(f"  |B_hon| = {tot}   safe = {safeB}")
    for wn,a,z in W:
        n=ns=0; ex=None; uc=Counter()
        for b in range(a,z):
            if not div_ok(Ed,b,L): continue
            n+=1
            u=tuple(sorted(set(range(8))-blocked_non(En,b,L)))
            uc[u]+=1
            if u:
                ns+=1
                if ex is None: ex=b
        print(f"  window {wn}: |B_hon n W|={n}  safe={ns}  first safe b={ex}")
        print(f"     uncovered-set census (top 6): {uc.most_common(6)}")
    if do_x0:
        print("  x_0(E) by brute force over all k in 1..N-1 :", x0_bruteforce(E))

for arg in sys.argv[1:]:
    E=tuple(int(t) for t in arg.split(","))
    profile(E, do_x0=(L_of(E)<=200000))
    print()
