"""Making the last step finite.

Band 2 is reachable iff some profile has NO clear R in [1,7] u [9,15], i.e. the six non-minimal
combs COVER that region.  Write u_i = 1/s_i.  Comb i's bad intervals are

        [ (8k-1) u_i ,  (8k+1) u_i ]        k = 0, 1, 2, ...

A union of intervals covers [a,b] iff they CHAIN: ordered by left endpoint, each next interval
starts at or before the previous one ends, the first contains a, the last contains b.  Every one of
those conditions is LINEAR in u:

        (8k_j - 1) u_{i_j}  <=  (8k_{j-1} + 1) u_{i_{j-1}}

So "band 2 is reachable" is a finite union of LP feasibility problems, one per chain.  This script
builds and solves them.

Constraints carried throughout:
  u_i = 1/s_i with 1 = s_1 < s_2 < ... < s_7 = S,  so  1 > u_2 > u_3 > ... > u_7 = 1/S
  S > 7 (else clear at R = 1, Corollary 6.21), so u_7 < 1/7
VALIDATION FIRST: the same machinery must reproduce a KNOWN covering -- the region [1,7] under a
profile whose clear set we can check directly."""
import sys; sys.path.insert(0,'experiments/n8')
from itertools import product
import numpy as np
from scipy.optimize import linprog

NC = 6              # combs s_2..s_7, indices 0..5 here
EPS = 1e-9

def chain_lp(chain, a, b):
    """chain = [(i,k), ...] in order.  Variables u_0..u_5 (= 1/s_2 .. 1/s_7).
    Returns (feasible, u) for covering [a,b]."""
    A, rhs = [], []
    def row(): return [0.0]*NC
    # 1) first interval contains a:  (8k-1)u <= a  and  a <= (8k+1)u
    i0,k0 = chain[0]
    r=row(); r[i0]= (8*k0-1); A.append(r); rhs.append(a)                    # (8k-1)u <= a
    r=row(); r[i0]= -(8*k0+1); A.append(r); rhs.append(-a)                  # -(8k+1)u <= -a
    # 2) chaining
    for (ip,kp),(i,k) in zip(chain, chain[1:]):
        r=row(); r[i]+= (8*k-1); r[ip]-= (8*kp+1); A.append(r); rhs.append(0.0)
    # 3) last interval contains b
    il,kl = chain[-1]
    r=row(); r[il]= -(8*kl+1); A.append(r); rhs.append(-b)
    # 4) ordering u_0 > u_1 > ... > u_5, and bounds
    for j in range(NC-1):
        r=row(); r[j+1]-=1.0; r[j]+=0.0; r[j]= -1.0; r[j+1]= 1.0
        A.append(r); rhs.append(-EPS)                                        # u_{j+1} - u_j <= -eps
    bounds=[(1/8+EPS, 1-EPS)]*NC
    bounds[NC-1]=(1/8+EPS, 1/7-EPS)                                          # S > 7
    res=linprog(c=[0.0]*NC, A_ub=np.array(A), b_ub=np.array(rhs), bounds=bounds, method="highs")
    return res.status==0, (res.x if res.status==0 else None)

def enumerate_chains(a, b, KMAX, maxlen):
    """all chains of (comb, k) pairs, non-decreasing in k per comb, length <= maxlen"""
    out=[]
    def rec(cur):
        if len(cur)>maxlen: return
        if cur:
            ok,u = chain_lp(cur,a,b)
            if ok: out.append((list(cur),u)); return       # found a covering chain
        for i in range(NC):
            for k in range(0,KMAX+1):
                if cur and (i,k)==cur[-1]: continue
                cur.append((i,k)); rec(cur); cur.pop()
    rec([])
    return out

print("  VALIDATION: can six combs cover [1,7]?  (chains up to length 4, k <= 3)")
res=enumerate_chains(1.0, 7.0, KMAX=3, maxlen=4)
print(f"    feasible chains found: {len(res)}")
if res:
    ch,u=res[0]
    s=[1/x for x in u]
    print(f"    example chain {ch}")
    print(f"    u = {[round(x,5) for x in u]}")
    print(f"    s = {[round(x,4) for x in s]}   S = {round(s[-1],4)}")
    # independent check: is [1,7] really covered by these combs?
    import math
    def bad(sv,R):
        m=(sv*R)%8.0
        return m<1.0 or m>7.0
    grid=np.arange(1.0,7.0001,0.0005)
    unc=[R for R in grid if not any(bad(sv,R) for sv in s)]
    print(f"    independent check: clear points of s_2..s_7 in [1,7] at 5e-4 resolution: {len(unc)}")
    print(f"      (0 would mean the covering is real; >0 means the LP chain is not a true covering)")
