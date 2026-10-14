# One-multiple family: D' (k nonzero integers, none divisible by 8) plus one reading x = 8c.
# Exact Fractions only; every loop bounded. Cells of D' in [0,1] (closed gaps between merged open zones;
# degenerate cells = touches). DispCell law: x survives cell [u,w] iff disp x u <= w.
import sys
from fractions import Fraction as F
from math import floor
from itertools import combinations
def zones(d):
    return [((F(8*j-1,8*d)),(F(8*j+1,8*d))) for j in range(0,d+1)]
def cells(D):
    Z=sorted(z for d in D for z in zones(d))
    out=[]; e=None
    for s,t in Z:
        if e is None: e=t; continue
        if s<e: e=max(e,t)
        else:
            out.append((e,s)); e=t
    return [(u,w) for (u,w) in out if u>=0 and w<=1]
def clear(d,t):
    f=d*t-floor(d*t); return F(1,8)<=f<=F(7,8)
def disp(x,a):
    if clear(x,a): return a
    j=floor(x*a+F(1,8)); return F(8*j+1,8*x)
def cascade(ds,limit=400):
    m=min(ds); t=F(1,8*m); n=0
    while n<limit:
        bl=[d for d in ds if not clear(d,t)]
        if not bl: return t,n
        d=max(bl,key=lambda d:F(8*floor(d*t+F(1,8))+1,8*d)); t=F(8*floor(d*t+F(1,8))+1,8*d); n+=1
    return None,n
def main(k,N,Cmax):
    stat={'pairs':0,'first_undisp':0,'first_disp_survives':0,'later_cell':0,'none_in_0_1':0,'cascade_mismatch':0,'cascade_unfinished':0}
    idx={}; first_len_ok=0; first_len_bad=0
    nonmult=[d for d in range(1,N+1) if d%8]
    for D in combinations(nonmult,k):
        C=cells(D)
        if not C: continue
        for c in range(1,Cmax+1):
            x=8*c; stat['pairs']+=1
            surv=None
            for i,(u,w) in enumerate(C):
                p=disp(x,u)
                if p<=w: surv=(i,p,u); break
            if surv is None: stat['none_in_0_1']+=1; print("NO SURVIVOR",D,c); continue
            i,p,u=surv
            if i==0 and p==u: stat['first_undisp']+=1
            elif i==0: stat['first_disp_survives']+=1
            else: stat['later_cell']+=1
            idx[i]=idx.get(i,0)+1
            # cascade check on the union, taking the first instant it lands
            t,n=cascade(list(D)+[x])
            if t is None: stat['cascade_unfinished']+=1
            elif t!=p:
                # the cascade lands at a lonely instant; law predicts p (first survivor in [0,1]); compare
                stat['cascade_mismatch']+=1
                if stat['cascade_mismatch']<=3: print("MISMATCH",D,c,"cascade",t,"law",p)
    print(f"k={k} N={N} Cmax={Cmax}",stat,"first-survivor cell index counts",dict(sorted(idx.items())),flush=True)
if __name__=="__main__":
    k,N,C=map(int,sys.argv[1:4]); main(k,N,C)
