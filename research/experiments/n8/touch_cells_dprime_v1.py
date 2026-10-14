# Touch cells (zero-width cells) of D' (k non-multiples of 8 in {1..N}): opener (d,j) at u=(8j+1)/(8d), closer (d',j') with entry (8j'-1)/(8d')=u.
# Exact Fractions, deterministic, every D' listed. Cells are the closed gaps between merged open zones in [0,1].
import sys
from fractions import Fraction as F
from itertools import combinations
from one_multiple_cells_v1 import cells
def roles(D,u):
    ops=[];cls=[]
    for d in D:
        v=8*d*u-1
        if v.denominator==1 and v>=0 and v%8==0: ops.append((d,int(v)//8))
        v2=8*d*u+1
        if v2.denominator==1 and v2>=0 and v2%8==0: cls.append((d,int(v2)//8))
    return ops,cls
def main(k,N):
    nonmult=[d for d in range(1,N+1) if d%8]
    sets=0; first_touch=0; touch_idx={}; ntouch={}; summod={}; multi_open=0; multi_close=0; notouchpair=0
    firstR={}
    for D in combinations(nonmult,k):
        C=cells(D)
        if not C: continue
        sets+=1
        T=[i for i,(u,w) in enumerate(C) if u==w]
        ntouch[len(T)]=ntouch.get(len(T),0)+1
        for i in T[:6]: touch_idx[i]=touch_idx.get(i,0)+1
        if T and T[0]==0: first_touch+=1
        for i in T:
            u=C[i][0]; ops,cls=roles(D,u)
            if len(ops)>1: multi_open+=1
            if len(cls)>1: multi_close+=1
            if not ops or not cls: notouchpair+=1; continue
            for (d,j) in ops:
                for (e,jj) in cls:
                    s=(d+e)%8; summod[s]=summod.get(s,0)+1
    print(f"k={k} N={N}: sets={sets}; sets whose first cell is a touch={first_touch}; number of touches per set {dict(sorted(ntouch.items()))}; sets with a touch at cell index i {dict(sorted(touch_idx.items()))}; touches with several openers={multi_open}, several closers={multi_close}, without an opener or closer found={notouchpair}; (d+e) mod 8 over opener/closer pairs {dict(sorted(summod.items()))}",flush=True)
for a in [(4,20),(5,18),(6,16),(4,40)]: main(*a)
