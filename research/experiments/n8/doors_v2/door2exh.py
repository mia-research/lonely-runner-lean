from itertools import combinations
from math import gcd
from fractions import Fraction as F
def inway(d,P,Q):
    r=(d*P)%Q; return 8*min(r,Q-r)<Q
def nextop(d,P,Q):
    num=8*d*P-Q; den=8*Q; k=-((-num)//den); g=gcd(8*k+1,8*d); return ((8*k+1)//g,(8*d)//g)
def move(ds,P,Q):
    bP,bQ=P,Q
    for d in ds:
        if inway(d,P,Q):
            nP,nQ=nextop(d,P,Q)
            if nP*bQ>bP*nQ: bP,bQ=nP,nQ
    return bP,bQ
def cascade(ds,cap=4000):
    m=min(ds); P,Q=1,8*m; g=gcd(P,Q); P,Q=P//g,Q//g; mv=0
    while mv<cap:
        P2,Q2=move(ds,P,Q)
        if (P2,Q2)==(P,Q): return mv,P,Q
        P,Q=P2,Q2; mv+=1
    return None,P,Q

for hi in (18,20,22):
    mx=F(0); arg=None; mxmv=0; argm=None; n=0; noarr=0
    for s in combinations(range(1,hi+1),7):
        g=0
        for x in s: g=gcd(g,x)
        if g!=1: continue
        n+=1
        mv,P,Q=cascade(list(s))
        if mv is None: noarr+=1; print("  NO ARRIVAL:",s); continue
        tau=F(min(s)*P,Q)
        if tau>mx: mx,arg=tau,s
        if mv>mxmv: mxmv,argm=mv,s
    print(f"EXHAUSTIVE [1,{hi}]: {n} primitive 7-sets, no-arrival={noarr}")
    print(f"   max tau (arrival in nearest runner's laps) = {mx} = {float(mx):.5f}  at {arg}")
    print(f"   max moves = {mxmv} at {argm}")
