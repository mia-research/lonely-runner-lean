#!/usr/bin/env python3
"""PRE-REGISTERED, CRT_STAR_STRUCTURE_v1 §7.  Does the Sigma-alpha margin decompose into
per-prime contributions under the star structure?
CONTROL (committed in advance): the three tight instances must give margin exactly 0."""
from fractions import Fraction as F
from itertools import combinations
from math import lcm, gcd
from functools import reduce

def ivs(E):
    out=[]
    for e in E:
        for k in range(0,e+1):
            lo,hi=max(F(8*k-1,8*e),F(0)),min(F(8*k+1,8*e),F(1))
            if lo<hi: out.append((lo,hi))
    return out
def merge(iv):
    iv=sorted(iv); m=[]
    for lo,hi in iv:
        if m and lo<=m[-1][1]: m[-1][1]=max(m[-1][1],hi)
        else: m.append([lo,hi])
    return m
def comp(m):
    g,cur=[],F(0)
    for lo,hi in m:
        if cur<lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<1: g.append((cur,F(1)))
    return g
def GH(H): return comp(merge(ivs(H)))
def meas(iv): return sum(b-a for a,b in iv)
def inter(A,B):
    out=[]
    for a,b in A:
        for c,d in B:
            lo,hi=max(a,c),min(b,d)
            if lo<hi: out.append((lo,hi))
    return out
def alpha(x,G):
    A=merge(ivs([x]))                      # blocked set of speed x
    return meas(inter(G,A))/meas(G)
def best_split(E):
    bst=None
    for k in range(1,len(E)-1):            # |O| >= 2
        for H in combinations(E,k):
            O=[e for e in E if e not in H]
            G=GH(list(H))
            if meas(G)==0: continue
            s=sum(alpha(x,G) for x in O)
            if bst is None or s<bst[0]: bst=(s,H,tuple(O))
    return bst

T=[(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]
print("CONTROL -- tight instances must give min_O Sigma alpha exactly 1 (margin 0)")
for E in T:
    s,H,O=best_split(E)
    print(f"  {E}  min Sigma alpha = {s}  {'== 1 PASS' if s==1 else '*** FAIL ***'}   H={H} O={O}")

E=(2,6,7,8,10,13,14)
s,H,O=best_split(E)
print(f"\nE* = {E}   min Sigma alpha = {s} = {float(s):.6f}   H={H}  O={O}")
G=GH(list(H)); MG=meas(G)
print(f"  |G_H| = {MG}   margin = 1 - Sigma alpha = {1-s}")

# star decomposition of S over CRT(Z/8L)
def psi(t):
    t=t-int(t)
    if t<0: t+=1
    if t<=F(1,8): return 3*t/4
    if t<=F(7,8): return F(1,8)-t/4
    return 3*(t-1)/4
S=lambda x: sum(psi(F(x)*v)-psi(F(x)*u) for u,v in G)
L=reduce(lcm,H); M=8*L
def factor(m):
    f,d=[],2
    while d*d<=m:
        if m%d==0:
            q=1
            while m%d==0: m//=d; q*=d
            f.append(q)
        d+=1
    if m>1: f.append(m)
    return f
mods=factor(M)
print(f"  M = 8*lcm(H) = {M} = {mods}")
tab={}
for x in range(M): tab[tuple(x%m for m in mods)]=S(x)
def cmean(U):
    acc={}
    for key,v in tab.items():
        sub=tuple(key[j] for j in U); acc[sub]=acc.get(sub,F(0))+v
    cnt=M
    for j in U: cnt//=mods[j]
    return {k:v/cnt for k,v in acc.items()}
CM={U:cmean(U) for r in range(len(mods)+1) for U in combinations(range(len(mods)),r)}
def part(x,T_):
    return sum((-1)**(len(T_)-len(U))*CM[U][tuple(x%mods[j] for j in U)]
               for r in range(len(T_)+1) for U in combinations(T_,r))
print(f"\n  {'x':>4} {'S_x':>14} {'S_x/x':>12} | star components by index set")
for x in O:
    ps={T_:part(x,T_) for r in range(1,len(mods)+1) for T_ in combinations(range(len(mods)),r)}
    nz={('x'.join(str(mods[j]) for j in T_)):v for T_,v in ps.items() if v!=0}
    print(f"  {x:>4} {str(S(x)):>14} {float(S(x))/x:>12.6f} | " +
          "  ".join(f"{k}:{float(v):+.5f}" for k,v in nz.items()))
lhs=sum(F(S(x),x) for x in O)
print(f"\n  criterion (SIGMA_ALPHA §5):  S_x/x + S_y/y  <  |G_H|/2")
print(f"    LHS = {lhs} = {float(lhs):.6f}   RHS = {MG/2} = {float(MG/2):.6f}"
      f"   -> {'HOLDS' if lhs<MG/2 else 'FAILS'}, margin {MG/2-lhs}")
print("\n  PER-PRIME SPLIT of the LHS (does any single prime carry the deficit?)")
for r in range(1,len(mods)+1):
    for T_ in combinations(range(len(mods)),r):
        v=sum(F(1,x)*part(x,T_) for x in O)
        if v!=0:
            lab='x'.join(str(mods[j]) for j in T_)
            print(f"    {lab:>10}: {v}  = {float(v):+.6f}")
