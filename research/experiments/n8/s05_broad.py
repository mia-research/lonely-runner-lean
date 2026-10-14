"""S05: broad divisor-based search.  Classifies by |E_div| and by whether E_div=={8}
(the only case in which the task's B_div literally equals the honest fibre set)."""
from itertools import combinations
from math import gcd
from n8_fibre_core import L_of, split, safe, div_ok, witness_from_fibre

UNITS={1,3,5,7}
def unit_complete(En):
    R=set(e%8 for e in En); return UNITS<=R and len(R)==5
def divisors(n):
    d=[];i=1
    while i*i<=n:
        if n%i==0:
            d.append(i)
            if i!=n//i: d.append(n//i)
        i+=1
    return sorted(d)

def analyse(E):
    L=L_of(E); Ed,En=split(E)
    lo,hi=-(-L//8),(7*L)//8
    W=[(-(-2*L//7),(2*L)//5),(-(-3*L//5),(5*L)//7)]
    inw=lambda b: any(a<=b<z for a,z in W)
    s_hon=s_hon_w=0; ex=None; thm_fail=0
    for b in range(lo,hi+1):
        if not safe(En,b,L): continue
        if witness_from_fibre(E,b) is None: thm_fail+=1
        if div_ok(Ed,b,L):
            s_hon+=1
            if inw(b):
                s_hon_w+=1
                if ex is None: ex=b
    return L,Ed,En,s_hon,s_hon_w,ex,thm_fail

LS=set()
for L in range(8, 6001, 8):
    LS.add(L)
res={"tot":0,"nohon":0,"nowin":0}
fails_win=[]; fails_hon=[]; thm_bad=0; thm_bad_e8=0; tested_e8=0; nowin_e8=[]
for L in sorted(LS):
    divs=divisors(L)
    if not (8<=len(divs)<=20): continue
    if L>4000: continue
    for E in combinations(divs,7):
        if L_of(E)!=L: continue
        g=0
        for e in E: g=gcd(g,e)
        if g!=1: continue
        Ed,En=split(E)
        if not Ed or not unit_complete(En): continue
        Lx,Ed,En,s_hon,s_hon_w,ex,tf=analyse(E)
        res["tot"]+=1
        if tf: thm_bad+=1
        if Ed==[8]:
            tested_e8+=1
            if tf: thm_bad_e8+=1
            if s_hon_w==0: nowin_e8.append((E,L,s_hon))
        if s_hon==0: fails_hon.append((E,L))
        if s_hon_w==0: fails_win.append((E,L,s_hon,len(Ed)))
print("configs tested:", res["tot"])
print("  with NO safe fibre in the honest fibre set B_hon :", len(fails_hon))
print("  with NO safe fibre inside the two windows        :", len(fails_win))
print("  for which the ASSUMED THEOREM on B_lit fails     :", thm_bad)
print()
print("restricted to E_div == {8} exactly (B_lit == B_hon):")
print("  tested:", tested_e8, " assumed-theorem failures:", thm_bad_e8,
      " window failures:", len(nowin_e8))
for E,L,s in nowin_e8[:15]:
    print("     WINDOW FAIL, E_div={8}:", E, "L=",L, "safe fibres in B =", s)
print()
print("window failures by |E_div|:")
from collections import Counter
print("  ", Counter(k for *_ ,k in fails_win))
for E,L,s,k in fails_win[:10]:
    print("   ", E, "L=",L,"|E_div|=",k,"safe in B=",s)
