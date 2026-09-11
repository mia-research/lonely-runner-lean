#!/usr/bin/env python3
"""The GECT collapse law applied to n=8, with the d|n restriction dropped.

GECT Verification Log §1: at t = a/m in lowest terms, k = |{v_i mod m}| independent of a
-- geometry and timing are one function of m.  §4: n gaps summing to 1 each >= 1/n forces
the exact n-grid.  §7.1: N(V,n) = sum over d|n with d dividing no v, of phi(d).

At n=8 the d|n form gives 4*[no e=0 mod 8] + 2*[no e=0 mod 4] + 1*[all e odd], positive
iff no speed is a multiple of 8 -- i.e. exactly Case 1.  It vanishes on Case 2, which is
where n=8 is open.  §1 says the parameter is m, not d|n.  So define, for arbitrary m,

  W(E,m) = #{ a in (Z/m)* : ||e_j a / m|| >= 1/8 for every j }      (exact Fractions)
  k(E,m) = |{ e_j mod m } u {0}|                                    (the collapse law's k)

W(E,m) > 0 is a WITNESS: t = a/m certifies LRC(8) for E.  Questions, in order:
  Q1  controls: does the d|n form reproduce Case 1, and does k(m)=m, m<=8 force a witness?
  Q2  does dropping d|n reach Case 2 -- is there an m with W > 0 for the extremum?
  Q3  is "W(E,m) > 0" a function of the completeness profile m -> k(E,m) alone?
"""
from fractions import Fraction as F
from math import gcd
from itertools import combinations
import sys

def nrm(x):
    x = x - int(x)
    if x < 0: x += 1
    return min(x, 1-x)
def W(E, m):
    return [a for a in range(1, m) if gcd(a, m) == 1
            and all(nrm(F(e*a, m)) >= F(1,8) for e in E)]
def kprof(E, m): return len({e % m for e in E} | {0})
def Nd(E):   # the §7.1 divisor form at n=8
    return sum(ph for d, ph in ((2,1),(4,2),(8,4)) if all(e % d for e in E))

T1=(1,2,3,4,5,6,7); T2=(1,2,3,4,5,7,12); T3=(1,4,5,6,7,11,13)
ES=(2,6,7,8,10,13,14)
NAMED=(("T1 tight",T1),("T2 tight",T2),("T3 tight",T3),("E* Case-2 extremum",ES))

print("="*78)
print("Q1 CONTROL A -- the d|n form N(V,8) vs Case 1 (no speed a multiple of 8)")
import random; random.seed(20260911)
bad=0; n=0
for _ in range(4000):
    E=tuple(sorted(random.sample(range(1,40),7)))
    if (Nd(E)>0) != all(e%8 for e in E): bad+=1
    n+=1
print(f"  {n} random 7-tuples, disagreements {bad}   {'PASS' if bad==0 else '*** FAIL ***'}")

print("\nQ1 CONTROL B -- completeness at m<=8 must force a witness (§4 gap-sum)")
bad=0; tested=0
for _ in range(4000):
    E=tuple(sorted(random.sample(range(1,40),7)))
    for m in range(2,9):
        if kprof(E,m)==m:
            tested+=1
            if not W(E,m): bad+=1
            break
print(f"  {tested} tuples complete at some m<=8, witness missing in {bad}"
      f"   {'PASS' if bad==0 else '*** FAIL ***'}")

print("\n" + "="*78)
print("Q2 -- drop d|n.  Smallest m with a witness t=a/m, for the four named tuples.")
print(f"  {'tuple':22s} {'N_d|n':>6} {'k(8)':>5}  {'first m with W>0':>18}   witnesses a")
for lab,E in NAMED:
    hit=None
    for m in range(2,400):
        w=W(E,m)
        if w: hit=(m,w); break
    s = f"m={hit[0]:<4d}" if hit else "none up to 400"
    print(f"  {lab:22s} {Nd(E):>6} {kprof(E,8):>5}  {s:>18}   {hit[1][:6] if hit else ''}")

print("\n" + "="*78)
print("Q3 -- is 'W(E,m)>0' a function of the completeness profile alone?")
print("  Search for E, E' with identical profile m->k(m) for all m<=M, but different")
print("  witness-set { m<=M : W>0 }.  One pair refutes.")
M=24
prof=lambda E: tuple(kprof(E,m) for m in range(2,M+1))
wset=lambda E: tuple(1 if W(E,m) else 0 for m in range(2,M+1))
tab={}
pool=list(range(1,17))
cnt=0
for E in combinations(pool,5):
    if gcd(*E)!=1: pass
    p=prof(E); tab.setdefault(p,{}).setdefault(wset(E),[]).append(E); cnt+=1
viol={p:d for p,d in tab.items() if len(d)>=2}
print(f"  {cnt} 5-subsets of [1..16]; {len(tab)} distinct profiles;"
      f" {len(viol)} profiles carrying >=2 witness-sets")
if viol:
    p=sorted(viol,key=lambda p:len(viol[p]))[0]; d=viol[p]
    ks=sorted(d); A=d[ks[0]][0]; B=d[ks[-1]][0]
    dm=[m for i,m in enumerate(range(2,M+1)) if ks[0][i]!=ks[-1][i]]
    print(f"  REFUTED. same profile, different witness sets:")
    print(f"    E  = {A}   W>0 at m in {[m for m in range(2,M+1) if W(A,m)][:8]}")
    print(f"    E' = {B}   W>0 at m in {[m for m in range(2,M+1) if W(B,m)][:8]}")
    print(f"    first m where they differ: {dm[:5]}")
else:
    print("  no counterexample in this box -- profile determines the witness set")

print("\n" + "="*78)
print("CORRECTION.  Control B tested the wrong statement (completeness is irrelevant).")
print("Correct: d | e fails, d not| e succeeds.  N*(V,8) = sum over d<=8 with d dividing")
print("no speed, of phi(d).  The d|n restriction of §7.1 is not needed; d<=n suffices.")
PHI={2:1,3:2,4:2,5:4,6:2,7:6,8:4}
def Nstar(E): return sum(p for d,p in PHI.items() if all(e%d for e in E))
def Nstar_d(E): return [d for d in PHI if all(e%d for e in E)]

print("\nCONTROL B' -- N*(E,8) > 0 must imply an actual witness at that d")
bad=0;fired=0
for _ in range(4000):
    E=tuple(sorted(random.sample(range(1,40),7)))
    for d in Nstar_d(E):
        fired+=1
        if not W(E,d): bad+=1
print(f"  {fired} (tuple,d) pairs with d dividing no speed; witness missing in {bad}"
      f"   {'PASS' if bad==0 else '*** FAIL ***'}")

print("\nCOVERAGE of Case 2 (some speed a multiple of 8), exhaustive over [1..18]")
tot=c2=cov_N=cov_Ns=0
uncov=[]
for E in combinations(range(1,19),7):
    if gcd(*E)!=1: continue
    tot+=1
    if all(e%8 for e in E): continue          # Case 1
    c2+=1
    if Nd(E)>0: cov_N+=1
    if Nstar(E)>0: cov_Ns+=1
    else: uncov.append(E)
print(f"  primitive 7-tuples in [1..18]: {tot};  Case 2 (has a multiple of 8): {c2}")
print(f"    closed by the d|n form  N(V,8)>0 : {cov_N} ({100*cov_N/c2:.2f}%)")
print(f"    closed by     d<=n form N*(V,8)>0: {cov_Ns} ({100*cov_Ns/c2:.2f}%)  <-- the gain")
print(f"    remaining uncovered: {len(uncov)}")
from collections import Counter
print(f"    E* among the uncovered: {ES in uncov}")
print(f"    first five uncovered: {uncov[:5]}")

print("\n" + "="*78)
print("CHARACTERISATION of the residual: uncovered <=> E hits every d in 2..8")
bad=0
for E in combinations(range(1,19),7):
    if gcd(*E)!=1 or all(e%8 for e in E): continue
    if (Nstar(E)==0) != all(any(e%d==0 for e in E) for d in range(2,9)): bad+=1
print(f"  disagreements over all 20349 Case-2 tuples: {bad}"
      f"   {'PASS -- exact characterisation' if bad==0 else '*** FAIL ***'}")
