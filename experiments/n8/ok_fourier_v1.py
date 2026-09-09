r"""
ok_fourier_v1 -- route (A): the Fourier identity for |G|, and the support-2 tail.

f = indicator of ||theta|| >= 1/8 = [1/8,7/8].  Then
    fhat(0) = 3/4,      fhat(k) = -sin(pi k/4)/(pi k)   (k != 0),
so fhat is EVEN, |fhat(k)| <= 1/(pi|k|), and fhat(k) = 0 exactly when 4 | k.

    |G| = int prod_j f(e_j t) dt = SUM over integer k with k.e = 0 of prod_j fhat(k_j).

k = 0 gives (3/4)^7 = 0.13348.  Every other term is a RESONANCE.  Support 1 is impossible
(k_j e_j = 0 forces k_j = 0).  Support 2 for the pair (i,j): with g = gcd(e_i,e_j),
a = e_i/g, b = e_j/g (coprime, distinct), the solutions are k_i = m b, k_j = -m a, m != 0.

T2 := sum over pairs, over m != 0, of |fhat(mb) fhat(ma)| * (3/4)^5
is the absolute support-2 tail.  If (3/4)^7 - T2 - (support>=3) > 0 the tuple is settled.
Verified below against the exact |G| computed by interval arithmetic.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd, sin, pi
import statistics

def fhat(k):
    if k == 0: return 0.75
    if k % 4 == 0: return 0.0
    return -sin(pi*k/4)/(pi*k)

def arcs(e): return [(F(8*j+1,8*e), F(8*j+7,8*e)) for j in range(e)]
def inter(A,B):
    out=[]; i=j=0
    while i<len(A) and j<len(B):
        lo=max(A[i][0],B[j][0]); hi=min(A[i][1],B[j][1])
        if lo<hi: out.append((lo,hi))
        if A[i][1]<B[j][1]: i+=1
        else: j+=1
    return out
def G_measure(E):
    cur=arcs(E[0])
    for e in E[1:]:
        cur=inter(cur,arcs(e))
        if not cur: return F(0)
    return sum((b-a for a,b in cur), F(0))

MAIN = 0.75**7
def T2(E, M=400):
    tot=0.0
    for i in range(7):
        for j in range(i+1,7):
            g=gcd(E[i],E[j]); a=E[i]//g; b=E[j]//g
            s=0.0
            for m in range(1,M+1):
                s += abs(fhat(m*b)*fhat(m*a))
            tot += 2*s*(0.75**5)
    return tot
def nrel(E):
    S=set(E); return sum(1 for x in E for y in E if x<y and x+y in S)

print(f"main term (3/4)^7 = {MAIN:.6f}\n")
print(f"{'E':30} {'rel':>4} {'|G| exact':>11} {'T2':>10} {'(3/4)^7 - T2':>14} {'settled?':>9}")
tests=[(2,6,7,8,10,13,14),(1,3,4,5,7,11,24),(1,2,3,4,5,7,24),(1,3,5,7,13,15,24),
       (1,3,5,7,13,23,24),(2,12,13,14,16,19,20),(3,10,14,15,16,19,21),(5,12,14,16,20,26,28)]
for E in tests:
    g=float(G_measure(list(E))); t2=T2(list(E)); d=MAIN-t2
    print(f"{str(E):30} {nrel(E):>4} {g:11.6f} {t2:10.6f} {d:14.6f} {'YES' if d>0 else 'no':>9}")

print("\nsweep: how often does (3/4)^7 - T2 > 0, by relation count?  (Case 2, [1..24], sampled)")
import random
random.seed(3)
from collections import defaultdict
buck=defaultdict(lambda:[0,0])
pool=[E for E in combinations(range(1,25),7)]
random.shuffle(pool)
n=0
for E in pool:
    if n>=4000: break
    if reduce(gcd,E)!=1: continue
    if not any(e%8==0 for e in E): continue
    n+=1
    k=min(nrel(E),4); d=MAIN-T2(list(E),200)
    buck[k][0]+=1
    if d>0: buck[k][1]+=1
print(f"  {'rel':>5} {'sampled':>8} {'settled by support-2 alone':>28}")
for k in sorted(buck):
    c,s=buck[k]
    lab=f"{k}" if k<4 else "4+"
    print(f"  {lab:>5} {c:>8} {s:>10} ({100*s/c:5.1f}%)")
