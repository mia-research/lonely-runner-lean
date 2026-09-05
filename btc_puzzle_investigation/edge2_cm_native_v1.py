#!/usr/bin/env python3
"""
Edge 2, redone in the CURVE-NATIVE (Eisenstein/ℤ[ω]) basis instead of raw bits.
For each of the 100k points [d]G=(X,Y) on E:y^2=x^3+7 / F_p, compute the CM-native
'angular' features:
  chi6(X)=X^((p-1)/6)  (sextic sector / twist lens, mu_6 angle),
  chi3(X), chi2(X)=Legendre, chi6(Y),
and look for RESIDUE / RESONANCE / INTERFERENCE structure vs the scalar & decomposition:
  - marginals (calibration: should be uniform over mu_6),
  - null-subtracted MI vs d mod {3,6}, n/k/D mod 6,
  - a RESONANCE SCAN: MI(chi6(X); d mod m) over many m (spectral peaks),
  - the (chi6(X),chi6(Y)) INTERFERENCE table (curve-equation constraints show here).
Exact integer characters; MI null-subtracted (shuffle removes finite-sample bias).
"""
import csv, math, random
from collections import Counter
p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
e6=(p-1)//6; e3=(p-1)//3; e2=(p-1)//2
def prim6():
    for g in range(2,200):
        z=pow(g,e6,p)
        if pow(z,6,p)==1 and all(pow(z,t,p)!=1 for t in (1,2,3)): return z
z6=prim6(); six={pow(z6,j,p):j for j in range(6)}
z3=pow(z6,2,p); three={pow(z3,j,p):j for j in range(3)}
def chi6(x): return six.get(pow(x%p,e6,p))
def chi3(x): return three.get(pow(x%p,e3,p))
def chi2(x):
    r=pow(x%p,e2,p); return 0 if r==1 else 1

d=[];X=[];Y=[];n=[];k=[];D=[]
with open('constructed_keys_1to160_100k_exact.csv') as f:
    for row in csv.DictReader(f):
        d.append(int(row['d']));X.append(int(row['X'],16));Y.append(int(row['Y'],16))
        n.append(int(row['n']));k.append(int(row['k']));D.append(int(row['D']))
N=len(d); print(f"loaded {N} points; computing CM-native characters...")
c6X=[chi6(x) for x in X]; c3X=[chi3(x) for x in X]; c2X=[chi2(x) for x in X]
c6Y=[chi6(y) for y in Y]

def MI(A,B):
    ca=Counter(A);cb=Counter(B);cab=Counter(zip(A,B));tot=len(A);mi=0.0
    for (x,y),c in cab.items():
        pxy=c/tot;mi+=pxy*math.log2(pxy/((ca[x]/tot)*(cb[y]/tot)))
    return mi
random.seed(9)
def realMI(A,Bv,reps=15):
    obs=MI(A,Bv);B2=Bv[:];nl=[]
    for _ in range(reps):
        random.shuffle(B2);nl.append(MI(A,B2))
    mu=sum(nl)/reps;sd=(sum((x-mu)**2 for x in nl)/reps)**.5 or 1e-12
    return obs-mu,(obs-mu)/sd

print("\n1) MARGINALS (calibration; uniform => sound):")
for nm,cc,k_ in [("chi6(X)",c6X,6),("chi3(X)",c3X,3),("chi2(X)",c2X,2),("chi6(Y)",c6Y,6)]:
    ct=Counter(cc); print(f"   {nm}: {[ct[j] for j in range(k_)]}  (unif={N//k_})")

print("\n2) null-subtracted MI: CM-native point features vs scalar/decomp (bits, z):")
dm6=[v%6 for v in d]; dm3=[v%3 for v in d]
nm6=[v%6 for v in n]; km6=[v%6 for v in k]; Dm6=[v%6 for v in D]
targs={"d%6":dm6,"d%3":dm3,"n%6":nm6,"k%6":km6,"D%6":Dm6}
feats={"chi6(X)":c6X,"chi3(X)":c3X,"chi2(X)":c2X,"chi6(Y)":c6Y}
print(f"{'':10}"+"".join(f"{t:>14}" for t in targs))
for fn,fv in feats.items():
    row=f"{fn:10}"
    for tn,tv in targs.items():
        r,z=realMI(fv,tv); row+=f"  {r:>6.4f}/{z:>4.1f}"
    print(row)

print("\n3) RESONANCE SCAN  MI(chi6(X); d mod m) - null, over m (peak => resonance):")
best=[]
for m in [2,3,4,5,6,7,8,9,11,12,13,18,24,36,7*6,63,84]:
    r,zz=realMI(c6X,[v%m for v in d]); best.append((zz,m,r))
for zz,m,r in sorted(best,reverse=True)[:6]:
    print(f"   m={m:3d}: real MI={r:.4f} bits, z={zz:.1f}")

print("\n4) INTERFERENCE (chi6(X),chi6(Y)) 6x6 joint vs uniform (curve-eqn pattern):")
J=Counter(zip(c6X,c6Y)); exp=N/36
chi2stat=sum((J[(i,j)]-exp)**2/exp for i in range(6) for j in range(6))
# forbidden/enhanced cells
cells=sorted(((J[(i,j)]/exp,i,j) for i in range(6) for j in range(6)))
print(f"   chi^2(35 df)={chi2stat:.0f}  (uniform ~35).  extreme cells (obs/exp):")
print(f"     lowest:  {[(f'{i},{j}',round(r,2)) for r,i,j in cells[:3]]}")
print(f"     highest: {[(f'{i},{j}',round(r,2)) for r,i,j in cells[-3:]]}")
