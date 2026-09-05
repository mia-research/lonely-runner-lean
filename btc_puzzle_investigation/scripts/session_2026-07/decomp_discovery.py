"""
DISCOVERY: could a bounded-window / residue-sieve / congruence-filter attach to
the chosen keys? Such a tool needs the chosen (n,k,residues) to be NON-GENERIC vs
a truly-uniform key. The decomposition itself is a tautology, so we compare the 82
CHOSEN keys' coordinates against a COMPUTED reference (uniform u), not an assumed
one. Any exploitable structure = chosen deviates from the uniform reference.

Four probes, each with its correct reference:
  [A] best-approx denominator n: chosen vs Monte-Carlo uniform-u reference.
      (uniform u does NOT give uniform n -- must compute the reference, not assume)
  [B] Farey depth  theta = ||u*n|| * n  (how deep the approx sits): chosen vs ref.
  [C] integer-congruence scan: is d mod m (and the free part r=d-2^{N-1} mod m)
      non-uniform across chosen keys?  a hit => a residue sieve d = r (mod m).
  [D] n mod m and k mod m non-uniformity.
Multiple testing is tracked; a hit is a candidate, not a verdict.
"""
import csv
from math import gcd, log2
from fractions import Fraction
import numpy as np

def best_nk_float(u, nmax=256):
    best=(9e9,1,0)
    for n in range(1,nmax+1):
        k=round(u*n); e=abs(u-k/n)
        if e<best[0]: best=(e,n,k)
    return best[1],best[2],best[0]

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['bits']),int(r['private_key'],16),int(r['n']),int(r['k'])))
# distributional probes need u with >=~10 real bits, so best-approx isn't forced
big=[(b,d,n,k) for (b,d,n,k) in rows if b>=11]
Nn=np.array([n for _,_,n,_ in big]); Kk=np.array([k for _,_,_,k in big])
Dd=[d for _,d,_,_ in big]; Bb=[b for b,_,_,_ in big]
print(f"{len(big)} chosen keys with N>=11 (distributional probes); {len(rows)} total.")

rng=np.random.default_rng(2024)
# ---------- [A] reference n-distribution from uniform u ----------
REF=200000
ru=rng.random(REF)
refn=np.array([best_nk_float(x)[0] for x in ru])
# two-sample KS on n (chosen vs reference)
def ks2(a,b):
    a=np.sort(a); b=np.sort(b); i=j=0; d=0.0
    grid=np.union1d(a,b)
    Fa=np.searchsorted(a,grid,side='right')/len(a)
    Fb=np.searchsorted(b,grid,side='right')/len(b)
    return np.max(np.abs(Fa-Fb))
ksn=ks2(Nn,refn)
crit=1.36*np.sqrt(1/len(Nn)+1/REF)
print(f"\n[A] denominator n vs uniform-u reference:")
print(f"    chosen n: median {np.median(Nn):.0f}, mean {Nn.mean():.0f}, %>=200 = {(Nn>=200).mean():.2f}")
print(f"    ref    n: median {np.median(refn):.0f}, mean {refn.mean():.0f}, %>=200 = {(refn>=200).mean():.2f}")
print(f"    two-sample KS = {ksn:.3f}  (5% crit {crit:.3f}) -> "
      f"{'DEVIATES' if ksn>crit else 'consistent with uniform'}")

# ---------- [B] Farey depth theta = ||u*n|| * n ----------
def theta_from(u,n,k):
    return abs(u-k/n)*n*n            # normalized approx quality in [0, .5]
th_ch=np.array([theta_from(float(Fraction(d-2**(b-1),2**(b-1))),n,k) for (b,d,n,k) in big])
th_rf=np.array([theta_from(x,*best_nk_float(x)[:2][::1]) for x in ru[:20000]]) if False else None
# reference theta properly:
th_rf=[]
for x in ru[:20000]:
    n,k,e=best_nk_float(x); th_rf.append(e*n*n)
th_rf=np.array(th_rf)
ksth=ks2(th_ch,th_rf)
critth=1.36*np.sqrt(1/len(th_ch)+1/len(th_rf))
print(f"\n[B] Farey depth theta=|u-k/n|*n^2:")
print(f"    chosen: median {np.median(th_ch):.3f}   reference: median {np.median(th_rf):.3f}")
print(f"    KS = {ksth:.3f} (5% crit {critth:.3f}) -> "
      f"{'DEVIATES' if ksth>critth else 'consistent'}")

# ---------- [C] integer-congruence scan on d and free part r ----------
def chi_uniform(vals, m):
    obs=np.bincount(np.array([v%m for v in vals]),minlength=m).astype(float)
    exp=len(vals)/m
    return ((obs-exp)**2/exp).sum(), m-1
from math import erf
def chisq_sf(x,df):  # survival via Wilson-Hilferty
    if x<=0: return 1.0
    t=(x/df)**(1/3); mu=1-2/(9*df); s=np.sqrt(2/(9*df)); z=(t-mu)/s
    return 0.5*(1-erf(z/np.sqrt(2)))
alld=[d for _,d,_,_ in rows]
rfree=[d-2**(b-1) for b,d,_,_ in rows]
print(f"\n[C] congruence scan (chi-square vs uniform; {len(alld)} keys). "
      f"Bonferroni over the m-range noted.")
ms=list(range(2,33)); hits=[]
for label,vals in (("d mod m",alld),("r=d-2^(N-1) mod m",rfree)):
    best=(1.0,None)
    for m in ms:
        x,df=chi_uniform(vals,m); p=chisq_sf(x,df)
        if p<best[0]: best=(p,m)
    bonf=min(1.0,best[0]*len(ms))
    print(f"    {label:>20}: smallest p at m={best[1]} -> p={best[0]:.4f} "
          f"(Bonferroni {bonf:.3f}){'  << candidate' if bonf<0.05 else ''}")

# ---------- [D] n mod m, k mod m ----------
print(f"\n[D] n mod m / k mod m non-uniformity ({len(rows)} keys):")
for label,vals in (("n mod m",[n for _,_,n,_ in rows]),("k mod m",[k for _,_,_,k in rows])):
    best=(1.0,None)
    for m in range(2,17):
        x,df=chi_uniform(vals,m); p=chisq_sf(x,df)
        if p<best[0]: best=(p,m)
    bonf=min(1.0,best[0]*15)
    print(f"    {label:>8}: smallest p at m={best[1]} -> p={best[0]:.4f} (Bonf {bonf:.3f})"
          f"{'  << candidate' if bonf<0.05 else ''}")

print("\nRead: any DEVIATES / candidate is where a window or sieve could attach.")
print("All consistent => the chosen keys' decomposition coords match uniform keys")
print("at this sample/these probes -> no sieve handle here, at this power.")
