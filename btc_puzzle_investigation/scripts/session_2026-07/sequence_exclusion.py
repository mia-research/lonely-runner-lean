"""
SAME QUESTION (exploitable structure in the chosen keys), DIFFERENT ANGLES.
Corrects three assumptions from the earlier residue tests:

  #1 index was marginalized out. Keys were generated sequentially (one batch).
     Test the SEQUENCE of n_i, k_i, u_i (ordered by puzzle #), not the histogram.
  #2 only distributional shift was tested. Add EXCLUSION: forbidden (n,k) cells.
  #3 "no generator" was an UNDERPOWERED null (spectral control failed at n=63) and
     only the d-bits were BM-tested, never n/k. Re-open with fired controls.

Every detector carries a positive control; a null without a firing control is
discarded (it just means underpowered).
"""
import csv, math
from math import gcd
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']),int(r['bits']),int(r['private_key'],16),
                     int(r['n']),int(r['k'])))
rows.sort()
# contiguous run with real (non-forced) n: puzzles 11..70
run=[(p,b,d,n,k) for (p,b,d,n,k) in rows if 11<=p<=70]
P=[p for p,_,_,_,_ in run]; N=[b for _,b,_,_,_ in run]
dd=[d for _,_,d,_,_ in run]; nn=np.array([n for _,_,_,n,_ in run],float)
kk=np.array([k for _,_,_,_,k in run],float)
uu=np.array([(d-2**(b-1))/2**(b-1) for _,b,d,_,_ in run])
L=len(run); print(f"contiguous run puzzles 11-70: {L} keys")
rng=np.random.default_rng(5)

# ---------- ANGLE #1: sequence structure (with controls) ----------
def autocorr(s,lag):
    s=np.asarray(s,float); s=s-s.mean(); den=(s*s).sum()
    return (s[:-lag]*s[lag:]).sum()/den if den>0 else 0.0
def affine_R2(s):
    """predict s[i] from s[i-1],s[i-2] by least squares; R^2, + shuffle-null p."""
    y=s[2:]; Xd=np.column_stack([s[1:-1],s[:-2],np.ones(len(y))])
    beta,_,_,_=np.linalg.lstsq(Xd,y,rcond=None); r=y-Xd@beta
    R2=1-(r@r)/(((y-y.mean())**2).sum()+1e-30)
    null=[]
    for _ in range(2000):
        ys=rng.permutation(y); b2,_,_,_=np.linalg.lstsq(Xd,ys,rcond=None); rr=ys-Xd@b2
        null.append(1-(rr@rr)/(((ys-ys.mean())**2).sum()+1e-30))
    p=(1+sum(x>=R2 for x in null))/(1+len(null)); return R2,p
def lcg_modulus(s,B):
    q=[int(x*(1<<B)) for x in s] if max(s)<=1 else [int(x)%(1<<B) for x in s]
    d1=[q[i+1]-q[i] for i in range(len(q)-1)]
    z=[d1[i+1]*d1[i-1]-d1[i]*d1[i] for i in range(1,len(d1)-1)]
    g=0
    for v in z: g=gcd(g,v)
    return abs(g).bit_length()

print("\n[#1 SEQUENCE] autocorrelation (white 95%% band +-%.3f):"%(2/math.sqrt(L)))
for nm,s in (("u",uu),("n",nn),("k",kk)):
    ac=[round(autocorr(s,l),3) for l in (1,2,3)]
    print(f"    {nm}: lag1..3 = {ac}")
# control: AR(1) sequence must show lag1 autocorr
ar=np.zeros(L);
for i in range(1,L): ar[i]=0.6*ar[i-1]+rng.normal()
print(f"    [CTRL AR(1)]: lag1 = {autocorr(ar,1):+.3f}  (control fires if ~0.6)")

print("\n[#1 SEQUENCE] affine predictability R^2 (predict s_i from 2 prev):")
for nm,s in (("u",uu),("n",nn),("k",kk)):
    R2,p=affine_R2(s); print(f"    {nm}: R^2={R2:.3f}  shuffle-p={p:.3f}{'  << structure' if p<0.05 else ''}")
# control: an LCG must be perfectly affine-predictable
Mc=2**31-1; lc=np.empty(L); x=12345
for i in range(L): x=(1103515245*x+12345)%Mc; lc[i]=x/Mc
R2,p=affine_R2(lc); print(f"    [CTRL LCG]: R^2={R2:.3f}  p={p:.3f}  (fires if R^2~1)")

print("\n[#1 SEQUENCE] LCG modulus recovery (bit-length of recovered gcd):")
for B in (20,28,36):
    print(f"    u @B={B}: {lcg_modulus(uu,B)} bits (a hit ~ B); ", end="")
    # control LCG at width B
    Mc2=(1<<B)-1; s=[]; x=7
    for _ in range(L): x=(16807*x+3)%Mc2; s.append(x/Mc2)
    print(f"[CTRL LCG@{B}]: {lcg_modulus(np.array(s),B)} bits")

# ---------- ANGLE #2: exclusion / forbidden (n,k) cells ----------
print("\n[#2 EXCLUSION] forbidden (n mod a, k mod b) cells vs matched-uniform ref:")
import random as _rr; _rr.seed(9)
def synth_nk():
    out=[]
    for _,b,_,_,_ in run:
        lo=2**(b-1); d=lo+_rr.randrange(lo); u=(d-lo)/lo
        best=(9e9,1,0)
        for n in range(1,257):
            k=round(u*n); e=abs(u-k/n)
            if e<best[0]: best=(e,n,k)
        out.append((best[1],best[2]))
    return out
def empty_cells(nk,a,b):
    seen=set((n%a,k%b) for n,k in nk)
    return a*b-len(seen)
ch_nk=[(int(n),int(k)) for n,k in zip(nn,kk)]
for (a,b) in ((6,6),(8,8),(5,7),(12,5)):
    obs=empty_cells(ch_nk,a,b)
    null=[empty_cells(synth_nk(),a,b) for _ in range(300)]
    p=(1+sum(x>=obs for x in null))/(1+len(null))   # MORE empty => exclusion
    print(f"    ({a}x{b}): chosen empties={obs}  null-med={np.median(null):.0f}  "
          f"p(more-empty)={p:.3f}{'  << exclusion' if p<0.05 else ''}")

print("\nControls that FIRE validate the nulls. Any '<<' is a candidate to chase.")
