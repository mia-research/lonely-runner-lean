"""
FIX the two weak detectors from sequence_exclusion.py:
  - affine-R^2 could not see an LCG (modular wrap defeats float regression; its
    control failed). Replace with a proper MODULAR RECURRENCE search over Z_M:
    is  s_{i+1} == a*s_i + c (mod M)  for some (a,c,M)?  This is the real
    "generator on the n / k / position sequence" test, and it handles wrap.
  - exclusion test had no positive control. Add a planted-forbidden control.

Both detectors must FIRE on their control or the null is discarded.
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
run=[(p,b,d,n,k) for (p,b,d,n,k) in rows if 11<=p<=70]
nn=[int(n) for _,_,_,n,_ in run]; kk=[int(k) for _,_,_,_,k in run]
qq=[int(((d-2**(b-1))*(1<<24))//(2**(b-1))) for _,b,d,_,_ in run]   # 24-bit position ints
L=len(run); print(f"run 11-70: {L} keys")

def best_modular_recurrence(s, Mrange):
    """max fraction of i with s_{i+1} == a*s_i+c (mod M), over (a,M)."""
    best=(0.0,None,None)
    Ln=len(s)
    for M in Mrange:
        sm=[x%M for x in s]
        for a in range(M):
            # c_i = s_{i+1}-a s_i mod M ; consistency = frequency of the modal c
            cs=[(sm[i+1]-a*sm[i])%M for i in range(Ln-1)]
            vals,cnts=np.unique(cs,return_counts=True)
            frac=cnts.max()/(Ln-1)
            if frac>best[0]: best=(frac,a,M)
    return best

Mr=list(range(2,120))
print("\n[FIXED] modular recurrence  s_{i+1} == a*s_i + c (mod M)  best consistency:")
for nm,s in (("n",nn),("k",kk),("q(pos)",qq)):
    frac,a,M=best_modular_recurrence(s,Mr)
    print(f"    {nm}: best {frac*100:.0f}% consistent  (a={a}, M={M})")
# expected chance level: with modal-of-M-uniform over L-1 points
# control: a real modular recurrence must hit 100%
xc=[7]; a0,c0,M0=17,5,101
for i in range(L-1): xc.append((a0*xc[-1]+c0)%M0)
frac,a,M=best_modular_recurrence(xc,Mr)
print(f"    [CTRL recurrence a=17,c=5,M=101]: recovered {frac*100:.0f}% (a={a},M={M})  "
      f"{'FIRES' if frac>0.99 else 'FAIL'}")
# chance baseline: shuffle n and re-fit (breaks any real recurrence)
import random as _r; _r.seed(1)
sh=nn[:]; _r.shuffle(sh)
fracs,_,_=best_modular_recurrence(sh,Mr)
print(f"    [chance, shuffled-n]: best {fracs*100:.0f}% consistent  "
      f"(this is the look-elsewhere floor for the (a,M) search)")

# ---------- exclusion WITH a positive control ----------
print("\n[EXCLUSION + control] forbidden (n mod a, k mod b) cells:")
_r.seed(9)
def synth_nk(nkeys_b):
    out=[]
    for b in nkeys_b:
        lo=2**(b-1); d=lo+_r.randrange(lo); u=(d-lo)/lo
        best=(9e9,1,0)
        for n in range(1,257):
            k=round(u*n); e=abs(u-k/n)
            if e<best[0]: best=(e,n,k)
        out.append((best[1],best[2]))
    return out
Bs=[b for _,b,_,_,_ in run]
def empt(nk,a,b): return a*b-len(set((n%a,k%b) for n,k in nk))
ch=list(zip(nn,kk))
for (a,b) in ((6,6),(8,8)):
    obs=empt(ch,a,b); null=[empt(synth_nk(Bs),a,b) for _ in range(300)]
    p=(1+sum(x>=obs for x in null))/(1+len(null))
    print(f"    ({a}x{b}) chosen empties={obs} null-med={np.median(null):.0f} p={p:.3f}")
# control: force a forbidden region (drop all keys with n%6==0) -> must show excess empties
ctrl=[(n,k) for n,k in ch if n%6!=0]
obs=empt(ctrl,6,6); null=[empt(synth_nk(Bs),6,6) for _ in range(300)]
pc=(1+sum(x>=obs for x in null))/(1+len(null))
print(f"    [CTRL forbid n%6==0]: empties={obs} p={pc:.3f}  {'FIRES' if pc<0.05 else 'weak'}")
