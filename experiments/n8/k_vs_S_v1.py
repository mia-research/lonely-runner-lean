"""Is the flank-opening index k bounded as a function of S = d_max/d_min ?
bounded_k_attack_v1 reached k=369 but its witness has S ~ 14,125.  That experiment asked
'is k bounded?' (no).  It never asked 'is k bounded GIVEN S?'.  Adversarial per S-band.
Exact Fraction.  2026-09-18."""
import random, time
from fractions import Fraction as F

TH=F(1,8)
def circd(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1-f)
def min_k_any_flank(ds, KMAX):
    for k in range(KMAX+1):
        kk=F(k)+TH
        for e in ds:
            t = kk/e
            if all(circd(d*t) >= TH for d in ds):
                return k
    return None
def Sof(ds): return max(ds)/min(ds)

rng=random.Random(20260918)
def rand_ds(Scap, dens):
    """7 positive rationals with d_max/d_min <= Scap"""
    lo=F(1)
    out={lo}
    while len(out)<7:
        num=rng.randint(1, int(Scap*dens))
        v=F(num,dens)
        if v>=lo and v<=lo*Scap: out.add(v)
    return sorted(out)
def perturb(ds, Scap, dens):
    out=list(ds); i=rng.randrange(7)
    out[i]=out[i]+F(rng.randint(-40,40), dens)
    if out[i]<=0: return None
    out=sorted(set(out))
    if len(out)!=7: return None
    if Sof(out)>Scap: return None
    return out

print(f"{'S cap':>8} {'restarts':>9} {'max min-k':>10} {'S at max':>10} {'KMAX hit':>9}")
BUDGET=55
for Scap in [8,10,15,20,30,50,100,300,1000]:
    KMAX = max(60, int(Scap*4))
    t0=time.time(); best=(-1,None); restarts=0; hits=0
    while time.time()-t0 < BUDGET:
        restarts+=1
        dens = rng.choice([7,13,14,100,1000])
        ds = rand_ds(Scap, dens)
        k = min_k_any_flank(ds, KMAX)
        if k is None: hits+=1; continue
        cur=(k,ds)
        for _ in range(250):
            if time.time()-t0>BUDGET: break
            cand = perturb(cur[1], Scap, dens)
            if cand is None: continue
            kk = min_k_any_flank(cand, KMAX)
            if kk is None: hits+=1; continue
            if kk>=cur[0]:
                cur=(kk,cand)
                if kk>best[0]: best=(kk,cand)
    print(f"{Scap:>8} {restarts:>9} {best[0]:>10} {float(Sof(best[1])):>10.2f} {hits:>9}")
    if best[0]>0:
        print(f"         witness readings: {[round(float(d/min(best[1])),3) for d in best[1]]}")
