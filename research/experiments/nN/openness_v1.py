"""Is 'has an isolation point' an OPEN condition on arrangements?
A certificate is a flank e and index j.  At the opening (j+1/n)/e the flank reads exactly 1/n
BY CONSTRUCTION -- that equality moves with e and is not destroyed by perturbation.
Test: perturb every disparity by a small amount and ask whether the SAME (e,j) still certifies."""
from fractions import Fraction as F
import random
N=8
def clear_at(ds,e,j):
    a=N*j+1
    return all(e<=(d*a)%(N*e)<=(N-1)*e for d in ds)
def cert(ds):
    for e in ds:
        for j in range(e):
            if clear_at(ds,e,j): return (e,j)
    return None
def lonely_real(ds,t):
    def cd(x):
        f=x-int(x)
        if f<0: f+=1
        return min(f,1-f)
    return all(cd(d*t)>=F(1,N) for d in ds)
random.seed(11)
print("  perturbing every disparity by +-delta and re-testing the SAME certificate")
print("  delta      trials   same (e,j) still certifies   some certificate exists")
for den in (10**3,10**4,10**6,10**9):
    same=exists=tot=0
    for _ in range(600):
        ds=sorted(random.sample(range(1,60),7))
        c=cert(ds)
        if c is None: continue
        e,j=c
        # perturb: scale to rationals with a small random shift
        pert=[F(d)+F(random.choice([-1,1])*random.randrange(1,10),den) for d in ds]
        if len(set(pert))!=7: continue
        tot+=1
        # the SAME certificate: flank is the perturbed image of e, same index j
        ep=pert[ds.index(e)]
        t=(F(j)+F(1,N))/ep
        if lonely_real(pert,t): same+=1
        # does SOME opening of SOME perturbed flank work?
        ok=False
        for f in pert:
            for k in range(0,40):
                if lonely_real(pert,(F(k)+F(1,N))/f): ok=True; break
            if ok: break
        if ok: exists+=1
    print(f"  1/{den:<10d} {tot:6d} {same:26d} {exists:24d}")
