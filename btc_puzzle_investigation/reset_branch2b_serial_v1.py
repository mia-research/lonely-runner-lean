#!/usr/bin/env python3
"""
BRANCH 2b: serial structure of the normalized-position SEQUENCE (bit-length confound
removed). Object: u_1..u_70 (contiguous), u_N = (d_N - 2^(N-1))/2^(N-1) as an exact
Fraction. Statistic: Kendall tau (concordant - discordant, an integer count) between the
sequence and its lag-L shift, for L=1,2,3. Null: shuffle the generation order (the
hypothesis under test) and recompute -> permutation p-value. Exact throughout.
Controls: an AR(1)/LCG-like ordered sequence must fire; a shuffled one must not.
"""
import random
from fractions import Fraction
from reset_common import load_solved, contiguous_run

solved=load_solved()
RUN=contiguous_run(solved,1)
U=[Fraction(solved[N]["d"]-(1<<(N-1)), 1<<(N-1)) for N in RUN]

def kendall_lag(seq, lag):
    a=seq[:len(seq)-lag]; b=seq[lag:]
    c=d=0
    n=len(a)
    for i in range(n):
        for j in range(i+1,n):
            sa=(a[i]>a[j])-(a[i]<a[j]); sb=(b[i]>b[j])-(b[i]<b[j])
            p=sa*sb
            if p>0: c+=1
            elif p<0: d+=1
    return c-d

def perm_p(seq, lag, B=4000, seed=0):
    obs=kendall_lag(seq,lag)
    rng=random.Random(seed); ge=le=0
    for _ in range(B):
        s=seq[:]; rng.shuffle(s); v=kendall_lag(s,lag)
        if v>=obs: ge+=1
        if v<=obs: le+=1
    return obs, 2*min(ge,le)/B

print("=== BRANCH 2b: serial correlation of normalized-position sequence ===\n")
for lag in (1,2,3):
    obs,p=perm_p(U,lag)
    print(f"  lag {lag}: Kendall (C-D) = {obs:>6}, 2-sided perm p = {min(p,1.0):.4f}")

# controls
def ar1(n, rho=0.8):
    rng=random.Random(1); xs=[Fraction(rng.randrange(10**6),10**6)]
    for _ in range(n-1):
        prev=xs[-1]
        nxt=(rho*prev + (1-rho)*Fraction(rng.randrange(10**6),10**6))
        xs.append(nxt)
    return xs
ac=ar1(len(U)); o,p=perm_p(ac,1)
print(f"\n[CTRL AR(1) rho=.8] lag1 Kendall={o}, p={p:.4f} -> {'FIRES' if p<0.01 else 'no'}")
rng=random.Random(2); sh=U[:]; rng.shuffle(sh); o2,p2=perm_p(sh,1,seed=3)
print(f"[CTRL shuffled real] lag1 Kendall={o2}, p={p2:.4f} -> {'null as expected' if p2>0.05 else 'unexpected'}")

print("\n-> " + ("SERIAL structure present" if min(perm_p(U,1)[1],perm_p(U,2)[1])<0.05
      else "no serial correlation in the generation-ordered sequence (control-valid)"))
