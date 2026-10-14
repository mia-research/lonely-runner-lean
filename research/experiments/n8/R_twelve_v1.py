"""Max R found is 11.9649 across 6.15M profile evaluations -- matching the 11.96 already on file.
That is far below band 1's ceiling of 15.  Is the real barrier 12 = 8 x 1.5 (d_min antipodal)?

Two probes:
 (1) hunt specifically for R >= 12, with seeds AT the current maximiser
 (2) at the maximiser, identify WHICH disparity blocks just past R = 11.9649
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
import random
def clear(S,R):
    for s in S:
        m=(s*R)%8.0
        if m<1.0 or m>7.0: return False
    return True
def Rdir(S, RMAX=40.0):
    c=[1.0]
    for s in S:
        k=1
        while (8*k+1)/s<=RMAX:
            r=(8*k+1)/s
            if r>=1.0: c.append(r)
            k+=1
    c.sort()
    for R in c:
        if clear(S,R+1e-12): return R
    return None
BEST=[1.0,2.2817,3.1758,4.1893,5.2226,5.7856,7.4384]
print(f"(1) targeted hunt for R >= 12, seeded at the current maximiser")
rng=random.Random(4242)
best=(Rdir(BEST),tuple(BEST)); N=0
for restart in range(2500):
    if restart%2==0:
        S=[1.0]+[max(1.03,x+rng.gauss(0,0.25)) for x in BEST[1:]]
        S=[1.0]+sorted(S[1:])
    else:
        S=[1.0]+sorted(rng.uniform(1.05,7.95) for _ in range(6))
    cur=Rdir(S) or 0; stall=0
    for _ in range(4000):
        W=list(S); k=rng.randrange(1,7)
        W[k]+=rng.gauss(0,0.03)
        W=[1.0]+sorted(W[1:])
        if W[1]<=1.02 or W[6]>15.0 or any(W[i+1]-W[i]<0.02 for i in range(6)): continue
        v=Rdir(W) or 0; N+=1
        if v>cur: S,cur,stall=W,v,0
        elif v==cur: S,stall=W,stall+1
        else: stall+=1
        if stall>600: break
    if cur>best[0]: best=(cur,tuple(W))
print(f"    {N} evaluations;  max R = {best[0]:.6f}   band {int(best[0]//8)}")
print(f"    R >= 12 : {'REACHED' if best[0]>=12 else 'NOT reached'}")

print(f"\n(2) at the maximiser, what blocks just past R = {best[0]:.6f}?")
S=list(best[1]); R=best[0]
print(f"    profile: " + " ".join(f"{x:.4f}" for x in S))
print(f"    {'s_i':>9} {'s_i R mod 8':>13}  status")
for s in S:
    m=(s*R)%8.0
    print(f"    {s:>9.4f} {m:>13.5f}  {'AT LOWER EDGE' if abs(m-1)<0.01 else ('AT UPPER EDGE' if abs(m-7)<0.01 else 'interior')}")
eps=1e-6
print(f"\n    just past (R + 1e-6):")
for s in S:
    m=(s*(R+eps))%8.0
    if m<1.0 or m>7.0: print(f"      s = {s:.4f} goes BAD (mod 8 = {m:.6f})")
