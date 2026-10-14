#!/usr/bin/env python3
"""Do clustered-at-the-end and clustered-in-the-middle need their own treatment?

The problem is TRANSLATION invariant (subtract any speed) and REFLECTION invariant
(v -> C - v leaves every |v_j - v_i| unchanged, and ||.|| is even). So a configuration is
determined, for LRC purposes, by its GAP SEQUENCE UP TO REVERSAL.
Test that, then measure difficulty by where the clustering sits.
"""
from itertools import combinations
from collections import Counter

def cons(V,i): return tuple(sorted({abs(w-V[i]) for w in V if w!=V[i]}))
def profile(V): return sorted(cons(V,i) for i in range(len(V)))
def reflect(V):
    C=max(V)+min(V); return tuple(sorted(C-v for v in V))
def residual(S): return not any(all(s%d for s in S) for d in range(2,9))

N=16
print("TEST 1 -- reflection invariance: does V and its mirror pose the same problem?")
bad=0; tot=0
for V in combinations(range(1,N+1),8):
    tot+=1
    if profile(V)!=profile(reflect(V)): bad+=1
print(f"   {tot:,} configurations: per-runner constraint profiles differ under reflection in {bad}"
      f"   {'PASS -- identical' if bad==0 else '*** FAIL ***'}")
print("   => clustered-at-the-FRONT and clustered-at-the-END are the SAME problem mirrored.")
print()

print("TEST 2 -- difficulty by where the clustering sits.")
print("   gap sequence g_1..g_7 of the sorted speeds; classify by which third holds the")
print("   smallest gaps (weighted centroid of 1/g).")
buckets={}
for V in combinations(range(1,N+1),8):
    g=[V[i+1]-V[i] for i in range(7)]
    w=[1.0/x for x in g]; tot_w=sum(w)
    centroid=sum((i+0.5)*w[i] for i in range(7))/tot_w/7.0   # in [0,1]
    key = 'front' if centroid<1/3 else ('end' if centroid>2/3 else 'middle')
    b=buckets.setdefault(key,[0,0,0])
    for i in range(8):
        b[0]+=1
        if residual(cons(V,i)): b[1]+=1
    b[2]+=1
print(f"   {'cluster':>8} {'configs':>9} {'runners':>9} {'residual runners':>18}")
for k in ('front','middle','end'):
    if k not in buckets: continue
    n,r,c=buckets[k]
    print(f"   {k:>8} {c:>9,} {n:>9,} {r:>10,} = {100*r/n:5.2f}%")
print()
print("TEST 3 -- are front and end statistically identical, as reflection predicts?")
f=buckets.get('front',[0,0,0]); e=buckets.get('end',[0,0,0])
print(f"   front residual rate {100*f[1]/f[0]:.4f}%   end residual rate {100*e[1]/e[0]:.4f}%")
print(f"   identical: {f[1]/f[0]==e[1]/e[0] if f[0] and e[0] else 'n/a'}")
