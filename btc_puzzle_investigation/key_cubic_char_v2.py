#!/usr/bin/env python3
"""
v2 — re-do of the multiplicative cubic/sextic character test, addressing two flaws
in v1:
  (1) v1 attributed the p=0.10 cubic lean to a 'decimal/human artifact' by analogy
      to the base-10 finding. That analogy is unjustified (different object). Drop it.
  (2) Use the canonical 100k SYNTHETIC dataset as the null (better powered,
      reproducible) instead of a fresh 20k randrange bootstrap. Also test the
      SYNTHETIC baseline directly: if synthetic keys show the SAME class-0 lean,
      the lean is intrinsic to the short-interval character sum, NOT creator signal.
Also states the honest scope: this channel only carries creator info if the
generator worked mod n (an LCG mod n) -- already tested null (T2). Real signal is
irreducibly the 82 solved keys; the 100k are OUR randint (null, not signal).
"""
import csv, random
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
LAM= 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
e3=(N-1)//3; e6=(N-1)//6
croot={pow(LAM,j,N):j for j in range(3)}
def prim6():
    for g in range(2,200):
        z=pow(g,e6,N)
        if pow(z,6,N)==1 and all(pow(z,k,N)!=1 for k in (1,2,3)): return z
Z6=prim6(); sroot={pow(Z6,j,N):j for j in range(6)}
def chi3(d): return croot.get(pow(d%N,e3,N))
def chi6(d): return sroot.get(pow(d%N,e6,N))
def counts(vals,k):
    c=[0]*k
    for v in vals:
        if v is not None: c[v]+=1
    return c
def disp(c):
    tot=sum(c); k=len(c)
    return sum((k*ci-tot)**2 for ci in c) if tot else 0

# real keys (the ONLY creator data)
real=[]; realbits=[]
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        real.append(int(row['private_key'],16)); realbits.append(int(row['bits']))
# 100k synthetic keys grouped by bit-length (OUR randint => null only)
synth={}
with open('constructed_keys_1to160_100k_exact.csv') as f:
    for row in csv.DictReader(f):
        synth.setdefault(int(row['bits']),[]).append(int(row['d']))
print(f"real keys: {len(real)} | synthetic pool: {sum(len(v) for v in synth.values())} across {len(synth)} bit-lengths")

for name,chi,k in [("cubic chi3",chi3,3),("sextic chi6",chi6,6)]:
    # (a) synthetic BASELINE over ALL 100k -- is the null itself uniform?
    allsyn=[d for v in synth.values() for d in v]
    base=counts([chi(d) for d in allsyn],k)
    # (b) real observed
    obs=counts([chi(d) for d in real],k)
    # (c) bit-MATCHED null from the synthetic pool: draw one synth key per real bit-length
    rng=random.Random(2024); NULLN=20000; s_obs=disp(obs); worse=0
    for _ in range(NULLN):
        draw=[rng.choice(synth[b]) for b in realbits if b in synth]
        if disp(counts([chi(d) for d in draw],k))>=s_obs: worse+=1
    print(f"\n  {name}:")
    print(f"    synthetic baseline (100k) class fractions: {[round(x/sum(base),3) for x in base]}  (uniform={round(1/k,3)})")
    print(f"    real-82 class counts {obs} (frac {[round(x/sum(obs),3) for x in obs]}); dispersion={s_obs}")
    print(f"    real vs 100k-synthetic bit-matched null: P(disp>=obs)={worse/NULLN:.4f}")

# CONTROL: does the pipeline detect a REAL vs SYNTHETIC difference? plant cubic-residue reals.
rng=random.Random(5); planted=[pow(rng.randrange(2,N),3,N) for _ in real]
o=counts([chi3(d) for d in planted],3); s=disp(o); worse=0
for _ in range(20000):
    draw=[rng.choice(synth[b]) for b in realbits if b in synth]
    if disp(counts([chi3(d) for d in draw],3))>=s: worse+=1
print(f"\n  [CONTROL planted cubic-residue 'reals'] counts {o}; P(>=obs)={worse/20000:.5f} (want ~0)")
