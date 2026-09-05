#!/usr/bin/env python3
"""
Generation-recipe SIGNATURE battery. For each candidate recipe, generate keys
matching the 82 real keys' bit-length multiset, fingerprint them across the
calibrated detector set, then ask which recipe the 82 REAL keys resemble.
Smarter than brute seed-search: characterize each recipe's fingerprint, then match.

Recipes: uniform, MT(getrandbits), LCG(mod 2^b), smooth-select, decimal-select, lowHam.
Key-side detectors (recipe signatures live here; point side is decoupled per the
constructed-key result): Hamming fraction, small-prime-factor count(<=1000),
decimal trailing zeros, Farey denominator n.
Match: real vs each recipe, two-sample permutation p per detector. A recipe is
CONSISTENT if the real keys fail to reject on every detector; DISTINGUISHABLE if any
detector rejects. Exact ints; mean is a monotone stat ranked vs matched shuffle.
"""
import csv, random, math
from fractions import Fraction
from sympy import primerange
SP=list(primerange(2,1000))
rng=random.Random(20260712)

# real keys + their bit lengths
real=[]; bits=[]
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        real.append(int(row['private_key'],16)); bits.append(int(row['bits']))

def keyU(b): A=1<<(b-1); return A+rng.randrange(1<<(b-1)) if b>1 else 1
def keyMT(b): return (1<<(b-1))|rng.getrandbits(b-1) if b>1 else 1
class LCG:
    def __init__(s,seed): s.x=seed
    def nx(s,b):
        s.x=(6364136223846793005*s.x+1442695040888963407)&((1<<64)-1)
        # assemble b-1 bits from high bits of successive outputs
        out=0; need=b-1
        while need>0:
            s.x=(6364136223846793005*s.x+1442695040888963407)&((1<<64)-1)
            take=min(32,need); out=(out<<take)|((s.x>>(64-take))&((1<<take)-1)); need-=take
        return (1<<(b-1))|out if b>1 else 1
lcg=LCG(0xDEADBEEF)
def keyLCG(b): return lcg.nx(b)
def keySmooth(b):
    A=1<<(b-1)
    if b<=6:  # tiny: just uniform (few choices)
        return keyU(b)
    for _ in range(200):
        d=1
        while d<A: d*=rng.choice(SP[:80])
        if A<=d<2*A: return d
    return keyU(b)
def keyDecimal(b):
    A=1<<(b-1)
    if b<8: return keyU(b)
    for _ in range(200):
        d=keyU(b);
        # round to a decimal multiple in-range
        base=10**(max(1,len(str(d))-3))
        dd=(d//base)*base
        if A<=dd<2*A and dd>0: return dd
    return keyU(b)
def keyLowHam(b):
    if b<=2: return (1<<(b-1)) if b>1 else 1
    d=1<<(b-1)
    for _ in range(rng.randint(1,3)): d|=1<<rng.randrange(b-1)
    return d
RECIPES={'uniform':keyU,'MT_getrandbits':keyMT,'LCG64':keyLCG,
         'smooth_select':keySmooth,'decimal_select':keyDecimal,'lowHam':keyLowHam}

def ham_frac(d,b): return bin(d).count('1')/max(1,b)
def smooth_ct(d):
    c=0
    for q in SP:
        while d%q==0: d//=q;c+=1
    return c
def deczeros(d):
    s=str(d); return len(s)-len(s.rstrip('0'))
def farey_n(d,b):
    A=1<<(b-1); return Fraction(d-A,A).limit_denominator(256).denominator if b>1 else 1
DETS=['ham_frac','smooth_ct','decZeros','farey_n']
def featvec(keys,bs):
    return {
      'ham_frac':[ham_frac(d,b) for d,b in zip(keys,bs)],
      'smooth_ct':[smooth_ct(d) for d in keys],
      'decZeros':[deczeros(d) for d in keys],
      'farey_n':[farey_n(d,b) for d,b in zip(keys,bs)],
    }
realF=featvec(real,bits)
def perm_p(a,b,reps=3000):
    obs=abs(sum(a)/len(a)-sum(b)/len(b)); pool=a+b; na=len(a); hit=0
    for _ in range(reps):
        rng.shuffle(pool)
        if abs(sum(pool[:na])/na-sum(pool[na:])/len(b))>=obs: hit+=1
    return hit/reps

DRAWS=20
print(f"REAL-82 vs each recipe, MEDIAN p over {DRAWS} independent recipe draws (kills")
print("single-draw sampling noise). LOW median p on a detector => real distinguishable there.")
print(f"{'recipe':16}"+"".join(f"{d:>12}" for d in DETS)+"   verdict")
import statistics
for rn,fn in RECIPES.items():
    per={dd:[] for dd in DETS}
    for _ in range(DRAWS):
        keys=[fn(b) for b in bits]; F=featvec(keys,bits)
        for dd in DETS: per[dd].append(perm_p(realF[dd][:],F[dd][:],reps=1200))
    med={dd:statistics.median(per[dd]) for dd in DETS}
    row=f"{rn:16}"+"".join(f"{med[dd]:>12.3f}" for dd in DETS)
    verdict="CONSISTENT" if min(med.values())>0.05 else f"distinguish(min med p={min(med.values()):.3f})"
    print(row+"   "+verdict)
print("\n(good-PRNG recipes should be CONSISTENT with real; selection recipes DISTINGUISHABLE")
print(" unless the real keys share that selection bias — that is the smoothness question.)")
