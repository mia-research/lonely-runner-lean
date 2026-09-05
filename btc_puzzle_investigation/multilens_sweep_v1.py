#!/usr/bin/env python3
"""
Multi-lens selection sweep: guard against a false null from LENS/representation bias.
Pre-registered NON-MODULAR features across binary / decimal / multiplicative lenses
(modular residues in every base are already covered by the all-moduli joint test,
reset_method2, null). Each feature: real-82 aggregate vs the 100k SYNTHETIC pool as
a bit-length-matched null; two-sided rank p-value; Bonferroni over the battery.
Exact integer feature ops; the mean/dispersion is a monotone stat ranked vs a
matched null (no float threshold decides a verdict).
"""
import csv, random
from sympy import primerange

SMALL_PRIMES=list(primerange(2,1000))

def features(d, N):
    low = d - (1<<(N-1)) if N>1 else 0
    w = N-1 if N>1 else 1
    bits = [(low>>i)&1 for i in range(w)]
    pc = sum(bits)
    # longest run
    lr=1; cur=1
    for i in range(1,w):
        if bits[i]==bits[i-1]: cur+=1; lr=max(lr,cur)
        else: cur=1
    half=w//2
    topbot = sum(bits[half:]) - sum(bits[:half])
    v2 = (d & -d).bit_length()-1 if d else 0
    ds = str(d)
    lead = int(ds[0]); trail = d%10; tz10 = len(ds)-len(ds.rstrip('0'))
    nsf = sum(1 for p in SMALL_PRIMES if d%p==0)
    return {
        'B1_hamming_frac': (pc, w),          # ratio pc/w handled at aggregate
        'B2_longrun': lr,
        'B3_topbot_bal': topbot,
        'B4_v2_trailingzeros': v2,
        'D1_lead_digit': lead,               # categorical 1..9
        'D2_trail_digit': trail,             # categorical 0..9
        'D3_dec_trailzeros': tz10,
        'M1_smallprime_count': nsf,
    }
SCALAR=['B2_longrun','B3_topbot_bal','B4_v2_trailingzeros','D3_dec_trailzeros','M1_smallprime_count']
RATIO =['B1_hamming_frac']
CATEG ={'D1_lead_digit':(1,9),'D2_trail_digit':(0,9)}

# load real + synthetic-by-bitlen, precompute features once
real=[]; realbits=[]
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        d=int(row['private_key'],16); b=int(row['bits']); real.append(features(d,b)); realbits.append(b)
synth={}
with open('constructed_keys_1to160_100k_exact.csv') as f:
    for row in csv.DictReader(f):
        b=int(row['bits']); synth.setdefault(b,[]).append(features(int(row['d']),b))
print(f"real {len(real)} | synthetic pool {sum(len(v) for v in synth.values())} | features {len(SCALAR)+len(RATIO)+len(CATEG)}")

def agg_scalar(fs,key): return sum(x[key] for x in fs)/len(fs)
def agg_ratio(fs,key):
    num=sum(x[key][0] for x in fs); den=sum(x[key][1] for x in fs); return num/den
def agg_categ(fs,key,lo,hi):
    k=hi-lo+1; c=[0]*k
    for x in fs: c[x[key]-lo]+=1
    tot=sum(c); return sum((k*ci-tot)**2 for ci in c)

rng=random.Random(31337); NULLN=20000
def bit_matched_draw():
    return [rng.choice(synth[b]) for b in realbits if b in synth]

# observed aggregates
obsval={}
for k in SCALAR: obsval[k]=agg_scalar(real,k)
for k in RATIO:  obsval[k]=agg_ratio(real,k)
for k,(lo,hi) in CATEG.items(): obsval[k]=agg_categ(real,k,lo,hi)
# ONE shared null loop: compute every feature's aggregate per draw
above={k:0 for k in obsval}; below={k:0 for k in obsval}
for _ in range(NULLN):
    fs=bit_matched_draw()
    for k in SCALAR:
        v=agg_scalar(fs,k)
        if v>=obsval[k]: above[k]+=1
        if v<=obsval[k]: below[k]+=1
    for k in RATIO:
        v=agg_ratio(fs,k)
        if v>=obsval[k]: above[k]+=1
        if v<=obsval[k]: below[k]+=1
    for k,(lo,hi) in CATEG.items():
        if agg_categ(fs,k,lo,hi)>=obsval[k]: above[k]+=1
results={}
for k in SCALAR+RATIO:
    results[k]=(round(obsval[k],4), min(1.0, 2*min(above[k],below[k])/NULLN))
for k in CATEG:
    results[k]=(obsval[k], above[k]/NULLN)

m=len(results)
print(f"\n{'feature':24} {'obs':>10}  {'p(2sided)':>10}  {'Bonf x'+str(m):>10}")
print("-"*62)
for key in sorted(results):
    obs,p=results[key]
    print(f"{key:24} {str(obs):>10}  {p:>10.4f}  {min(1.0,p*m):>10.4f}")
minp=min(p for _,p in results.values())
print(f"\nmin p = {minp:.4f}; Bonferroni x{m} = {min(1.0,minp*m):.4f}")
print("=> a non-null under any lens shows as a surviving Bonferroni-corrected p.")

# CONTROL: plant a binary bias (force low Hamming weight) -> B1 must fire
plant=[]
for b in realbits:
    if b>1:
        # low weight: set only a few random low bits
        low=0
        for _ in range(max(1,(b-1)//8)): low |= 1<<rng.randrange(b-1)
        plant.append(features((1<<(b-1))|low,b))
    else: plant.append(features(1,b))
obs=agg_ratio(plant,'B1_hamming_frac'); below=sum(1 for _ in range(NULLN) if agg_ratio(bit_matched_draw(),'B1_hamming_frac')<=obs)
print(f"\n[CONTROL low-Hamming plant] B1 obs={obs:.4f}, P(null<=obs)={below/NULLN:.5f} (want ~0)")
