#!/usr/bin/env python3
"""
Reset thread C (redone in the CURVE-NATIVE coordinate): Eisenstein, not base-10.

The curve has CM by Z[omega] (disc -3). Its native "roundness" is Eisenstein:
chi_{-3} (d mod 3), split (p==1 mod 3) vs inert (p==2 mod 3) prime structure, and
v_3. Base-10's carriers 2 and 5 are BOTH inert in Z[omega] -- i.e. the doc's signal
lives in the non-curve primes. The curve-resonant question is whether SPLIT primes
(the ones that factor in Z[omega], where the CM/Hecke action lives) are over- or
under-represented in the keys.

Null = the 100k CONSTRUCTED-key dataset (660 uniform-random synthetic d per
bit-length), sampled to match each real key's bit-length. This is the matched-null
role the 100k set is for. Positive control: a keyset biased to chi_{-3}=1 + split
divisibility must fire.

Exact integers only.
"""
import csv, os, random
from collections import defaultdict
from reset_common import load_solved

PB = 500
def sieve(n):
    ok=[True]*(n+1); ok[0]=ok[1]=False
    for i in range(2,int(n**0.5)+1):
        if ok[i]:
            for j in range(i*i,n+1,i): ok[j]=False
    return [i for i in range(2,n+1) if ok[i]]
PRIMES = sieve(PB)
SPLIT  = [p for p in PRIMES if p%3==1]     # split in Z[omega]
INERT  = [p for p in PRIMES if p%3==2]     # inert
RAMIFIED = 3

def v(m,q):
    m=abs(m); c=0
    if m==0: return 0
    while m%q==0: m//=q; c+=1
    return c
def count_div(d, primes):
    return sum(1 for p in primes if d % p == 0)

solved = load_solved()
KEYS = sorted(solved)
BITS = {N: solved[N]["bits"] for N in KEYS}
D    = {N: solved[N]["d"] for N in KEYS}

# ---- load 100k constructed keys grouped by bit-length (the matched null source) ----
print("loading 100k constructed-key null (grouped by bits) ...")
NULLPOOL = defaultdict(list)
path = os.path.join(os.path.dirname(__file__), "constructed_keys_1to160_100k_exact.csv")
with open(path) as f:
    for r in csv.DictReader(f):
        NULLPOOL[int(r["bits"])].append(int(r["d"]))
missing = [BITS[N] for N in KEYS if len(NULLPOOL.get(BITS[N],[]))<50]
print(f"  buckets with >=50 synthetic keys: {sum(1 for b in NULLPOOL if len(NULLPOOL[b])>=50)}; "
      f"real-key bit-lengths under-covered: {sorted(set(missing))}\n")

rng = random.Random(0xE15E)
def null_keyset():
    out={}
    for N in KEYS:
        pool = NULLPOOL.get(BITS[N])
        out[N] = rng.choice(pool) if pool else rng.randrange(1<<(BITS[N]-1), 1<<BITS[N])
    return out

# ---- Eisenstein statistics over a keyset ----
def chi3_split_frac(ks):      # #{d == 1 mod 3}  (split residue)
    return sum(1 for N in ks if ks[N]%3==1)
def chi3_inert_frac(ks):
    return sum(1 for N in ks if ks[N]%3==2)
def split_divsum(ks):         # total split-prime divisors across keys
    return sum(count_div(ks[N], SPLIT) for N in ks)
def inert_divsum(ks):
    return sum(count_div(ks[N], INERT) for N in ks)
def v3_sum(ks):
    return sum(v(ks[N],3) for N in ks)
def v3_sum_dm(ks):
    return sum(v(ks[N]-(1<<(BITS[N]-1)),3) for N in ks)
def split_minus_inert(ks):    # net curve-resonance: split divisors minus inert
    return sum(count_div(ks[N],SPLIT)-count_div(ks[N],INERT) for N in ks)

STATS = {
    "chi3 split (d==1 mod3)":  chi3_split_frac,
    "chi3 inert (d==2 mod3)":  chi3_inert_frac,
    "split-prime divisors":    split_divsum,
    "inert-prime divisors":    inert_divsum,
    "split MINUS inert":       split_minus_inert,
    "v3(d) sum":               v3_sum,
    "v3(d-A) sum":             v3_sum_dm,
}
B = 5000
print(f"=== Thread C (Eisenstein / curve-native), null=100k, B={B} ===")
print(f"{len(SPLIT)} split primes, {len(INERT)} inert primes < {PB}\n")
print(f"{'statistic':<26} {'observed':>10} {'null-mean':>11} {'p(2-sided)':>12}")
null_cache = [null_keyset() for _ in range(B)]
for name, fn in STATS.items():
    obs = fn(D)
    vals = [fn(ks) for ks in null_cache]
    mean = sum(vals)/len(vals)
    ge = sum(1 for x in vals if x>=obs); le = sum(1 for x in vals if x<=obs)
    p2 = 2*min(ge,le)/len(vals)
    print(f"{name:<26} {obs:>10} {mean:>11.2f} {min(p2,1.0):>12.4f}")

# ---- positive control: bias toward chi3=1 and split divisibility ----
print("\n[CTRL] planted keyset (d forced == 1 mod 3 AND * a split prime):")
def planted():
    out={}
    for N in KEYS:
        A=1<<(BITS[N]-1)
        base = rng.randrange(A, 1<<BITS[N])
        base -= base % 7                 # make divisible by 7 (split)
        while base % 3 != 1: base += 7
        if base < A: base = A + (A%7==0 and 0 or (7-A%7))
        out[N]=base
    return out
pk = planted()
for name in ("chi3 split (d==1 mod3)","split MINUS inert"):
    fn=STATS[name]; obs=fn(pk)
    vals=[fn(ks) for ks in null_cache]
    ge=sum(1 for x in vals if x>=obs)
    print(f"   {name:<24} obs {obs:>5}  p(>=) {ge}/{B}={ge/B:.4f} -> {'FIRES' if ge/B<0.01 else 'no'}")
