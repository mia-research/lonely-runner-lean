#!/usr/bin/env python3
"""
METHOD 2 (replaces per-key marginals): joint residue-clustering of the SET.

Idea: a shared generator or a selection filter leaves relations BETWEEN keys, not a
property on each key. If many keys share a residue mod some m, the SET clusters at m
(and their pairwise differences are divisible by m). Base-10 roundness is just the
m=10^k special case; this scans ALL moduli.

Statistic (exact integer): T(m) = sum_c (#keys with d == c mod m)^2  (collision count;
higher = more clustered). Null = the 100k constructed keys, matched by bit-length.
Multiple testing: minP permutation correction -- reference distribution per m from one
null pool, min-p null distribution from a disjoint pool. No float in the signal path
(residues and counts are integers; p-values are integer ratios).
Positive control: keys clustered mod 97 must be detected at m=97 with corrected p.
"""
import csv, os, random
from collections import defaultdict, Counter
from reset_common import load_solved

solved = load_solved()
KEYS = sorted(solved)
BITS = {N: solved[N]["bits"] for N in KEYS}
Dreal = {N: solved[N]["d"] for N in KEYS}

# moduli to scan: dense small + power families + a few curve-related
MODULI = list(range(2, 201))
for base in (2,3,5,10):
    e=2
    while base**e <= 10**7:
        MODULI.append(base**e); e+=1
MODULI += [7,13,19,31,37,149,631]       # curve/(n-1) related
MODULI = sorted(set(MODULI))

def Tvec(dmap):
    """T(m) for all m in MODULI over the keyset dmap."""
    out = {}
    ds = list(dmap.values())
    for m in MODULI:
        cnt = Counter(d % m for d in ds)
        out[m] = sum(v*v for v in cnt.values())
    return out

# null pool from 100k
pool = defaultdict(list)
with open(os.path.join(os.path.dirname(__file__),
        "constructed_keys_1to160_100k_exact.csv")) as f:
    for r in csv.DictReader(f):
        pool[int(r["bits"])].append(int(r["d"]))
rng = random.Random(0x105E7)
def null_keyset():
    return {N: (rng.choice(pool[BITS[N]]) if pool.get(BITS[N])
               else rng.randrange(1<<(BITS[N]-1),1<<BITS[N])) for N in KEYS}

N_REF, N_CAL = 3000, 1500
print("=== METHOD 2: joint residue-clustering (minP-corrected) ===")
print(f"{len(MODULI)} moduli scanned; null=100k; ref={N_REF}, cal={N_CAL}\n")

ref = [Tvec(null_keyset()) for _ in range(N_REF)]
def pval_per_m(Tobs):
    """right-tail p per modulus vs the reference pool."""
    return {m: (sum(1 for t in ref if t[m] >= Tobs[m]) + 1) / (N_REF + 1) for m in MODULI}

def report(label, Tobs):
    p = pval_per_m(Tobs)
    minp = min(p.values())
    argm = min(p, key=lambda m: p[m])
    # minP null distribution (disjoint calibration pool)
    cal_minps = []
    for _ in range(N_CAL):
        pc = pval_per_m(Tvec(null_keyset()))
        cal_minps.append(min(pc.values()))
    corrected = (sum(1 for x in cal_minps if x <= minp) + 1) / (N_CAL + 1)
    print(f"{label}: most-clustered modulus m={argm} (uncorrected p={minp:.4f}, "
          f"T_obs={Tobs[argm]}); minP-corrected p = {corrected:.4f}")
    # show top 5 moduli by uncorrected p
    top = sorted(p.items(), key=lambda kv: kv[1])[:5]
    print("   top moduli (uncorrected): " +
          ", ".join(f"m={m}:p={pv:.3f}" for m,pv in top))
    return corrected

corr_real = report("[REAL]", Tvec(Dreal))

# ---- positive control ----
def clustered_keys(mstar=97):
    out={}
    for N in KEYS:
        A=1<<(BITS[N]-1)
        base=rng.randrange(A,1<<BITS[N])
        base -= base % mstar               # force d == 0 mod 97
        out[N]= base if base>=A else A+(mstar-(A%mstar))%mstar
    return out
print()
corr_ctrl = report("[CTRL m=97]", Tvec(clustered_keys(97)))
print(f"\n control fired: {corr_ctrl < 0.01}")
print(f"\n REAL corrected p = {corr_real:.4f}  -> "
      + ("clustering detected, investigate" if corr_real < 0.05
         else "no joint residue clustering at any scanned modulus beyond the matched null"))
