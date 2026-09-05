#!/usr/bin/env python3
# Steps 4-5 of PREREG_diffset_cubic_cmvanishing_v1.md
# Apply: controls + decision. Compute E3(X'_real) on the 82 real E'-derived X-coords,
# assert forced-structure, run planted-firing control, run cross-check regen, decide vs frozen [L',U'].

import csv, json, random, time
import numpy as np
try:
    from gmpy2 import mpz, powmod
    def cube_class(z):
        r = int(powmod(mpz(z), (P-1)//3, P))
        return 0 if r==1 else (1 if r==BETA else (2 if r==BETA2 else -1))
    FAST=True
except Exception:
    def cube_class(z):
        r = pow(z, (P-1)//3, P)
        return 0 if r==1 else (1 if r==BETA else (2 if r==BETA2 else -1))
    FAST=False

BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
BETA2= pow(BETA,2,P)

def E3_of(xs):
    a=b=c=0
    n=len(xs)
    for j in range(n):
        xj=xs[j]
        for k in range(j+1,n):
            cl=cube_class((xj-xs[k])%P)
            if cl==0: a+=1
            elif cl==1: b+=1
            elif cl==2: c+=1
            else: raise ValueError("cubic class undefined")
    return a,b,c, a*a+b*b+c*c-a*b-b*c-c*a

# load frozen null + region
null = np.load(f"{BASE}/diffset_cubic_Eprime_frozen_null_v1.npy", allow_pickle=True).astype(object)
null = [int(v) for v in null]
with open(f"{BASE}/diffset_cubic_Eprime_frozen_meta_v1.json") as f:
    FM = json.load(f)
L_PRIME = int(FM["L_prime"]); U_PRIME = int(FM["U_prime"])
print(f"frozen null: n={len(null)} mean={sum(null)/len(null):.1f}  region [L',U']=[{L_PRIME},{U_PRIME}]  alpha={FM['alpha_achieved']}", flush=True)
print(f"secp region (for reference, NOT used): [84, 11997]; E3(secp real)=13125", flush=True)

# ===== STEP 4a: real 82 E3 on E' =====
real=[]
with open(f"{BASE}/solved_puzzles_xy_Eprime.csv") as f:
    for r in csv.DictReader(f): real.append((int(r["bits"]), int(r["X_Eprime"],16)))
real.sort(key=lambda t:t[0])
xs_real=[x for _,x in real]
assert len(xs_real)==82
a,b,c,E3_real = E3_of(xs_real)
print(f"\n########## STEP 4a: REAL 82 on E' ##########", flush=True)
print(f"class counts (a,b,c) = ({a},{b},{c})  sum={a+b+c} (must=3321)", flush=True)
print(f"E3'(real) = {E3_real}   E3' mod 3 = {E3_real%3} (forced 0)", flush=True)
# CONTROL 1: forced structure
assert a+b+c==3321, "FORCED-STRUCTURE FAIL: sum != 3321 (path bug)"
assert E3_real%3==0, "FORCED-STRUCTURE FAIL: E3 not divisible by 3 (path bug)"
print(f"CONTROL 1 (forced-structure): FIRES (sum=3321, E3 mod 3=0)", flush=True)
# deviations from uniform (3321/3 = 1107 each)
print(f"  deviations from uniform (1107 each): ({a-1107},{b-1107},{c-1107})", flush=True)

# ===== STEP 4b: planted-firing control =====
# Concentration plant eps: reassign eps*3321 pairs to one class. Must reject-high at eps=0.05 with power >= 0.9.
print(f"\n########## STEP 4b: PLANTED-FIRING CONTROL ##########", flush=True)
real_bits=[bb for bb,_ in real]
pool={}
with open(f"{BASE}/constructed_keys_Eprime_100k.csv") as f:
    for r in csv.DictReader(f):
        if not r["X_Eprime"]: continue
        pool.setdefault(int(r["bits"]),[]).append(int(r["X_Eprime"],16))
random.seed(12345)
def planted_E3(eps):
    """take a null draw, then reassign eps*3321 of its pairs to class 0 (concentration)."""
    xs=[random.choice(pool[bb]) for bb in real_bits]
    # recompute (a,b,c) with eps*3321 forced into class 0
    pairs=[]
    for j in range(82):
        for k in range(j+1,82):
            cl=cube_class((xs[j]-xs[k])%P)
            pairs.append(cl)
    n_pairs=len(pairs)  # 3321
    n_force=int(eps*n_pairs)
    # force the first n_force pairs to class 0
    forced=pairs[:]
    random.shuffle(forced)
    forced[:n_force]=[0]*n_force
    aa=bb_=cc=0
    for cl in forced:
        if cl==0: aa+=1
        elif cl==1: bb_+=1
        else: cc+=1
    return aa*aa+bb_*bb_+cc*cc-aa*bb_-bb_*cc-cc*aa
EPS=0.05; N_PLANT=500
rejects=0
for _ in range(N_PLANT):
    e=planted_E3(EPS)
    if e>U_PRIME: rejects+=1
power_05 = rejects/N_PLANT
print(f"planted eps={EPS}: {rejects}/{N_PLANT} reject-high -> power={power_05:.3f} (target >=0.9)", flush=True)
if power_05 < 0.9:
    print(f"CONTROL 2 (planted-firing): DOES NOT FIRE (power {power_05:.3f} < 0.9) -- TEST VOID", flush=True)
    print(f"*** INSTRUMENT FAILURE, NOT A NULL RESULT. Record and stop. ***", flush=True)
    sys.exit(1)
print(f"CONTROL 2 (planted-firing): FIRES (power {power_05:.3f} >= 0.9 at eps=0.05)", flush=True)

# ===== STEP 4c: cross-check regen =====
print(f"\n########## STEP 4c: CROSS-CHECK REGEN ##########", flush=True)
random.seed(4242)
NT = 2000 if FAST else 300
regen=[]
for _ in range(NT):
    xs=[random.choice(pool[bb]) for bb in real_bits]
    regen.append(E3_of(xs)[3])
regen.sort()
m=sum(regen)/len(regen)
print(f"regen n={NT} (seed 4242): mean={m:.1f}  2.5%={regen[int(0.025*NT)]}  50%={regen[int(0.5*NT)]}  97.5%={regen[int(0.975*NT)]}", flush=True)
print(f"  (frozen null: mean={sum(null)/len(null):.1f}, 2.5%={null[int(0.025*len(null))]}, 50%={null[int(0.5*len(null))]}, 97.5%={null[int(0.975*len(null))]})", flush=True)
print(f"  consistent if regen quantiles are within sampling noise of frozen.", flush=True)

# ===== STEP 5: DECISION =====
print(f"\n########## STEP 5: DECISION ##########", flush=True)
print(f"frozen region [L',U'] = [{L_PRIME}, {U_PRIME}]", flush=True)
print(f"E3'(real) = {E3_real}", flush=True)
ge = sum(1 for v in null if v>=E3_real)
le = sum(1 for v in null if v<=E3_real)
p_two = min((ge+1)/(len(null)+1), (le+1)/(len(null)+1))*2
pct = le/len(null)*100
if E3_real > U_PRIME:
    decision = "REJECT-HIGH (concentration)"
    reading = "d-DRIVEN: anomaly survives curve swap -> 82 d's carry cubic structure independent of curve"
elif E3_real < L_PRIME:
    decision = "REJECT-LOW (over-uniformity)"
    reading = "over-uniformity on E' (CM supplied the high-E3 bias on secp); characterize, do not close"
else:
    decision = "FAIL-TO-REJECT"
    reading = "CM-DRIVEN: anomaly does not survive curve swap -> E3 secp anomaly is a j=0 curve fingerprint"
print(f"decision: {decision}", flush=True)
print(f"  #(null>=E3')={ge}  #(null<=E3')={le}  two-sided rank p ~ {p_two:.4f}", flush=True)
print(f"  E3' at ~{pct:.1f}th percentile of E' null", flush=True)
print(f"  reading: {reading}", flush=True)
print(f"\nsecp E3(real)=13125 was at 98.4th pct of secp null (p~0.033).", flush=True)
print(f"E'  E3(real)={E3_real} is at {pct:.1f}th pct of E' null (p~{p_two:.3f}).", flush=True)
