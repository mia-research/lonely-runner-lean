#!/usr/bin/env python3
# Step 3 of PREREG_diffset_cubic_cmvanishing_v1.md
# FREEZE the E' null: 10,000 resamples of 82 from the constructed pool, compute E3 for each.
# Region [L', U'] = [A'[249], A'[9750]] (two-sided alpha ~ 0.05). Seed frozen at 20260728.
#
# THIS IS THE LOAD-BEARING GATE STEP. The null is built ONLY from the constructed pool
# (known-MT19937 d's mapped to E'); the real 82 E' values are NOT touched here.
# The secp frozen region [84, 11997] is NOT reused -- E' gets its own region from its own null.

import csv, json, random, hashlib, time
import numpy as np
try:
    from gmpy2 import mpz, powmod
    def cube_class(z):
        r = int(powmod(mpz(z), (P-1)//3, P))
        return 0 if r==1 else (1 if r==BETA else (2 if r==BETA2 else -1))
    FAST = True
except Exception:
    def cube_class(z):
        r = pow(z, (P-1)//3, P)
        return 0 if r==1 else (1 if r==BETA else (2 if r==BETA2 else -1))
    FAST = False

BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
BETA2= pow(BETA,2,P)
SEED = 20260728
N_NULL = 10000

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

# ---- real 82 bit-lengths (for matched resampling) ----
real_bits=[]
with open(f"{BASE}/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f): real_bits.append(int(r["bits"]))
real_bits.sort()
print(f"real 82 bit-lengths: min={min(real_bits)} max={max(real_bits)} n={len(real_bits)}", flush=True)

# ---- constructed pool, indexed by bit-length ----
pool={}
n_pool=0
with open(f"{BASE}/constructed_keys_Eprime_100k.csv") as f:
    for r in csv.DictReader(f):
        if not r["X_Eprime"]: continue   # skip any (extremely unlikely) identity
        pool.setdefault(int(r["bits"]),[]).append(int(r["X_Eprime"],16))
        n_pool+=1
print(f"constructed pool on E': {n_pool} keys across {len(pool)} bit-lengths", flush=True)
missing=[b for b in real_bits if b not in pool or len(pool[b])==0]
assert not missing, f"missing bit-lengths in pool: {missing}"

# ---- freeze null ----
print(f"\nFREEZING null: {N_NULL} resamples, seed={SEED}, fast={FAST}", flush=True)
random.seed(SEED)
t0=time.time()
null_E3=[]
null_abc=[]
for i in range(N_NULL):
    xs=[random.choice(pool[bb]) for bb in real_bits]
    a,b,c,E3 = E3_of(xs)
    null_E3.append(E3)
    null_abc.append((a,b,c))
    if (i+1) % 500 == 0:
        el=time.time()-t0
        print(f"  {i+1}/{N_NULL}  ({el:.1f}s, {(i+1)/el:.1f}/s)", flush=True)
el=time.time()-t0
print(f"null built in {el:.1f}s", flush=True)

null_E3.sort()
n=len(null_E3)
# region: lower/upper 0.025 tails
L = null_E3[249]      # A[249]   (index 249 -> 250/10000 = 0.025 lower tail)
U = null_E3[9750]     # A[9750]  (index 9750 -> 250/10000 = 0.025 upper tail)
mean = sum(null_E3)/n
all_mod3 = all(v%3==0 for v in null_E3)
print(f"\nnull E3: n={n} mean={mean:.1f} min={null_E3[0]} max={null_E3[-1]}", flush=True)
print(f"  2.5%={null_E3[int(0.025*n)]}  50%={null_E3[int(0.5*n)]}  97.5%={null_E3[int(0.975*n)]}", flush=True)
print(f"  all_mod3_0={all_mod3}  (forced-structure bug-check)", flush=True)
print(f"\n########## FROZEN REGION [L', U'] = [{L}, {U}] ##########", flush=True)
# alpha achieved = fraction of null outside [L,U] (should be ~0.05)
alpha = sum(1 for v in null_E3 if v < L or v > U) / n
print(f"achieved alpha = {alpha:.4f} (target ~0.05)", flush=True)

# ---- save artifacts ----
np.save(f"{BASE}/diffset_cubic_Eprime_frozen_null_v1.npy", np.array(null_E3, dtype=object))
meta = {
    "P": P, "BETA": BETA, "BETA2": BETA2,
    "seed": SEED, "N_null": N_NULL,
    "L_prime": int(L), "U_prime": int(U),
    "alpha_achieved": float(alpha),
    "null_mean": float(mean), "null_min": int(null_E3[0]), "null_max": int(null_E3[-1]),
    "null_p025": int(null_E3[int(0.025*n)]),
    "null_p50":  int(null_E3[int(0.5*n)]),
    "null_p975": int(null_E3[int(0.975*n)]),
    "all_mod3_0": bool(all_mod3),
    "Eprime_a": 1, "Eprime_b": 1,
    "Eprime_j": "44822744220896591776866187745298544975459348902828605434628742196609871486028",
    "Eprime_n_prime": 1735267482095677159220328300040520133145015240816313753,
    "pool_size": n_pool, "n_real_bits": len(real_bits),
    "prereg_sha256_at_freeze": hashlib.sha256(open(f"{BASE}/PREREG_diffset_cubic_cmvanishing_v1.md","rb").read()).hexdigest(),
}
with open(f"{BASE}/diffset_cubic_Eprime_frozen_meta_v1.json","w") as f:
    json.dump(meta, f, indent=2)
print(f"wrote diffset_cubic_Eprime_frozen_null_v1.npy + diffset_cubic_Eprime_frozen_meta_v1.json", flush=True)
print(f"\nNULL FROZEN. Region [{L}, {U}]. Real 82 E3 NOT yet computed.", flush=True)
