#!/usr/bin/env python3
# APPLY the frozen cubic difference-set energy test to the real 82. Exact integer path.
# Decision vs FROZEN region [84, 11997] (two-sided). Independent null cross-check.
import csv, random
import numpy as np
try:
    from gmpy2 import mpz, powmod
    def cube_class(z, P, B, B2):
        r = int(powmod(mpz(z), (P-1)//3, P))
        return 0 if r==1 else (1 if r==B else (2 if r==B2 else -1))
    FAST=True
except Exception:
    def cube_class(z, P, B, B2):
        r = pow(z, (P-1)//3, P)
        return 0 if r==1 else (1 if r==B else (2 if r==B2 else -1))
    FAST=False

P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
BETA2= pow(BETA,2,P)
BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
SCR  = "/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/c9342981-88ed-4087-91d0-dfebd9a02142/scratchpad"
L_FROZEN, U_FROZEN = 84, 11997

def E3_of(xs):
    a=b=c=0
    n=len(xs)
    for j in range(n):
        xj=xs[j]
        for k in range(j+1,n):
            cl=cube_class((xj-xs[k])%P, P, BETA, BETA2)
            if cl==0: a+=1
            elif cl==1: b+=1
            elif cl==2: c+=1
            else: raise ValueError("cubic class undefined (z=0?)")
    return a,b,c, a*a+b*b+c*c-a*b-b*c-c*a

# ---- REAL 82 ----
real=[]
with open(f"{BASE}/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f):
        real.append((int(r["bits"]), int(r["X"],16)))
real.sort(key=lambda t:t[0])
xs_real=[x for _,x in real]
assert len(xs_real)==82
a,b,c,E3 = E3_of(xs_real)
print(f"[fast={FAST}]  APPLY cubic E3 to real 82", flush=True)
print(f"class counts (a,b,c) = ({a},{b},{c})  sum={a+b+c} (must=3321)", flush=True)
print(f"E3(real) = {E3}   E3 mod 3 = {E3%3} (forced 0 bug-check)", flush=True)
assert a+b+c==3321 and E3%3==0, "forced-structure check FAILED -> path bug"

# ---- FROZEN null ----
null = np.load(f"{SCR}/frozen_null_E3.npy").astype(object)  # int64 -> py int for exact
null = [int(v) for v in null]
n=len(null)
ge = sum(1 for v in null if v>=E3)   # #{null >= E3}
le = sum(1 for v in null if v<=E3)   # #{null <= E3}
p_two = min((ge+1)/(n+1), (le+1)/(n+1))*2   # two-sided-ish
snull=sorted(null)
print(f"\nfrozen null: n={n} mean={sum(null)/n:.1f} min/max={snull[0]}/{snull[-1]} all_mod3_0={all(v%3==0 for v in null)}", flush=True)
print(f"order-stat verify: A[249]={snull[249]} (=>L=84?)  A[9750]={snull[9750]} (=>U=11997?)", flush=True)
decision = "REJECT-HIGH (concentration)" if E3>U_FROZEN else ("REJECT-LOW (over-uniformity)" if E3<L_FROZEN else "FAIL-TO-REJECT")
print(f"\n########## DECISION (frozen rule) ##########", flush=True)
print(f"frozen region [L,U] = [{L_FROZEN}, {U_FROZEN}]  (reject if outside)", flush=True)
print(f"E3(real) = {E3}  ->  {decision}", flush=True)
print(f"#(null>=E3)={ge}  #(null<=E3)={le}   two-sided rank p ~ {p_two:.4f}", flush=True)
pct = le/n*100
print(f"E3 at ~{pct:.1f}th percentile of null", flush=True)

# ---- independent cross-check regen (fast gmpy2) ----
print(f"\n########## independent regen cross-check ##########", flush=True)
pool={}
with open(f"{BASE}/constructed_keys_1to160_100k.csv") as f:
    for r in csv.DictReader(f):
        pool.setdefault(int(r["bits"]),[]).append(int(r["X"],16))
real_bits=[bb for bb,_ in real]
random.seed(4242)
NT = 2000 if FAST else 300
regen=[]
for _ in range(NT):
    xs=[random.choice(pool[bb]) for bb in real_bits]
    regen.append(E3_of(xs)[3])
regen.sort()
m=sum(regen)/len(regen)
print(f"regen n={NT} (seed 4242) mean={m:.1f}  2.5%={regen[int(0.025*NT)]}  50%={regen[int(0.5*NT)]}  97.5%={regen[int(0.975*NT)]}", flush=True)
print(f"  (frozen: mean~3274, 2.5%=84, 50%=2268, 97.5%=11997  -> consistent if close)", flush=True)
