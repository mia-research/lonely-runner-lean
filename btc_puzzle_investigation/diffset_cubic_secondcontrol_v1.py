#!/usr/bin/env python3
# Control-2 (generator-agnostic): uniform random VALID secp curve x-coords.
# Build E3 null, validate it matches the MT null shape, apply frozen E3(real)=13125.
import csv, random
import numpy as np
from gmpy2 import mpz, powmod

P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
E3EXP=(P-1)//3
QUA  =(P-1)//2
BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
SCR  = "/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/c9342981-88ed-4087-91d0-dfebd9a02142/scratchpad"
random.seed(20260727)

def cc(z):
    r=int(powmod(mpz(z%P),E3EXP,P)); return 0 if r==1 else (1 if r==BETA else 2)
def is_valid_x(x):
    return int(powmod(mpz((x*x*x+7)%P),QUA,P))==1
def E3_of(xs):
    a=b=c=0; n=len(xs)
    for j in range(n):
        xj=xs[j]
        for k in range(j+1,n):
            t=cc(xj-xs[k])
            if t==0:a+=1
            elif t==1:b+=1
            else:c+=1
    return a*a+b*b+c*c-a*b-b*c-c*a
def rand_valid_x():
    while True:
        x=random.randrange(1,P)
        if is_valid_x(x): return x

# integrity: recompute E3(real)
real=[]
with open(f"{BASE}/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f): real.append(int(r["X"],16))
E3_real=E3_of(real)
print(f"E3(real) integrity recompute = {E3_real}  (expect 13125)", flush=True)

# Control-2 null: fresh 82 uniform valid curve x per trial
NT=10000
null=[]
for i in range(NT):
    xs=[rand_valid_x() for _ in range(82)]
    null.append(E3_of(xs))
    if (i+1)%2000==0: print(f"  ...{i+1}/{NT}", flush=True)
null.sort()
n=len(null); mean=sum(null)/n
lo=null[int(0.025*n)]; md=null[int(0.5*n)]; hi=null[int(0.975*n)]
print(f"\nControl-2 null (uniform valid curve x, n={n}): mean={mean:.1f} 2.5%={lo} 50%={md} 97.5%={hi}", flush=True)

# validity gate vs MT null
mt=np.load(f"{BASE}/diffset_cubic_frozen_null_E3_v1.npy"); mt=sorted(int(v) for v in mt)
mtmean=sum(mt)/len(mt); mthi=mt[int(0.975*len(mt))]
print(f"MT null (frozen):                             mean={mtmean:.1f}          97.5%={mthi}", flush=True)
gate = abs(mean-mtmean)/mtmean<0.05 and abs(hi-mthi)/mthi<0.10
print(f"VALIDITY GATE (Control-2 ~ MT null shape): {'PASS' if gate else 'FAIL -> mismatch is itself a finding'}", flush=True)

# frozen decision vs Control-2
ge=sum(1 for v in null if v>=E3_real); le=sum(1 for v in null if v<=E3_real)
p_two=min((ge+1)/(n+1),(le+1)/(n+1))*2
decision="REJECT-HIGH" if E3_real>hi else ("REJECT-LOW" if E3_real<lo else "FAIL-TO-REJECT")
print(f"\n########## DECISION vs Control-2 (frozen rule) ##########", flush=True)
print(f"E3(real)={E3_real}  Control-2 region [{lo},{hi}]  -> {decision}", flush=True)
print(f"  percentile ~{100*(n-ge)/n:.1f}   two-sided rank p ~ {p_two:.4f}", flush=True)
print(f"  (MT gave: REJECT-HIGH, 98.4th pct, p~0.033)", flush=True)
