#!/usr/bin/env python3
# AUDIT the fired cubic E3 reject: jackknife stability, class attribution,
# and whether the excess survives on the high-bit keys (the ones that can differ from control).
import csv, random
from gmpy2 import mpz, powmod

P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
BETA2= pow(BETA,2,P)
E   = (P-1)//3
BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"

def cc(z):
    r=int(powmod(mpz(z%P),E,P)); return 0 if r==1 else (1 if r==BETA else 2)
def E3_of(xs):
    a=b=c=0; n=len(xs)
    for j in range(n):
        xj=xs[j]
        for k in range(j+1,n):
            t=cc(xj-xs[k])
            if t==0:a+=1
            elif t==1:b+=1
            else:c+=1
    return a,b,c,a*a+b*b+c*c-a*b-b*c-c*a

real=[]
with open(f"{BASE}/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f):
        real.append((int(r["bits"]),int(r["X"],16)))
real.sort(key=lambda t:t[0])
bits=[b for b,_ in real]; xs=[x for _,x in real]
a,b,c,E3=E3_of(xs)
print(f"FULL: (a,b,c)=({a},{b},{c})  E3={E3}", flush=True)
chi2=( (a-1107)**2+(b-1107)**2+(c-1107)**2 )/1107
print(f"class excess vs 1107: a{a-1107:+d} b{b-1107:+d} c{c-1107:+d}   chi2(df2)={chi2:.2f}", flush=True)

# ---- jackknife drop-one ----
jk=[]
for i in range(82):
    xi=xs[:i]+xs[i+1:]
    jk.append((E3_of(xi)[3], bits[i]))
vals=sorted(v for v,_ in jk)
# scaled reject threshold for 81 keys (E[E3] ∝ #pairs): 11997 * C(81,2)/C(82,2)
thr81=11997*(81*80//2)/(82*81//2)
above=sum(1 for v,_ in jk if v>thr81)
print(f"\nJACKKNIFE drop-one E3 (81 keys): min={vals[0]} med={vals[41]} max={vals[-1]}", flush=True)
print(f"  scaled 97.5% thr(81)~{thr81:.0f};  #drops still above = {above}/82  (fragile if small)", flush=True)
# most influential drops (largest E3 reduction = that key drives the excess)
jk_by_drop=sorted(jk)  # smallest resulting E3 = biggest reducer
print(f"  keys whose removal most REDUCES E3 (drive the excess): "
      f"{[(bt,v) for v,bt in jk_by_drop[:5]]}", flush=True)
print(f"  keys whose removal most INCREASES E3: {[(bt,v) for v,bt in jk_by_drop[-3:]]}", flush=True)

# ---- subset: high-bit keys only (bits>=11), with its own matched null ----
hi=[(bt,x) for bt,x in zip(bits,xs) if bt>=11]
hibits=[bt for bt,_ in hi]; hixs=[x for _,x in hi]
E3_hi=E3_of(hixs)[3]
pool={}
with open(f"{BASE}/constructed_keys_1to160_100k.csv") as f:
    for r in csv.DictReader(f):
        bb=int(r["bits"])
        if bb>=11: pool.setdefault(bb,[]).append(int(r["X"],16))
random.seed(77)
NT=1000
null_hi=sorted(E3_of([random.choice(pool[bt]) for bt in hibits])[3] for _ in range(NT))
ge=sum(1 for v in null_hi if v>=E3_hi)
print(f"\nHIGH-BIT SUBSET (bits>=11, n={len(hi)}, {len(hi)*(len(hi)-1)//2} pairs):", flush=True)
print(f"  E3_hi={E3_hi}  null(1000): 50%={null_hi[500]} 97.5%={null_hi[974]}  #null>=E3_hi={ge}  ~pctile={100*(NT-ge)/NT:.1f}", flush=True)
print(f"  -> {'still upper-tail' if ge<=25 else 'NOT significant on high-bit subset (excess was low-bit/shared)'}", flush=True)
