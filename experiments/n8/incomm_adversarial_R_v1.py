"""Adversarial search for large R = 8*d_min*t with GENUINELY INCOMMENSURABLE disparities.
Speeds in Q(sqrt2): v = a + b*sqrt2, a,b rational.  Exact arithmetic for every verdict.
Incommensurability is VERIFIED per subject (disparity vectors (p,q) must span rank 2 --
rank 1 means all disparities are one common multiple and a period exists).
Benchmark: the commensurable record on file is R ~ 11.96 at S ~ 7.44.   2026-09-18."""
import sys, math, random, time
sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import ceil
from lattice_witness_irrational_v1 import sign, floor_q2

TH=F(1,8)
def mul(x,y): return (x[0]*y[0]+2*x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def inv(x):
    a,b=x; den=a*a-2*b*b; return (a/den,-b/den)
def sub(x,y): return (x[0]-y[0],x[1]-y[1])
def lt(x,y): return sign(*sub(x,y))<0
def fv(x): return float(x[0])+float(x[1])*math.sqrt(2)
def cd_lt(x):                      # circle distance < 1/8 ?
    k=floor_q2(*x); fr=sub(x,(F(k),F(0)))
    return lt(fr,(TH,F(0))) or lt((1-TH,F(0)),fr)
def nextOp(d,t):
    dt=mul(d,t); k=ceil(fv(dt)-0.125)
    if k<0: k=0
    while lt((F(k)+TH,F(0)), dt): k+=1
    while k>0 and not lt((F(k-1)+TH,F(0)), dt): k-=1
    return mul((F(k)+TH,F(0)), inv(d))

def disparities(sp,i):
    ds=[]
    for j in range(len(sp)):
        if j==i: continue
        d=sub(sp[j],sp[i])
        s=sign(*d)
        if s==0: return None
        if s<0: d=(-d[0],-d[1])
        ds.append(d)
    return ds

def rank2(ds):
    """genuinely incommensurable iff the (p,q) vectors are not all parallel"""
    p0,q0=ds[0]
    return any(p0*q-q0*p!=0 for p,q in ds[1:])

MAXMOVES=400
def R_of(sp,i):
    ds=disparities(sp,i)
    if ds is None or not rank2(ds): return None
    dmin=min(ds,key=fv); dmax=max(ds,key=fv)
    t=mul((TH,F(0)),inv(dmin)); n=0
    while n<MAXMOVES:
        b=[d for d in ds if cd_lt(mul(d,t))]
        if not b:
            R=mul((F(8),F(0)),mul(dmin,t))
            return fv(R), fv(dmax)/fv(dmin), n
        t=max((nextOp(d,t) for d in b), key=fv)
        n+=1
    return None

def best_over_subjects(sp):
    best=None
    for i in range(8):
        r=R_of(sp,i)
        if r is None: continue
        if best is None or r[0]>best[0]: best=(r[0],r[1],r[2],i)
    return best

# ---- seeds: random, plus the known hard COMMENSURABLE cases pushed into Q(sqrt2)
HARD=[(27,70,107,137,159,188,344,393),
      (1,31,75,97,128,160,176,225),
      (11,21,22,23,26,34,35,40),
      (10,65,101,126,159,222,256,271)]
def rand_speeds(rng,N=60,D=10):
    a=sorted(rng.sample(range(0,N),8))
    return [(F(a[k]), F(rng.randint(0,D),D)) for k in range(8)]
def seed_from_hard(rng,D=10):
    base=rng.choice(HARD)
    return [(F(b), F(rng.randint(0,D),D)) for b in base]

def perturb(sp,rng,D=10):
    sp=list(sp); k=rng.randrange(8); a,b=sp[k]
    if rng.random()<0.5:
        a=a+rng.choice([-3,-2,-1,1,2,3])
        if a<0: a=-a
    else:
        b=b+F(rng.choice([-3,-2,-1,1,2,3]),D)
        if b<0: b=-b
    sp[k]=(a,b)
    return sp

t0=time.time(); rng=random.Random(20260918)
BEST=(0,0,0,None,None); evals=0
while time.time()-t0 < 420:
    cur = seed_from_hard(rng) if rng.random()<0.5 else rand_speeds(rng)
    c = best_over_subjects(cur); evals+=1
    if c is None: continue
    for _ in range(140):
        if time.time()-t0 > 420: break
        cand = perturb(cur,rng)
        r = best_over_subjects(cand); evals+=1
        if r is None: continue
        if r[0] >= c[0]:
            cur, c = cand, r
            if c[0] > BEST[0]:
                BEST=(c[0],c[1],c[2],c[3],[ (str(x[0]),str(x[1])) for x in cur ])
                print(f"  R={c[0]:.5f}  S={c[1]:.4f}  moves={c[2]}  subj={c[3]}  t+{time.time()-t0:.0f}s")
print()
print(f"evaluations: {evals}")
print(f"BEST INCOMMENSURABLE  R = {BEST[0]:.6f}   S = {BEST[1]:.4f}   moves = {BEST[2]}  subject idx {BEST[3]}")
print(f"  speeds (a, b) meaning a + b*sqrt2:")
for s in BEST[4]: print(f"    {s[0]} + {s[1]}*sqrt2")
print()
print("benchmark: commensurable record on file  R ~ 11.96  at S ~ 7.44")
