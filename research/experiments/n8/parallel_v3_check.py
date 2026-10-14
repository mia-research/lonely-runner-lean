"""Check the parallel session's three new structural claims.
 A  d_min sets AT MOST 1 move, ever.
 B  minimum return gap between moves by the same setter is >= 2 (>= 4 in K=28).
 C  tau = d_min . t* lies in [1,2) -- arrival in the 2nd relative lap.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def run(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None,None
    t=TH/min(ds); seq=[]
    for _ in range(200000):
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return seq,t
        t,s=max((nextOp(d,t),d) for d in b); seq.append(s)
    return None,None
DEEP={"23-move":[30,74,96,127,159,175,224],"28-move":[49,205,234,256,286,323,366],
      "27 banded":[28,69,95,123,154,172,220],"27 banded2":[55,131,181,233,293,329,419]}
print("(A) does d_min ever set >= 2 moves?")
rng=random.Random(808); worst=0; n=0; witness=None
for _ in range(6000):
    v=speeds(rng.sample(range(1,120),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        seq,_=run(ds)
        if seq is None: continue
        n+=1; k=sum(1 for s in seq if s==min(ds))
        if k>worst: worst,witness=k,(ds,seq)
print(f"    {n} cascades; max times d_min sets a move: {worst}")
if worst>=2: print(f"      witness {witness[0]}  seq {[int(x) for x in witness[1]]}")
for name,ds in DEEP.items():
    seq,_=run(ds); print(f"    {name}: d_min={min(ds)} sets {sum(1 for s in seq if s==min(ds))} move(s)")

print("\n(B) minimum return gap between consecutive moves by the same setter")
for name,ds in DEEP.items():
    seq,_=run(ds); pos={}
    for j,s in enumerate(seq): pos.setdefault(int(s),[]).append(j)
    gaps=[b-a for p in pos.values() for a,b in zip(p,p[1:])]
    print(f"    {name}: min gap {min(gaps)}  all gaps {sorted(gaps)}")

print("\n(C) tau = d_min . t*  -- in [1,2)?")
for name,ds in DEEP.items():
    seq,t=run(ds); tau=F(min(ds))*t
    print(f"    {name}: tau = {tau} = {float(tau):.6f}  R = {float(8*tau):.4f}  "
          f"{'in [1,2)' if 1<=tau<2 else 'OUTSIDE [1,2)'}")
rng=random.Random(99); out=Counter(); mx=0; mn=9
for _ in range(4000):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        seq,t=run(ds)
        if seq is None: continue
        tau=float(F(min(ds))*t); out[floor(tau)]+=1; mx=max(mx,tau); mn=min(mn,tau)
print(f"    over {sum(out.values())} random subjects: floor(tau) distribution {dict(sorted(out.items()))}")
print(f"      min tau {mn:.6f}   max tau {mx:.6f}")
print(f"      -> tau in [1,2) universally? {'YES' if set(out)=={1} else 'NO'}")
print("\n(D) do the cited Lean lemmas exist?")
import subprocess
for nm in ("no_return_after_faster","no_four_alternation","no_return_after_few_faster"):
    r=subprocess.run(["grep","-rl",nm,"LonelyRunner/LonelyRunner/"],capture_output=True,text=True)
    print(f"    {nm}: {'FOUND in '+r.stdout.strip().splitlines()[0] if r.stdout.strip() else 'NOT FOUND'}")
