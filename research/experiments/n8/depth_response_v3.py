"""v2 refuted the obvious claim: on c in [25,31] the initial blocker set is identical (only 224),
yet depth is 18,18,18,18,18,23,18.  c = 30 is a SPIKE inside a plateau.

So the initial conditions do not determine depth; something later in the trajectory does.  Trace
c = 29, 30, 31 side by side and find where they diverge and by how much.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor, gcd
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def trace(ds):
    ds=[F(d) for d in ds]; t=TH/min(ds); out=[]
    for _ in range(4000):
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return out
        tn,setter=max((nextOp(d,t),d) for d in b)
        D=1/(8*t)
        out.append((int(setter), float(D), float(tn/t)))
        t=tn
    return out
REST=[74,96,127,159,175,224]
tr={c: trace([c]+REST) for c in (29,30,31)}
print(f"  depths: c=29 -> {len(tr[29])},  c=30 -> {len(tr[30])},  c=31 -> {len(tr[31])}\n")
print(f"  {'step':>4} | {'c=29 setter':>12} {'D':>9} | {'c=30 setter':>12} {'D':>9} | {'c=31 setter':>12} {'D':>9}")
print("  " + "-"*78)
for i in range(max(len(tr[29]),len(tr[30]),len(tr[31]))):
    row=f"  {i:>4} |"
    for c in (29,30,31):
        if i<len(tr[c]):
            s,D,lam=tr[c][i]; row+=f" {s:>12} {D:>9.4f} |"
        else:
            row+=f" {'--':>12} {'--':>9} |"
    print(row)
    if i>=14: 
        print("  ...")
        break
print("\n  where do they first differ?")
for a,b in ((29,30),(30,31)):
    k=0
    while k<min(len(tr[a]),len(tr[b])) and tr[a][k][0]==tr[b][k][0]: k+=1
    print(f"    c={a} vs c={b}: first differing step = {k}"
          + (f"  (setters {tr[a][k][0]} vs {tr[b][k][0]})" if k<min(len(tr[a]),len(tr[b])) else ""))
print("\n  arithmetic of the three minima:")
for c in (29,30,31):
    print(f"    c={c}: factors of c = {[p for p in range(2,c+1) if c%p==0 and all(p%q for q in range(2,p))]}, "
          f"gcd(c, each of {REST}) = {[gcd(c,r) for r in REST]}")
