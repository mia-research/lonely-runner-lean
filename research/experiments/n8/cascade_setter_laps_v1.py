from fractions import Fraction as F
import math
N=8; THR=F(1,N)
def frac(x): return x-(x.numerator//x.denominator)
def cd(x): f=frac(x); return min(f,1-f)
def cascade(ds):
    m=min(ds); t=F(1)/(N*m); w=[]
    while True:
        best=None
        for d in ds:
            if cd(d*t)<THR:
                Q=math.ceil(d*t-THR); op=(F(Q)+THR)/d
                if best is None or op>best[0]: best=(op,d,Q)
        if best is None: return t,m,w
        w.append((best[1],best[2])); t=best[0]
v=[27,70,107,137,159,188,344,393]; k=393
ds=sorted(F(abs(x-k)) for x in v if x!=k)
t,m,w=cascade(ds)
print("global setter lap sequence:",[q for _,q in w])
per={}
for d,q in w: per.setdefault(d,[]).append(q)
print("\nper-runner setting laps (Certificate.laps_strictly_increase says these must strictly increase):")
ok=True
for d in sorted(per):
    seq=per[d]; inc=all(seq[i]<seq[i+1] for i in range(len(seq)-1))
    ok &= inc
    print(f"  d={str(d):>4}  u=d/m={float(d/m):5.2f}  laps={seq}  strictly increasing: {inc}")
print("\nall per-runner sequences strictly increasing:",ok)
print("distinct setters:",len(per),"of",len(ds),"  total moves:",len(w))
