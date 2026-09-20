from fractions import Fraction as F
import math
N=8; THR=F(1,N)
def frac(x): return x-(x.numerator//x.denominator)
def cd(x): f=frac(x); return min(f,1-f)
def cascade(ds):
    m=min(ds); t=F(1)/(N*m); w=[]
    while True:
        best=None; inway=[]
        for d in ds:
            if cd(d*t)<THR:
                inway.append(d)
                Q=math.ceil(d*t-THR); op=(F(Q)+THR)/d
                if best is None or op>best[0]: best=(op,d,Q)
        if best is None: return t,m,w
        w.append((best[1],best[2],len(inway))); t=best[0]
for name,v,k in [("28-move",[27,70,107,137,159,188,344,393],393),
                 ("second-lap",[1,31,75,97,128,160,176,225],1)]:
    ds=sorted(F(abs(x-k)) for x in v if x!=k)
    m=min(ds); t,_,w=cascade(ds)
    idx={d:i for i,d in enumerate(ds)}
    seq=[idx[d] for d,_,_ in w]
    print(f"\n{name}: setter index per move (0=nearest .. 6=farthest), {len(w)} moves")
    print("  ",seq)
    print("   laps  ",[q for _,q,_ in w])
    print("   #in-the-way at each step:",[c for _,_,c in w])
    # how often does the same runner set twice in a row / return after k others
    rets=[]
    last={}
    for j,i in enumerate(seq):
        if i in last: rets.append(j-last[i])
        last[i]=j
    print(f"   gaps between a runner's consecutive settings: {rets}")
    print(f"   distinct runners setting: {len(set(seq))}  max #in-way: {max(c for _,_,c in w)}")
