import random, math
from fractions import Fraction as F
n = 8
def circq(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def run(ds, maxsteps=400):
    m=min(ds); t0=F(1,n)/m; t=t0; rows=[]
    for _ in range(maxsteps):
        iw=[d for d in ds if circq(d*t) < F(1,n)]
        if not iw: return rows, True, t0, t
        best=None
        for d in iw:
            N=round(d*t); nxt=(F(N)+F(1,n))/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d,N)
        if best is None: return rows, False, t0, t
        nxt,d,N=best
        rows.append((d,t,N)); t=nxt
    return rows, False, t0, t

# THREE questions.
# Q1. Is min-over-cascade the right statistic?  In (i) the depth enters PER TERM,
#     weighted by 1/s_j:      log G <= sum_j (2 - 8 delta_j)/s_j.
#     So the operative quantity is the 1/s-WEIGHTED MEAN of delta, not the min.
# Q2. What does the composed constant do when the TRUE deltas are used instead of
#     the pessimal delta = 0 that tight.py silently assumed by writing the literal 2?
# Q3. Does (iii) sum(1/s) <= (k/6) log G actually hold in the data?
rng=random.Random(97)
c_eff=[]; c_min=[]; true_ratio=[]; lap=[]; comp_eff=[]; viol_iii=0; tot=0
for _ in range(30000):
    ds=sorted(F(x) for x in rng.sample(range(1,100),7))
    rows,arr,t0,tf = run(ds)
    if not arr or len(rows)<4: continue
    G=float(tf/t0)
    if G<=1.0001: continue
    tot+=1
    d_,t_,N_=zip(*rows)
    dl=[float(d*t-N)+1/8 for d,t,N in rows]
    s =[float(8*d*t) for d,t,N in rows]
    S =sum(1/x for x in s)
    W =sum(dd/ss for dd,ss in zip(dl,s))/S          # 1/s-weighted mean depth
    c_eff.append(W); c_min.append(min(dl))
    lap.append(S/math.log(G))
    # true (i) ratio: sum (2-8 delta_j)/s_j  over  log G
    tr=sum((2-8*dd)/ss for dd,ss in zip(dl,s))/math.log(G)
    true_ratio.append(tr)
    comp_eff.append((2-8*W)*S/math.log(G))
    if S > (7/6)*math.log(G): viol_iii+=1
for nm,v in (("weighted-mean depth c_eff",c_eff),("min depth over cascade",c_min),
             ("lap ratio  sum(1/s)/logG",lap),
             ("TRUE (i) ratio  sum((2-8d)/s)/logG",true_ratio),
             ("composed with c_eff",comp_eff)):
    v=sorted(v)
    print(f"{nm:38s} min {v[0]:8.4f}  1% {v[len(v)//100]:8.4f}  med {v[len(v)//2]:8.4f}  max {v[-1]:8.4f}")
print()
print(f"cascades {tot};  (iii) sum(1/s) <= (k/6)logG violated in {viol_iii} ({viol_iii/tot:.4f})")
print(f"TRUE (i) ratio < 1 in : {sum(1 for x in true_ratio if x<1)} of {tot}   <-- must be 0, it is log(1+x)<=x")
print(f"composed-with-c_eff < 1 in : {sum(1 for x in comp_eff if x<1)} of {tot}")
