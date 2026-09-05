#!/usr/bin/env python3
# analyze_h5_restoration_v1.py -- H-5 cofactor RESTORATION, per PREREG decision rules.
# beta_induced = OLS slope of T1_induced on ln(c) (c>=2); within-curve c-label permutation null.
# Plants: synthetic-slope (quo_conf:=quo_full*c -> beta~1), c=1 null (T1~0). Compare to beta_j0.
import json, math, random
from collections import defaultdict

recs=[json.loads(l) for l in open("h5_restoration_results_v1.jsonl")]
hdr=[r for r in recs if r.get("kind")=="header"][0]
beta_j0=hdr["beta_j0"]["beta_j0_samecurve"]
cells=[r for r in recs if r.get("kind")=="cell"]
# saturation guard
dropped=[r for r in cells if r.get("sat_conf")]
cells=[r for r in cells if not r.get("sat_conf")]
print("beta_j0(same-curve target)=%.4f  r2=%.3f | dropped(saturated)=%d"%(beta_j0,hdr["beta_j0"]["r2_same"],len(dropped)))

def ols(xs,ys):
    n=len(xs)
    if n<2: return float('nan'),float('nan'),float('nan'),float('nan')
    mx=sum(xs)/n; my=sum(ys)/n
    sxx=sum((x-mx)**2 for x in xs); sxy=sum((x-mx)*(y-my) for x,y in zip(xs,ys))
    b=sxy/sxx if sxx else float('nan'); a=my-b*mx
    resid=[y-(a+b*x) for x,y in zip(xs,ys)]
    se=(sum(r*r for r in resid)/((n-2)*sxx))**0.5 if (n>2 and sxx>0) else float('nan')
    ss=sum((y-my)**2 for y in ys); rr=sum(r*r for r in resid); r2=1-rr/ss if ss else float('nan')
    return b,a,se,r2

def fit_slope(cs, celllist):
    xs=[math.log(r["c"]) for r in celllist]; ys=[r["T1_induced"] for r in celllist]
    return ols(xs,ys)

for V in sorted({r["V"] for r in cells}):
    arm=[r for r in cells if r["V"]==V and r["c"]>=2]
    c1 =[r for r in cells if r["V"]==V and r["c"]==1]
    if len(arm)<3:
        print("|V|=%d: <3 confined cells"%V); continue
    b,a,se,r2=fit_slope(None,arm)
    # within-curve c-label permutation null
    bycurve=defaultdict(list)
    for r in arm: bycurve[(r["p"],r["A"],r["B"])].append(r)
    random.seed(20260830); B=10000; ge=0
    obs=b
    for _ in range(B):
        xs=[]; ys=[]
        for k,lst in bycurve.items():
            lncs=[math.log(r["c"]) for r in lst]; t1s=[r["T1_induced"] for r in lst]
            random.shuffle(t1s)
            xs+=lncs; ys+=t1s
        bp,_,_,_=ols(xs,ys)
        if bp>=obs-1e-12: ge+=1
    pv=(1+ge)/(1+B)
    # c=1 null plant
    c1_mean=sum(r["T1_induced"] for r in c1)/len(c1) if c1 else float('nan')
    # synthetic-slope plant: quo_conf := quo_full * c  => T1_synth = ln(c); slope must be ~1
    synth=[]
    for r in arm:
        lm_conf_s=math.log(sum(q*r["c"] for q in r["quo_full"])/len(r["quo_full"]))
        synth.append(dict(c=r["c"],T1_induced=lm_conf_s-r["lm_full"]))
    bs,_,_,_=fit_slope(None,synth)
    print("|V|=%d  N=%d  beta_induced=%.4f (SE %.4f) r2=%.3f  perm_p=%.4f | c=1 null T1=%.4f (n=%d) | synth-plant beta=%.3f | |b-b_j0|=%.3f"
          %(V,len(arm),b,se,r2,pv,c1_mean,len(c1),bs,abs(b-beta_j0)))

# pooled primary at |V|=6
print()
V=6
arm=[r for r in cells if r["V"]==V and r["c"]>=2]
if len(arm)>=3:
    b,a,se,r2=fit_slope(None,arm)
    within=abs(b-beta_j0)<=0.15
    print("PRIMARY |V|=6: beta_induced=%.4f  beta_j0=%.4f  |diff|=%.4f (tol 0.15: %s)  N=%d SE=%.4f"
          %(b,beta_j0,abs(b-beta_j0),"WITHIN" if within else "OUTSIDE",len(arm),se))
    print("  slope-1 (naive n2 law) excluded? |b-1|=%.3f  ->  %s"%(abs(b-1),"yes, ~sqrt(n2)" if abs(b-1)>0.3 else "no"))
    # verdict
    if len(arm)>=60 and within:
        print("  VERDICT: cofactor mechanism CONFIRMED prospectively (slope reproduced on cyclic curves).")
    elif len(arm)<60:
        print("  VERDICT: check N (need >=60 for full power); interpret with SE.")
