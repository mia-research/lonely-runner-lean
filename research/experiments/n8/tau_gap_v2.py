"""tau never reached 1 in 146,652 cascades (max 0.628) but that sample had NO depths 17-22.
tau = R/8 = (prod lambda)/8, so tau should grow EXPONENTIALLY in depth, not linearly:
1.11^23/8 = 1.38, against the observed 1.29 for the 23-case.

Fill the 17-22 band using the d_min axis of the known deep cases (the cell census already showed
depths 16,17,18,19,23 there) and check tau is continuous in K.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor, log, exp
import statistics as st
from collections import defaultdict
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
    t=TH/min(ds); n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n, F(min(ds))*t
        t=max(nextOp(d,t) for d in b); n+=1
    return None,None
byd=defaultdict(list)
BASES=[[30,74,96,127,159,175,224],[49,205,234,256,286,323,366],
       [28,69,95,123,154,172,220],[55,131,181,233,293,329,419]]
for B in BASES:
    for i in range(7):
        for num in range(int(B[i]*0.5*20), int(B[i]*1.7*20)):
            ds=list(B); ds[i]=F(num,20)
            n,tau=run(sorted(ds))
            if n is not None and n>=10: byd[n].append(float(tau))
print(f"  {'depth':>6} {'n':>7} {'min tau':>10} {'mean tau':>10} {'max tau':>10}   {'1.11^K/8':>9}")
for d in sorted(byd):
    a=byd[d]
    print(f"  {d:>6} {len(a):>7} {min(a):>10.4f} {st.mean(a):>10.4f} {max(a):>10.4f}   {1.11**d/8:>9.4f}")
alltau=[(d,x) for d,a in byd.items() for x in a]
print(f"\n  is tau continuous across the 17-22 band? "
      f"{'YES -- every depth 10..28 populated' if set(range(10,29))<=set(byd) else 'missing: '+str(sorted(set(range(10,29))-set(byd)))}")
print(f"  tau >= 1 occurs at depths: {sorted({d for d,x in alltau if x>=1})}")
print(f"\n  fit: log(8 tau) = sum log lambda, so tau = (prod lambda)/8.")
xs=[d for d,_ in alltau]; ys=[log(8*x) for _,x in alltau]
mx,my=st.mean(xs),st.mean(ys)
sl=sum((a-mx)*(b-my) for a,b in zip(xs,ys))/sum((a-mx)**2 for a in xs)
print(f"    regression log(8 tau) = {my-sl*mx:+.4f} + {sl:.5f} K   -> mean lambda = {exp(sl):.5f}")
print(f"    (measured geometric mean lambda over random cascades was 1.11301)")
