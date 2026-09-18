"""Owner, mid-session: "If we have eight runners on a circle isn't that eight disparities?" and
"If the runner's isolation is caused by 2 neighbours then isn't it 5 points?"

I answered both as counting corrections and moved on.  But the gap frame is a DIFFERENT OBJECT,
it is proved in Lean (lonelyAt_iff_gaps, gapAhead, gapBehind, gapAhead_add_gapBehind_le_one,
all from commit 919b944), and it has ZERO downstream uses.  Ask what the cascade looks like in it.

  gapAhead(t)  = min over i of frac((v_i - v_k) t)      -- the nearest runner AHEAD
  gapBehind(t) = 1 - max over i of frac((v_i - v_k) t)  -- the nearest runner BEHIND
  lonely  <=>  gapAhead >= 1/8  AND  gapBehind >= 1/8

Both start at 0 when the pack is together.  gapAhead OPENS at rate d_min; gapBehind CLOSES at
rate d_max.  So in the first lap loneliness needs a window to exist at all."""
from fractions import Fraction as F
from math import floor
import random
TH=F(1,8)
def frac(x): return x-floor(x)
def gapAhead(ds,t): return min(frac(d*t) for d in ds)
def gapBehind(ds,t): return 1-max(frac(d*t) for d in ds)

print("=== the first-lap window, derived in the gap frame ===")
print("   gapAhead >= 1/8  needs  t >= 1/(8*d_min)      (the BOUND)")
print("   gapBehind >= 1/8 needs  t <= 7/(8*d_max)")
print("   a first-lap window exists iff 1/(8 d_min) <= 7/(8 d_max), i.e.  d_max <= 7 d_min")
print("   -- which is THEOREM 4.8, S <= 7, recovered with no circle distance at all.")
print()
rng=random.Random(19); ok=0; tot=0; mism=0
for _ in range(4000):
    v=sorted(rng.sample(range(0,120),8))
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        m,M=min(ds),max(ds); tot+=1
        window = (M<=7*m)
        t=TH/m
        lonely = gapAhead(ds,t)>=TH and gapBehind(ds,t)>=TH
        if window:
            ok+=1
            if not lonely: mism+=1
print(f"   arrangements with S <= 7: {ok}/{tot};  of those, lonely at t = 1/(8 d_min): {ok-mism}/{ok}")
print(f"   mismatches: {mism}")

print()
print("=== what the two gaps actually do -- slopes and breakpoints ===")
def who(ds,t):
    fa=[(frac(d*t),d) for d in ds]
    return min(fa)[1], max(fa)[1]
for name,v,i in [("(1,31,75,97,128,160,176,225) r1",[1,31,75,97,128,160,176,225],0),
                 ("(11,21,22,23,26,34,35,40) r35",[11,21,22,23,26,34,35,40],6)]:
    ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
    m=min(ds)
    print(f"   {name}  d_min={m} d_max={max(ds)}  S={float(max(ds)/m):.2f}")
    prevA=prevB=None; changes=0; samples=0
    t=F(1,1000)
    while t<=F(3,1)/m:
        a,b=who(ds,t); samples+=1
        if prevA is not None and (a!=prevA or b!=prevB): changes+=1
        prevA,prevB=a,b
        t+=F(1,1000)/m
    print(f"      over t in (0, 3/d_min]: the (nearest-ahead, nearest-behind) PAIR changes {changes} times in {samples} samples")

print()
print("=== how many DISTINCT runners ever serve as nearest-ahead or nearest-behind? ===")
rng=random.Random(5); hist={}
for _ in range(600):
    v=sorted(rng.sample(range(0,90),8))
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        m=min(ds); seenA=set(); seenB=set()
        t=F(1,400)
        while t<=F(2,1)/m:
            a,b=who(ds,t); seenA.add(a); seenB.add(b); t+=F(1,400)/m
        k=(len(seenA),len(seenB))
        hist[k]=hist.get(k,0)+1
tot=sum(hist.values())
top=sorted(hist.items(),key=lambda kv:-kv[1])[:8]
print(f"   (#distinct nearest-ahead, #distinct nearest-behind) over t in (0, 2/d_min]:")
for k,c in top: print(f"      {k}: {c/tot:.4f}")
