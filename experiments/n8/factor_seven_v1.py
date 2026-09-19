"""Two things.
(1) The flank framework is an EXACT reformulation, not a reduction:
       flank e clear at multiplier c   <=>   subject lonely at time t = c/(8e).
(2) What MinusSeven.flank_clear_of_no_tiny actually delivers:
       max|d_j| <= 7*min|d_j|  =>  subject lonely, at the explicit time (8L-7)/(8e).
    Measure how much of the space that covers."""
from math import gcd, lcm
from fractions import Fraction
import random
def clearAt(ds,e,c):
    M=8*e
    return all(min((c*d)%M, M-(c*d)%M)>=e for d in ds)
def lonelyAt(ds,t):
    """t a Fraction; distance of t*d to the nearest integer >= 1/8 for every d"""
    for d in ds:
        x=t*d; f=x-int(x)
        if f<0: f+=1
        if min(f,1-f)<Fraction(1,8): return False
    return True
random.seed(19)
bad=0; tot=0
for _ in range(60000):
    e=random.randint(1,60); c=1+8*random.randint(-40,40)
    ds=[d for d in (random.randint(-300,300) for _ in range(7)) if d!=0]
    if not ds: continue
    tot+=1
    if clearAt(ds,e,c)!=lonelyAt(ds,Fraction(c,8*e)): bad+=1
print(f"(1) 'flank e clear at c' <=> 'lonely at t = c/(8e)' over {tot} cases: "
      f"{'HOLDS' if bad==0 else f'FAILS {bad}'}")

print("\n(2) the factor-7 theorem, checked directly against loneliness")
bad2=0; n2=0; cov={}
for hi in (20,100,1000):
    hit=0; tot2=0
    for _ in range(40000):
        v=random.sample(range(-hi,hi+1),8); s=random.randrange(8)
        ds=[v[j]-v[s] for j in range(8) if j!=s]
        tot2+=1
        A=[abs(d) for d in ds]; e=max(A)
        if e<=7*min(A):
            hit+=1
            L=lcm(*[e//gcd(a,e) for a in A])
            n2+=1
            if not lonelyAt(ds,Fraction(8*L-7,8*e)): bad2+=1
    cov[hi]=(hit,tot2)
print(f"    hypothesis max <= 7*min holds for: "
      + ", ".join(f"+-{h}: {a}/{b} = {100*a/b:.1f}%" for h,(a,b) in cov.items()))
print(f"    on those {n2} subjects, the predicted time (8L-7)/(8e) is lonely: "
      f"{'ALL' if bad2==0 else f'FAILS {bad2}'}")
