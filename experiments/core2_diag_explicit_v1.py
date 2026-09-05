"""Explicit 6-runner diagonal de-risk for core2: (1,7,8),(1,9,10),(1,10,11),(1,12,13).
Adds the fictional runner 2*w0: at any time tau, need circDist(2*{w0 tau}) >= 1/6.
Gap [a,b] must also be fictional-safe (runner-0 doubled band avoids near-0/near-1/2),
and each witness must have 2*f0 in a circDist>=1/6 position."""
from math import gcd
from fractions import Fraction as F
def frac(x): return x - (x.numerator // x.denominator)
def cd(x):
    f=frac(x); return min(f,1-f)
def Kf(n,theta):
    x=n*theta; k=x.numerator//x.denominator; return k, x-k

def longest_0123_gap(p,q):
    ns=[p,q-p,q,p+q]; pts=set([F(0),F(q)])
    for n in ns:
        for k in range(-1,n+3):
            for c in (F(1,6),F(5,6)):
                t=F(q)*(k+c)/n
                if F(0)<=t<=F(q): pts.add(t)
    pts=sorted(pts); best=(None,None,F(0))
    for i in range(len(pts)-1):
        ta,tb=pts[i],pts[i+1]; mid=(ta+tb)/2
        if all(cd(n*mid/q)>=F(1,6) for n in ns) and tb-ta>best[2]:
            best=(ta,tb,tb-ta)
    return best

def fict_ok_interval(p,q,a,b,samples=400):
    # 2*w0 over [a,b]: w0=p, position frac(p*t/q); fictional pos = frac(2*p*t/q); need cd>=1/6
    for k in range(samples+1):
        t=a+(b-a)*F(k,samples)
        if cd(2*p*t/q) < F(1,6): return False
    return True

def find_witness(p,q,r,s):
    ns=[p,q-p,q,r,s]
    for d in range(2,80):
        for a in range(1,d):
            th=F(a,d)
            if all(cd(n*th)>=F(1,6) for n in ns) and cd(2*p*th)>=F(1,6):
                return th
    return None

for p,q in [(1,7),(1,9),(1,10),(1,12)]:
    r=p+q
    ta,tb,L=longest_0123_gap(p,q)   # BHK-time
    a=ta/q; b=tb/q                  # tau numerators (x 1/g)
    smax=int(F(q)/(3*L))
    fok = fict_ok_interval(p,q,a,b)
    print(f"\n##### ({p},{q},{r})  gap tau=[{a},{b}] (x1/g) s<= {smax}  fict_gap_ok={fok}")
    for i,n in enumerate([p,q-p,q,r]):
        Ka,fa=Kf(n,a); Kb,fb=Kf(n,b)
        print(f"   r{i}(n={n}): K={Ka} fa={fa} fb={fb} same_K={Ka==Kb}")
    # fictional band over [a,b]: 2p
    K2a,f2a=Kf(2*p,a); K2b,f2b=Kf(2*p,b)
    print(f"   FICT(2p={2*p}): K={K2a} fa={f2a} fb={f2b} same_K={K2a==K2b} (need in[1/6,5/6])")
    for s in range(r+1, smax+1):
        th=find_witness(p,q,r,s)
        if th is None:
            print(f"   s={s}: NO fict-safe witness !!"); continue
        Ks=[]; fs=[]
        for n in [p,q-p,q,r,s]:
            k,f=Kf(n,th); Ks.append(k); fs.append(f)
        k2,f2=Kf(2*p,th)
        print(f"   s={s}: tau={th}/g K={Ks} f={[str(x) for x in fs]} | fict 2p*tau=K{k2}+{f2}")
