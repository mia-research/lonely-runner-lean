"""Emit exact Lean constants for the remaining BHK 5.2.12 diagonal cases.
g-free: positions {n_i * theta}, n=(p,q-p,q,p+q,s). Step-A interval in tau is
[ta/q, tb/q] (times 1/g). Witness tau passed as value/g."""
from fractions import Fraction as F

def frac(x): return x - (x.numerator // x.denominator)
def cdist(x):
    f=frac(x); return min(f,1-f)
def Kf(n, theta):
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
        if all(cdist(n*mid/q)>=F(1,6) for n in ns) and tb-ta>best[2]:
            best=(ta,tb,tb-ta)
    return best

def find_witness(ns):
    for d in range(2,80):
        for a in range(1,d):
            th=F(a,d)
            if all(cdist(n*th)>=F(1,6) for n in ns): return th
    return None

for p,q in [(1,6),(2,7),(2,9),(1,10)]:
    r=p+q; ns0123=[p,q-p,q,r]
    ta,tb,L=longest_0123_gap(p,q)
    a=ta/q; b=tb/q  # tau numerators (times 1/g)
    smax=int(F(q)/(3*L))
    print(f"\n##### ({p},{q},{r})  n=({p},{q-p},{q},{r},s)")
    print(f"  a = {a}/g   b = {b}/g    (b-a) = {b-a}/g")
    print(f"  s_bound: (b-a) <= 1/(3 g s) -> s <= q/(3*(b-a)) = {F(q)/(3*(b-a))} -> s<= {smax}")
    print(f"  STEP A bands (K, fa, fb):")
    for i,n in enumerate(ns0123):
        Ka,fa=Kf(n,a); Kb,fb=Kf(n,b)
        assert Ka==Kb, (p,q,i,Ka,Kb)
        ok = fa>=F(1,6) and fb<=F(5,6)
        print(f"    r{i}(n={n}): K={Ka} fa={fa} fb={fb}  in[1/6,5/6]={ok}")
    print(f"  STEP B witnesses:")
    for s in range(r+1, smax+1):
        nsf=[p,q-p,q,r,s]; th=find_witness(nsf)
        Ks=[]; fs=[]
        for n in nsf:
            k,f=Kf(n,th); Ks.append(k); fs.append(f)
        print(f"    s={s}: tau={th}/g  K={Ks}  f={[str(x) for x in fs]}")
