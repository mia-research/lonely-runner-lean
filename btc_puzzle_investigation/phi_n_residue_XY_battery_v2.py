#!/usr/bin/env python3
"""
v2 — close the loose ends from v1 so 'systematic' is honest:
  (1) EXACT permutation p-value for the one flagged modulus (q=53 X-histogram χ²).
  (2) Joint combinations the marginals miss: S_q for X+Y, X-Y, X*Y mod q.
  (3) Crypto-relevant φ(n) leakage: does X mod q carry the private-key POSITION
      denominator n?  Exact contingency χ²(X mod q, n mod q) + permutation p, and
      χ²(X mod q, parity of ω(n)).  n recomputed EXACTLY from d (no float-era cols).
Exact int/Fraction in the signal path. RNG used only to build integer null
histograms for permutation p-values (the rule's endorsed permutation null).
"""
import csv, random
from math import gcd, isqrt
from fractions import Fraction
random.seed(20260710)

p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
NMAX=256

def factorize(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d += 1 if d==2 else 2
    if m>1: f[m]=f.get(m,0)+1
    return f
def mobius(m):
    if m==1: return 1
    f=factorize(m)
    return 0 if any(e>1 for e in f.values()) else (-1 if len(f)%2 else 1)
def omega(m): return 0 if m<=1 else len(factorize(m))
def ram_table(q):
    divs=[d for d in range(1,q+1) if q%d==0]
    return [sum(d*mobius(q//d) for d in divs if gcd(a,q)%d==0) for a in range(q)]
def ram_var(q,tab): return Fraction(sum(c*c for c in tab), q)
def z_centi(S,var):
    if var==0: return 0
    mag=isqrt(int(Fraction(S*S)*(var**-1)*10000))
    return mag if S>=0 else -mag
def show_z(zc):
    s='-' if zc<0 else ' '; zc=abs(zc)
    return f"{s}{zc//100}.{zc%100:02d}"
def frac3(fr):
    fr=Fraction(fr); s=(fr.numerator*1000)//fr.denominator
    return f"{s//1000}.{s%1000:03d}"
def best_nk(d,N):
    A=1<<(N-1); num=d-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A)
        if k<0:k=0
        if k>n:k=n
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    if g>1: n//=g; k//=g
    return n,k

# ---------- load ----------
BITS=[];DS=[];XS=[];YS=[]
with open("constructed_keys_1to160_100k.csv") as fh:
    for r in csv.DictReader(fh):
        BITS.append(int(r["bits"])); DS.append(int(r["d"]))
        XS.append(int(r["X"],16)); YS.append(int(r["Y"],16))
big=[i for i in range(len(XS)) if BITS[i]>=64]
print(f"loaded {len(XS)}; N>=64 subset: {len(big)}\n")

# ---------- (1) exact permutation p for q=53 X-histogram χ² (full set) ----------
def chi2_hist(vals,q):
    h=[0]*q
    for v in vals: h[v%q]+=1
    exp=Fraction(len(vals),q)
    return sum((Fraction(x)-exp)**2 for x in h)*(exp**-1), h
q=53; Xall=XS
obs_chi,_=chi2_hist(Xall,q); M=len(Xall)
B=300; ge=0
for _ in range(B):
    hn=[0]*q
    for _ in range(M): hn[random.randrange(q)]+=1
    exp=Fraction(M,q)
    cn=sum((Fraction(x)-exp)**2 for x in hn)*(exp**-1)
    if cn>=obs_chi: ge+=1
print(f"(1) q=53 X-hist χ²={frac3(obs_chi)} (df52); exact perm p=({ge}+1)/({B}+1)={frac3(Fraction(ge+1,B+1))}")

# ---------- (2) joint combinations S_q (N>=64) ----------
X=[XS[i] for i in big]; Y=[YS[i] for i in big]; Mb=len(big)
print("\n(2) Ramanujan S_q on joint combinations (N>=64), top |z|:")
for name,comb in [("X+Y",lambda a,b:a+b),("X-Y",lambda a,b:a-b),("X*Y",lambda a,b:a*b)]:
    rows=[]
    for q in range(2,65):
        tab=ram_table(q); var=Fraction(Mb)*ram_var(q,tab)
        S=sum(tab[comb(a,b)%q] for a,b in zip(X,Y))
        rows.append((q,z_centi(S,var)))
    top=sorted(rows,key=lambda r:-abs(r[1]))[:5]
    print(f"   {name:4s}: "+"  ".join(f"q{q}:z={show_z(z)}" for q,z in top))

# ---------- (3) does X mod q leak the position denominator n? ----------
print("\n(3) leakage X mod q  vs  private-key position structure (N>=64, exact n):")
# recompute exact n on a 20k sample of the N>=64 keys
samp=big if len(big)<=20000 else random.sample(big,20000)
ns=[]; xs=[]
for i in samp:
    n,_=best_nk(DS[i],BITS[i]); ns.append(n); xs.append(XS[i])
Ms=len(samp)
def contingency_chi2(a,b,qa,qb):
    tab={}
    for u,v in zip(a,b): tab[(u%qa,v%qb)]=tab.get((u%qa,v%qb),0)+1
    ra=[0]*qa; rb=[0]*qb
    for (u,v),c in tab.items(): ra[u]+=c; rb[v]+=c
    tot=len(a); s=Fraction(0)
    for u in range(qa):
        for v in range(qb):
            o=tab.get((u,v),0); e=Fraction(ra[u]*rb[v],tot)
            if e>0: s+=(Fraction(o)-e)**2*(e**-1)
    return s,(qa-1)*(qb-1)
for q in (3,5,6,7,8,10):
    c2,df=contingency_chi2(xs,ns,q,q)
    # exact perm p by shuffling n against X mod q
    B2=200; ge=0
    xm=[x%q for x in xs]
    for _ in range(B2):
        perm=ns[:]; random.shuffle(perm)
        # inline shuffled contingency on already-reduced xm and n%q
        tab={}
        for u,v in zip(xm,perm): key=(u,v%q); tab[key]=tab.get(key,0)+1
        ra=[0]*q; rb=[0]*q
        for (u,v),cnt in tab.items(): ra[u]+=cnt; rb[v]+=cnt
        s=Fraction(0)
        for u in range(q):
            for v in range(q):
                o=tab.get((u,v),0); e=Fraction(ra[u]*rb[v],Ms)
                if e>0: s+=(Fraction(o)-e)**2*(e**-1)
        if s>=c2: ge+=1
    print(f"   X mod {q} × n mod {q}: χ²={frac3(c2)}(df{df})  perm p={frac3(Fraction(ge+1,B2+1))}")
# X mod q vs omega(n)-parity
print("   X mod q vs parity(ω(n)):")
oip=[omega(n)%2 for n in ns]
for q in (3,7):
    c2,df=contingency_chi2(xs,oip,q,2)
    print(f"     X mod {q} × ω(n)parity: χ²={frac3(c2)}(df{df})")
