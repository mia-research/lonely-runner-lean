#!/usr/bin/env python3
"""PREREG_ell_ge5_mutual_information_v1: MI probe of chi_l(p mod n) vs chi_l(n mod p).
Exact integers for the number theory; MI is a monotone statistic vs an exact permutation null
(project rule: float allowed only as a permutation-ranked statistic, never as a threshold).

THIS FILE runs the two MACHINERY controls (M0, M1) first -- they test the STATISTIC, not the
frozen arms -- then the arms. Machinery is safe to run pre-approval; arms wait for the designer.
"""
from math import isqrt, log, gcd
import random, sys
from collections import Counter

# ---------- number theory (exact) ----------
_S=[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]
def is_prime(m,bases=(2,3,5,7,11,13,17,19,23,29,31,37)):
    if m<2: return False
    for q in _S:
        if m%q==0: return m==q
    d,s=m-1,0
    while d%2==0: d//=2; s+=1
    for a in bases:
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def least_primitive_root(p):
    if p==2: return 1
    fac=[]; m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None

def cornacchia3(p,rnd):
    while True:
        g=rnd.randrange(2,p); w=pow(g,(p-1)//3,p)
        if w!=1: break
    r=(2*w+1)%p
    if r<p-r: r=p-r
    a,b=p,r; lim=isqrt(p)
    while b>lim: a,b=b,a%b
    c=p-b*b
    if c%3: return None
    y2=c//3; y=isqrt(y2)
    return (b,y) if y*y==y2 else None

def cornacchia_D(p,absD,rnd):
    """4p = t^2 + absD v^2 via sqrt(-absD)."""
    D=-absD
    # need sqrt(D) mod p
    if pow(D%p,(p-1)//2,p)!=1: return None
    # Tonelli
    def tonelli(a,p):
        a%=p
        if a==0: return 0
        if p%4==3: return pow(a,(p+1)//4,p)
        q,s=p-1,0
        while q%2==0: q//=2; s+=1
        z=2
        while pow(z,(p-1)//2,p)!=p-1: z+=1
        m,c,t,r=s,pow(z,q,p),pow(a,q,p),pow(a,(q+1)//2,p)
        while t!=1:
            i,t2=0,t
            while t2!=1: t2=t2*t2%p; i+=1
            b=pow(c,1<<(m-i-1),p); m,c=i,b*b%p; t=t*c%p; r=r*b%p
        return r
    x0=tonelli(D%p,p)
    if (x0-D)%2: x0=p-x0
    a,b=2*p,x0; c=isqrt(4*p)
    while b>c: a,b=b,a%b
    r=4*p-b*b
    if r%absD: return None
    v2=r//absD; v=isqrt(v2)
    return (b,v) if v*v==v2 and v>0 else None

def exponent(base, mod, ell, zeta):
    """discrete log of base^((mod-1)/ell) mod `mod` in <zeta>, i.e. j with base^..=zeta^j."""
    val=pow(base % mod,(mod-1)//ell,mod)
    z=1
    for jj in range(ell):
        if z==val: return jj
        z=z*zeta%mod
    raise AssertionError("not an ell-th root of unity")

# ---------- statistic ----------
def mutual_information(js,ks,ell):
    """plug-in MI in nats over (Z/ell)^2."""
    N=len(js)
    joint=Counter(zip(js,ks)); mj=Counter(js); mk=Counter(ks)
    I=0.0
    for (a,b),c in joint.items():
        pij=c/N; pi=mj[a]/N; pj=mk[b]/N
        I+=pij*log(pij/(pi*pj))
    return I

def perm_pvalue(js,ks,ell,rnd,shuffles=10000):
    obs=mutual_information(js,ks,ell)
    kl=list(ks); ge=0
    for _ in range(shuffles):
        rnd.shuffle(kl)
        if mutual_information(js,kl,ell)>=obs-1e-15: ge+=1
    return obs,(ge+1)/(shuffles+1)

# =====================================================================
# M0: choice-freeness -- relabel zeta and confirm MI is bit-identical
# =====================================================================
print("=== M0 (machinery): is MI invariant under root-of-unity relabeling? ===")
rnd=random.Random(1)
# synthesize an arbitrary dependent (j,k) sample
ell=7
js=[rnd.randrange(ell) for _ in range(3000)]
ks=[(2*j+rnd.randrange(3))%ell for j in js]      # dependent
I_base=mutual_information(js,ks,ell)
# relabel j->a*j, k->b*k (a,b coprime to ell)
for a,b in ((2,3),(3,5),(6,4)):
    js2=[(a*j)%ell for j in js]; ks2=[(b*k)%ell for k in ks]
    I2=mutual_information(js2,ks2,ell)
    print(f"  relabel (a={a},b={b}): MI={I2:.10f}  base={I_base:.10f}  identical={abs(I2-I_base)<1e-12}")
print()

# =====================================================================
# M1: synthetic-positive -- uniform marginals, DEPENDENT, 2x2 (0,0) cell blind
# =====================================================================
print("=== M1 (machinery): does MI catch a coupling the 2x2 (0,0)-cell test misses? ===")
rnd=random.Random(2)
ell=5; N=8000
# coupling: k = (j + s) mod ell with s in {1,2,3,4} chosen by j (never s=0),
# so (0,0) NEVER co-occurs by the shift... build so marginals uniform, P(0,0)=P0*P0 target.
# Simplify: j uniform; k=(j + f(j)) with f a fixed nonzero permutation offset -> deterministic dependence,
# uniform marginals, and P(j=0,k=0)=0 while P(j=0)P(k=0)=1/25. Then ADD noise to raise (0,0) to 1/25.
js=[]; ks=[]
for _ in range(N):
    j=rnd.randrange(ell)
    if rnd.random()<0.5:
        k=(j+1+rnd.randrange(ell-1))%ell    # dependent, avoids k=j sometimes
    else:
        k=rnd.randrange(ell)                 # noise
    js.append(j); ks.append(k)
# 2x2 test on booleans [j==0],[k==0]
A=[1 if j==0 else 0 for j in js]; B=[1 if k==0 else 0 for k in ks]
NN=len(A); a1=sum(A); b1=sum(B); agree=sum(x&y for x,y in zip(A,B))
E00=a1*b1/NN
def perm2(A,B,rnd,sh=10000):
    obs=sum(x&y for x,y in zip(A,B)); Bl=list(B); ge=0
    for _ in range(sh):
        rnd.shuffle(Bl);
        if sum(x&y for x,y in zip(A,Bl))>=obs: ge+=1
    return obs,(ge+1)/(sh+1)
o2,p2=perm2(A,B,rnd)
I_obs,p_mi=perm_pvalue(js,ks,ell,rnd)
print(f"  2x2 (0,0) cell : agree={o2} vs E={E00:.1f}  perm p={p2:.4f}   {'MISSES (null)' if p2>0.01 else 'sees it'}")
print(f"  MI Î={I_obs:.5f} nats  perm p={p_mi:.5f}   {'SEES IT (p<0.01)' if p_mi<0.01 else 'also blind'}")
print(f"  -> M1 {'PASS: MI beats the 2x2' if (p2>0.01 and p_mi<0.01) else 'FAIL or inconclusive'}")
print()

# =====================================================================
# power calibration: min detectable MI at each ell for N=8000 (null 95th pct)
# =====================================================================
print("=== power: null distribution of Î under independence (N=8000) ===")
rnd=random.Random(3)
for ell in (5,7,11,13):
    N=8000
    null=[]
    for _ in range(400):
        js=[rnd.randrange(ell) for _ in range(N)]
        ks=[rnd.randrange(ell) for _ in range(N)]
        null.append(mutual_information(js,ks,ell))
    null.sort()
    bias=(ell-1)**2/(2*N)
    print(f"  ell={ell:>2}: mean Î_null={sum(null)/len(null):.5f}  95th={null[int(.95*len(null))]:.5f}"
          f"  99th={null[int(.99*len(null))]:.5f}  (bias≈{bias:.5f})   cells={ell*ell}, ~{N//(ell*ell)}/cell")
    sys.stdout.flush()
