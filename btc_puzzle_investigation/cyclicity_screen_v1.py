#!/usr/bin/env python3
"""
Cyclicity screen for PREREG_subrayleigh_deficit_arithmetic_scatter_v5.py (§6).
SCHEDULE CONSTRUCTION ONLY — computes group orders / cyclicity / M / sextic-class.
NO delta, NO spectral statistic, NO leakage test. Exact integer arithmetic throughout
(no float in any path). Output feeds the frozen _SCHEDULE.txt (built in a later step).

For each candidate prime p == 1 (mod 3) in [3000, 12000], disjoint from the 30 training
primes, and the six sextic twists  E_k : y^2 = x^3 + 7 * g^k  (g = smallest primitive root):
  - #E_k  (exact point count)          - cyclic?(E_k)
  - M_k   with a_k^2 - 4p = -3 M_k^2   - sextic-class(7) in Z/6 (per-prime, base = smallest prim root)
"""
import sys
from math import isqrt

TRAINING = {151,193,211,241,277,349,397,433,523,619,691,823,937,1093,1249,1471,
            1693,1987,2281,2671,3169,3607,4177,4861,5647,6571,7639,8893,10357,12043}

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else:
            return False
    return True

def factorize(m):
    f = {}
    d = 2
    while d*d <= m:
        while m % d == 0:
            f[d] = f.get(d,0)+1; m//=d
        d += 1 if d==2 else 2
    if m>1: f[m]=f.get(m,0)+1
    return f

def primitive_root(p):
    if p == 2: return 1
    fs = list(factorize(p-1).keys())
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):
            return g
    raise RuntimeError("no prim root")

# --- exact EC over F_p:  y^2 = x^3 + c ---
def ec_add(P,Q,p,c):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q:
        if y1==0: return None
        lam=(3*x1*x1)*pow(2*y1,p-2,p)%p
    else:
        lam=(y2-y1)*pow((x2-x1)%p,p-2,p)%p
    x3=(lam*lam-x1-x2)%p
    y3=(lam*(x1-x3)-y1)%p
    return (x3,y3)

def scalar_mul(k,P,p,c):
    R=None; Q=P
    while k>0:
        if k&1: R=ec_add(R,Q,p,c)
        Q=ec_add(Q,Q,p,c); k>>=1
    return R

def count_points(p,c):
    """#E for y^2=x^3+c over F_p via exact quadratic-character sum. Returns n=#E."""
    # QR indicator table: qr[v] = +1 if v nonzero square, -1 if non-square, 0 if v==0
    qr=[-1]*p; qr[0]=0
    for x in range(1,p):
        qr[x*x%p]=1
    s=0
    for x in range(p):
        s+=qr[(x*x%p*x+c)%p]
    return p+1+s   # n = p+1 - a_p, a_p = -s

def is_cyclic(p,c,n):
    """Exact: E(F_p) ~ Z/d1 x Z/d2, d1|d2. Cyclic iff d1==1.
    d1 | gcd over primes of (v_l(n)//2 capped by v_l(p-1)). If that bound is 1 -> proven cyclic.
    Else confirm via exponent = lcm of point orders (== n iff cyclic)."""
    fn=factorize(n); fp1=factorize(p-1)
    d1max=1
    for l,e in fn.items():
        cap=min(e//2, fp1.get(l,0))
        d1max*= l**cap
    if d1max==1:
        return True, "proven(d1max=1)"
    # exponent test with deterministic small x-seeds (exact)
    import random
    rng=random.Random(p*1000003+c)
    def point_order(P):
        if P is None: return 1
        e=n
        for l in fn:
            while e%l==0 and scalar_mul(e//l,P,p,c) is None:
                e//=l
        return e
    L=1; tries=0; found=0
    x=0
    while found<40 and x<p:
        rhs=(x*x%p*x+c)%p
        if pow(rhs,(p-1)//2,p)==1 or rhs==0:
            y=tonelli(rhs,p)
            if y is not None:
                o=point_order((x,y)); L=L*o//gcd(L,o); found+=1
                if L==n: return True, f"exponent==n(found={found})"
        x+=1
    return (L==n), f"exponent={L}<n(found={found})"

from math import gcd
def tonelli(a,p):
    a%=p
    if a==0: return 0
    if pow(a,(p-1)//2,p)!=1: return None
    if p%4==3: return pow(a,(p+1)//4,p)
    q=p-1; s=0
    while q%2==0: q//=2; s+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    m=s; cc=pow(z,q,p); t=pow(a,q,p); r=pow(a,(q+1)//2,p)
    while t!=1:
        t2=t; i=0
        while t2!=1: t2=t2*t2%p; i+=1
        b=pow(cc,1<<(m-i-1),p)
        m=i; cc=b*b%p; t=t*cc%p; r=r*b%p
    return r

def sextic_class_of(val,p,g):
    """k in Z/6 with chi6(val) = zeta^k, zeta = g^((p-1)/6). Canonical (g=smallest prim root)."""
    e=(p-1)//6
    zeta=pow(g,e,p); t=pow(val%p,e,p)
    z=1
    for k in range(6):
        if z==t: return k
        z=z*zeta%p
    return -1

def main():
    lo,hi=3000,12000
    cands=[p for p in range(lo,hi+1) if p%3==1 and p not in TRAINING and is_prime(p)]
    rows=[]
    cyc_dist={}
    ge4=0
    out=open("cyclicity_screen_v1_data.txt","w")
    out.write("# p g sextic_class_of_7 | per-twist: k c_k n_k a_k M_k cyclic\n")
    for i,p in enumerate(cands):
        g=primitive_root(p)
        base=7%p
        scl7=sextic_class_of(base,p,g)
        ncyc=0; twists=[]
        for k in range(6):
            c=base*pow(g,k,p)%p
            if c==0: continue
            n=count_points(p,c)
            a=p+1-n
            disc=4*p-a*a
            M = isqrt(disc//3) if disc>0 and disc%3==0 else -1
            okM = (M>0 and 3*M*M==disc)
            cyc,_why=is_cyclic(p,c,n)
            if cyc: ncyc+=1
            twists.append((k,c,n,a,M if okM else -1,cyc))
            out.write(f"{p} {g} {scl7} | {k} {c} {n} {a} {M if okM else -1} {int(cyc)}\n")
        cyc_dist[ncyc]=cyc_dist.get(ncyc,0)+1
        if ncyc>=4: ge4+=1
        rows.append((p,scl7,ncyc,twists))
        if (i+1)%20==0: print(f"...{i+1}/{len(cands)} screened", file=sys.stderr)
    out.close()

    print(f"\n=== CYCLICITY SCREEN v1 — schedule construction (no delta) ===")
    print(f"candidate primes p==1 mod 3 in [{lo},{hi}], disjoint from 30 training: {len(cands)}")
    print(f"cyclic-twist-count distribution: {dict(sorted(cyc_dist.items()))}")
    print(f"primes with >=4 cyclic twists (retained for surface/H2): {ge4}  ({100*ge4/len(cands):.1f}%)")
    print(f"primes with >=1 cyclic twist (base-curve trajectory candidates): "
          f"{sum(v for k,v in cyc_dist.items() if k>=1)}")
    # base-curve (k=0) cyclic fraction -> trajectory usable set
    base_cyc=sum(1 for _,_,_,tw in rows if any(t[0]==0 and t[5] for t in tw))
    print(f"primes whose BASE curve k=0 is cyclic (H1 trajectory points): {base_cyc}")
    # sextic-class(7) distribution on the candidate set
    scl={}
    for _,s,_,_ in rows: scl[s]=scl.get(s,0)+1
    print(f"sextic-class(7) distribution over candidates: {dict(sorted(scl.items()))}")
    # M distribution among cyclic twists (H3 needs M>1)
    Ms=[t[4] for _,_,_,tw in rows for t in tw if t[5] and t[4]>0]
    m1=sum(1 for m in Ms if m==1)
    print(f"cyclic twists total={len(Ms)}; with M==1 (B1 infeasible)={m1}; with M>1 (H3-eligible)={len(Ms)-m1}")
    print(f"per-prime data -> cyclicity_screen_v1_data.txt")

if __name__=="__main__":
    main()
