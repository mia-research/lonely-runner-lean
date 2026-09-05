#!/usr/bin/env python3
"""
cm_lattice_unfolding — SETUP + SMOKE (validate pipeline before the frozen run).
Executes groundwork for PREREG_cm_lattice_unfolding_v1.md.

DEVIATION D1 (disclosed): the frozen transversal condition `e=0 ∧ s=0` does NOT
quotient the mu3 (phi) action — eps and s are BOTH constant on the mu3-suborbit
{phi^j P} (phi fixes y; eps is mu3-invariant), so e=0∧s=0 keeps FULL mu3-orbits and
the null would still manufacture mu3-lockstep MI. Corrected to the TRUE mu6-orbit
transversal: one canonical representative per scalar orbit {±λ^j d mod n} (min-d
rep). N=(n-1)/6 exactly. The mu6-mismatch WITNESS (spec §3) is run both ways to
confirm the transversal removes the inflation the e=0∧s=0 / full sets show.

Exact int/Fraction signal path (no float in features/targets). Statistic MI uses
math.log ranked against the permutation null (spec §8 carve-out).
"""
import sys, math, random
from fractions import Fraction
from lift_sextant_rhombus_law_proof_v2 import (reduced_basis, rdiv, enorm, gauss_reduce,
                                               cornacchia_4p_D3)
from int1_frame_operator_v1 import build

B_CURVE = 7


# ---------------- curve ----------------
def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True

def count_E(p):
    s=0
    for x in range(p):
        rhs=(x*x%p*x+B_CURVE)%p
        s += 0 if rhs==0 else (1 if pow(rhs,(p-1)//2,p)==1 else -1)
    return p+1+s

def ec_add(P,Q,p):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    m=(3*x1*x1*pow(2*y1,p-2,p))%p if P==Q else ((y2-y1)*pow((x2-x1)%p,p-2,p))%p
    x3=(m*m-x1-x2)%p
    return (x3,(m*(x1-x3)-y1)%p)

def find_gen(p,n):
    for x0 in range(1,p):
        rhs=(x0*x0%p*x0+B_CURVE)%p
        if rhs==0 or pow(rhs,(p-1)//2,p)!=1: continue
        y0=pow(rhs,(p+1)//4,p) if p%4==3 else tonelli(rhs,p)
        return (x0,min(y0,p-y0))
    raise RuntimeError

def tonelli(a,p):
    a%=p
    if p%4==3: return pow(a,(p+1)//4,p)
    q=p-1;s=0
    while q%2==0: q//=2;s+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    m=s;c=pow(z,q,p);t=pow(a,q,p);r=pow(a,(q+1)//2,p)
    while t!=1:
        i=0;tt=t
        while tt!=1: tt=tt*tt%p;i+=1
        b=pow(c,1<<(m-i-1),p); m=i;c=b*b%p;t=t*c%p;r=r*b%p
    return r


# ---------------- Eisenstein integer helpers (a+bω) ----------------
def mulw(z): a,b=z; return (-b, a-b)          # ×ω
def conj(z): a,b=z; return (a-b, -b)          # conjugate

def frobenius(p, n):
    """the Frobenius pi_p=(A,B), N(pi_p)=p, with N(pi_p-1)=n. Search 12 associates."""
    base = cornacchia_4p_D3(p)
    if base is None: return None
    cands=[]
    for z0 in (base, conj(base)):
        z=z0
        for _ in range(3):
            cands.append(z); cands.append((-z[0],-z[1]))
            z=mulw(z)
    for (A,Bc) in cands:
        assert enorm((A,Bc))==p
        if enorm((A-1,Bc))==n:
            return (A,Bc)
    return None

def partner_frob(p, n):
    """pi_n = (A,B), N(pi_n)=n, with N(pi_n-1)=p (amicable partner over F_n).
    Search associates of the norm-n element (pi_p-1)."""
    pip = frobenius(p, n)
    if pip is None: return None
    base = (pip[0]-1, pip[1])           # norm n
    assert enorm(base)==n
    cands=[]
    for z0 in (base, conj(base)):
        z=z0
        for _ in range(3):
            cands.append(z); cands.append((-z[0],-z[1])); z=mulw(z)
    for (A,Bc) in cands:
        if enorm((A-1,Bc))==p:
            return (A,Bc)
    return None

def ideal_basis(gen):
    """reduced Z-basis of the ideal (gen) in Z[ω]."""
    return gauss_reduce(gen, mulw(gen))

def babai(vec, R1, R2):
    """exact Babai reduction of vec=(a,0)-style 2-vector against basis (R1,R2)."""
    DET = R1[0]*R2[1]-R1[1]*R2[0]
    a,b = vec
    c1 = rdiv(a*R2[1]-b*R2[0], DET); c2 = rdiv(b*R1[0]-a*R1[1], DET)
    return (a-(c1*R1[0]+c2*R2[0]), b-(c1*R1[1]+c2*R2[1]))


# ---------------- ladder ----------------
def ladder(cls, lo, count):
    out=[]; p=lo|1
    while len(out)<count:
        if p%12==cls and is_prime(p):
            n=count_E(p)
            if is_prime(n): out.append((p,n))
        p+=2
    return out


def smoke(p, n):
    print("\n=== SMOKE p=%d n=%d (p%%12=%d) ==="%(p,n,p%12))
    pip = frobenius(p,n)
    assert pip is not None, "no Frobenius associate with N(pi-1)=n"
    A,Bc = pip
    print("  pi_p = %d + %d*w   N(pi_p)=%d(==p:%s)  N(pi_p-1)=%d(==n:%s)"
          %(A,Bc,enorm(pip),enorm(pip)==p,enorm((A-1,Bc)),enorm((A-1,Bc))==n))
    # partner Frobenius pi_n (norm n, N(pi_n-1)=p); Psi ideal = (pi_n - 1), norm p
    pin = partner_frob(p,n)
    print("  pi_n = %s   N(pi_n-1)=%s (==p:%s)"%(pin, enorm((pin[0]-1,pin[1])) if pin else None,
          (enorm((pin[0]-1,pin[1]))==p) if pin else None))
    Rn1,Rn2 = ideal_basis((pin[0]-1, pin[1]))   # partner norm-p ideal for Psi
    # target ideal (pi_p - 1), norm n
    Rt1,Rt2 = ideal_basis((A-1,Bc)); assert enorm(Rt1)*1  # basis of norm-n ideal
    # feature lift
    eis,eps = build(p)
    G=find_gen(p,n)
    # build all points, mu6-orbit transversal on scalars {±λ^j d}
    lam = None
    for c in range(2,n):
        if c!=1 and pow(c,3,n)==1: lam=c; break
    seen=[False]*n; reps=[]
    for d in range(1,n):
        if seen[d]: continue
        orb=set()
        t=d
        for _ in range(3):
            orb.add(t); orb.add((n-t)%n); t=t*lam%n
        for o in orb: seen[o]=True
        reps.append(min(orb))
    print("  mu6 transversal: %d reps  (expected (n-1)/6=%.1f)"%(len(reps),(n-1)/6))
    # walk points: need x,y for each rep scalar. Precompute [d]G for reps.
    # cheap: full scalar mult per rep (small p)
    def mul(d):
        R=None; base=G; dd=d
        while dd:
            if dd&1: R=ec_add(R,base,p)
            base=ec_add(base,base,p); dd>>=1
        return R
    Phi=[]; Psi=[]; T=[]; epscount={0:0,1:0,2:0}
    for d in reps:
        P=mul(d); x,y=P
        u,v = eis(x); e=eps(x); epscount[e]+=1
        up,vp = babai((x%p,0), Rn1, Rn2)          # partner lift Psi (norm-p ideal)
        Phi.append((u%2, v%2, e)); Psi.append((up%2, vp%2))
        a,b = babai((d%n,0), Rt1, Rt2)
        T.append((a%2, b%2))
    print("  eps dist on transversal:",epscount)
    from collections import Counter
    def MI(F,Tt):
        N=len(F); jf=Counter(F); jt=Counter(Tt); jj=Counter(zip(F,Tt))
        mi=0.0
        for (f,t),c in jj.items():
            pj=c/N; pf=jf[f]/N; pt=jt[t]/N
            mi += pj*math.log2(pj/(pf*pt))
        return mi
    def perm_p(F,Tt,Bn,seed):
        obs=MI(F,Tt); rng=random.Random(seed); ge=0
        for _ in range(Bn):
            Ts=Tt[:]; rng.shuffle(Ts)
            if MI(F,Ts)>=obs: ge+=1
        return obs,(1+ge)/(Bn+1)
    obs,pp = perm_p(Phi,T,999,0)
    print("  ARM P  MI(Phi2;T2)=%.5f  p_perm=%.4f (B=999)  -> %s"%(obs,pp,"LEAK" if pp<0.001 else "null"))
    # ARM N: conditional MI I(Psi;T|Phi) ~ MI((Phi,Psi);T) - MI(Phi;T)
    PhiPsi=[f+g for f,g in zip(Phi,Psi)]
    cobs = MI(PhiPsi,T)-MI(Phi,T)
    print("  ARM N  I(Psi;T|Phi)~=%.5f bits (conditional; full null in run script)"%cobs)
    # POSITIVE PLANT (must fire at eps=1): inject c = a mod 2
    Phi_pl=[f+(t[0],) for f,t in zip(Phi,T)]     # augment with a mod 2 (=T[0])
    _,pp_pl = perm_p(Phi_pl,T,999,1)
    print("  PLANT eps=1 (inject a mod2): p_perm=%.4f  -> %s"%(pp_pl,"FIRES" if pp_pl<0.001 else "*** DOES NOT FIRE ***"))
    # MU6 WITNESS: full-set (all points, NOT transversal) with plain shuffle should INFLATE
    Phi_full=[]; T_full=[]
    for d in range(1,n):
        P=mul(d); x,y=P
        u,v=eis(x); e=eps(x)
        Phi_full.append((u%2,v%2,e))
        a,b=babai((d%n,0),Rt1,Rt2); T_full.append((a%2,b%2))
    obs_f,pp_f = perm_p(Phi_full,T_full,499,2)
    print("  MU6-WITNESS full-set MI=%.5f p_perm=%.4f  (expect INFLATED/low-p vs transversal null)"%(obs_f,pp_f))
    return pip


if __name__=='__main__':
    # one ladder prime per class, small (p>10^3 for smoke speed; frozen run uses >10^4)
    for cls in (1,7):
        pr = ladder(cls, 2000, 1)[0]
        smoke(*pr)
