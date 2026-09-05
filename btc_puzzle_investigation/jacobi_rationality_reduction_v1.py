#!/usr/bin/env python3
"""
jacobi_rationality_reduction_v1.py -- 2026-09-01

Checks the REDUCTION of the one remaining gap of RESULT_jacobi_closed_form_m_law_v4.md
(the "J is real, sign set by p mod 3" claim, graded [EMPIRICAL 12/12], NOT proved).

Derivation chain under test (q=p^2, p=3 mod 4, F_q = F_p[i]):

  L1  chi4 is trivial on F_p^*  (v4 F1).  Coset-splitting the Gauss sum over
      F_q^*/F_p^* and using Tr(a+bi)=2a gives, for ANY chi of F_q^* whose
      restriction theta := chi|_{F_p^*} is nontrivial,
            g(chi) = g_p(theta) * S(chi),     S(chi) := sum_{Tr x = 1} chi(x).
      Since chi4 is subfield-trivial, chi3 and chi3*chi4 share the SAME theta,
      so the irrational prefactor g_p(theta) cancels in the ratio.

  L2  J(chi3,chi4) = g(chi3) g(chi4) / g(chi3 chi4)
                   = g(chi4) * S(chi3) / S(chi3 chi4).

  L3  g(chi4) = p * chi4(x0), x0 any nonzero trace-zero element, and
      chi4(x0) = zeta_4^{(p+1)/2} = +1 iff p = 7 mod 8.  So g(chi4) = (2|p)*p.
      [derived; witnessed exactly in jacobi_rationality_gate_v1.py]

  Hence  J = -p  (p=1 mod 3) / +p (p=2 mod 3)   <=>   C2 below.

TESTS (exact, integer / Z[zeta_12]; no floats in any verdict):
  C0  chi3 = chi3' o N   (norm-lift), chi3' := conj(chi3|_{F_p^*})
  C1  g(chi) = g_p(theta) * S(chi) for chi in {chi3, chi3*chi4}   [float, NOT a verdict]
  C2  S(chi3*chi4) = -(2|p)(-3|p) * S(chi3)      <-- THE reduced gap
  C3  S(chi3) = -chi3'(2) * J_p(chi2', chi3')    <-- ties S(chi3) to a classical
                                                     Jacobi sum over F_p, |.|=sqrt(p)
  C4  J(chi3,chi4) = -p / +p   (re-derived here independently of gate_v1)

No leakage / ECDLP / keyspace claim.  Not a leakage test, sweep, scan or
anomaly drill -- no statistic, no null, no target involving d.
"""
import cmath, sys

Z12 = [( 1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),
       (-1,0,1,0),(0,-1,0,1),(-1,0,0,0),(0,-1,0,0),
       (0,0,-1,0),(0,0,0,-1),(1,0,-1,0),(0,1,0,-1)]

def add(v,e,c=1):
    z=Z12[e%12]; return (v[0]+c*z[0],v[1]+c*z[1],v[2]+c*z[2],v[3]+c*z[3])
def smul(v,s): return tuple(s*x for x in v)

def primes_upto(N):
    s=[True]*(N+1); s[0]=s[1]=False
    for i in range(2,int(N**.5)+1):
        if s[i]:
            for j in range(i*i,N+1,i): s[j]=False
    return [i for i in range(N+1) if s[i]]
def factor(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def legendre(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1

def run(p):
    q=p*p; one=p
    def mul(u,v):
        a,b=divmod(u,p); c,d=divmod(v,p)
        return ((a*c-b*d)%p)*p + ((a*d+b*c)%p)
    order=q-1; facs=factor(order); gen=None
    for a in range(p):
        for b in range(p):
            e=a*p+b
            if e==0: continue
            ok=True
            for r in facs:
                x,k,base=one,order//r,e
                while k:
                    if k&1: x=mul(x,base)
                    base=mul(base,base); k>>=1
                if x==one: ok=False; break
            if ok: gen=e; break
        if gen is not None: break
    dlog=[None]*q; x=one
    for k in range(order): dlog[x]=k; x=mul(x,gen)
    assert x==one and dlog[one]==0

    enc=lambda a,b:(a%p)*p+(b%p)
    c3=lambda u: dlog[u]%3            # chi3(u) = zeta_3^{c3} = zeta_12^{4*c3}
    c4=lambda u: dlog[u]%4            # chi4(u) = zeta_4^{c4} = zeta_12^{3*c4}

    # ---- C0: chi3 = chi3' o N, chi3' = conj(chi3 restricted to F_p^*) ----
    #   theta(c)=chi3(c)=chi3'(c^2)=conj(chi3')(c)  =>  chi3'(c)=conj(theta(c))
    chi3p={}                                   # exponent of zeta_3 for c in F_p^*
    for c in range(1,p): chi3p[c]=(-c3(enc(c,0)))%3
    C0=True
    for a in range(p):
        for b in range(p):
            u=enc(a,b)
            if u==0: continue
            N=(a*a+b*b)%p                      # N(a+bi)=a^2+b^2
            if chi3p[N]!=c3(u): C0=False; break
        if not C0: break

    # ---- S(chi) over the trace-1 line: Tr(a+bi)=2a  =>  a = 1/2 ----
    half=pow(2,p-2,p)
    S3=(0,0,0,0); S34=(0,0,0,0)
    for b in range(p):
        u=enc(half,b)
        S3 =add(S3 , 4*c3(u))
        S34=add(S34, 4*c3(u)+3*c4(u))

    # ---- C2: S(chi3 chi4) = -(2|p)(-3|p) S(chi3) ----
    e2  = 1 if p%8 in (1,7) else -1            # (2|p)
    em3 = 1 if p%3==1 else -1                  # (-3|p)
    sgn = -e2*em3
    C2 = (S34 == smul(S3,sgn))

    # ---- C3: S(chi3) = -chi3'(2) * J_p(chi2',chi3') ----
    Jp=(0,0,0,0)
    for t in range(1,p):
        if (1-t)%p==0: continue
        l=legendre(t,p)
        Jp=add(Jp, 4*chi3p[(1-t)%p], l)
    C3 = (S3 == smul(add((0,0,0,0),4*chi3p[2%p]),-1) and False) or \
         (S3 == tuple(-x for x in _mulZ12(Z12[(4*chi3p[2%p])%12], Jp)))

    # ---- C4: J(chi3,chi4) recomputed directly ----
    J=(0,0,0,0)
    for u in range(1,q):
        a1,b1=divmod(u,p); w=enc(1-a1,-b1)
        if w==0: continue
        J=add(J, 4*c3(u)+3*c4(w))
    C4 = (J == ((-p,0,0,0) if p%3==1 else (p,0,0,0)))

    # ---- C1 float cross-check (not a verdict) ----
    zp=[cmath.exp(2j*cmath.pi*k/p) for k in range(p)]
    z12=[cmath.exp(2j*cmath.pi*k/12) for k in range(12)]
    def gq(expfn):
        s=0j
        for u in range(1,q):
            a1=u//p; s+=z12[expfn(u)%12]*zp[(2*a1)%p]
        return s
    def gp(th):
        s=0j
        for c in range(1,p): s+=z12[(4*th[c])%12]*zp[c%p]
        return s
    theta={c:(c3(enc(c,0)))%3 for c in range(1,p)}
    ev=lambda v: v[0]+v[1]*z12[1]+v[2]*z12[2]+v[3]*z12[3]
    g3=gq(lambda u:4*c3(u)); g34=gq(lambda u:4*c3(u)+3*c4(u)); gpt=gp(theta)
    C1=max(abs(g3-gpt*ev(S3)), abs(g34-gpt*ev(S34)))
    return C0,C1,C2,C3,C4,S3,S34,sgn

def _mulZ12(za,v):
    """multiply vector v by the Z12 basis vector za (a root of unity's vector form)"""
    # za is one of the Z12 entries = zeta^e ; recover e
    e=Z12.index(za)
    out=(0,0,0,0)
    for k,c in enumerate(v):
        if c: out=add(out,e+k,c)
    return out

if __name__=="__main__":
    LIM=int(sys.argv[1]) if len(sys.argv)>1 else 160
    ps=[p for p in primes_upto(LIM) if p%4==3 and p>3]
    hdr=f"{'p':>5} {'p%24':>5} | C0  C2  C3  C4 |  sgn | max|g-gp*S| (float)"
    print(hdr); print("-"*len(hdr))
    ok=True
    for p in ps:
        C0,C1,C2,C3,C4,S3,S34,sgn=run(p)
        ok &= (C0 and C2 and C3 and C4)
        print(f"{p:>5} {p%24:>5} |  {int(C0)}   {int(C2)}   {int(C3)}   {int(C4)} | {sgn:>+3} | {C1:.2e}")
    print()
    print(f"C0 (norm-lift) & C2 (REDUCED GAP) & C3 (classical Jacobi tie) & C4 (J=-+p): {ok}")
