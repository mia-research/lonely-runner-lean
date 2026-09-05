#!/usr/bin/env python3
"""
mlaw_s1_firsthand_check_v1.py -- 2026-09-02

Discharges flag F2 of AUDIT_session_2026_09_01_honesty_flags_v1.md: the D2 closure
(RESULT_jacobi_sign_law_proved_secp_class_v1.md) proves RESULT_jacobi_closed_form_m_law_v4.md **S2**,
but the m-law consequence inherits that file's **S1** reduction UNAUDITED.  S1 is checked here
first-hand, exactly.

S1 claims, for q=p^2, p=3 mod 4, B in F_p^*:
    (star)   S := sum_{x in F_q} chi4(x^3+B)  =  chi3(B)*J(chi3,chi4) + conj(chi3)(B)*J(conj(chi3),chi4)
via #{x : x^3=u} = 1+chi3(u)+chibar3(u), the vanishing of sum_u chi4(u+B), (F1) chi4 trivial on F_p^*,
and the substitution u = -B t.

ARM 1  (star) as an exact identity in Z[zeta_12].
ARM 2  the m-law table: S rational, m := S/p in {-2,+1,+2} by (p mod 12, cubic class of B).
ARM 3  the three (F1)/(F2) structural facts S1 rests on.
Exact integer / Z[zeta_12] throughout.  No leakage / ECDLP claim.
"""
import sys
Z12=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(-1,0,1,0),(0,-1,0,1),
     (-1,0,0,0),(0,-1,0,0),(0,0,-1,0),(0,0,0,-1),(1,0,-1,0),(0,1,0,-1)]
def add(v,e,c=1):
    z=Z12[e%12]; return (v[0]+c*z[0],v[1]+c*z[1],v[2]+c*z[2],v[3]+c*z[3])
def mulz(v,e):
    out=(0,0,0,0)
    for k,c in enumerate(v):
        if c: out=add(out,e+k,c)
    return out
def primes(N):
    s=[True]*(N+1); s[0]=s[1]=False
    for i in range(2,int(N**.5)+1):
        if s[i]:
            for j in range(i*i,N+1,i): s[j]=False
    return [i for i in range(N+1) if s[i]]
def fac(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
B=7
def run(p):
    q=p*p; one=p
    def mul(u,v):
        a,b=divmod(u,p); c,d=divmod(v,p)
        return ((a*c-b*d)%p)*p+((a*d+b*c)%p)
    order=q-1; fs=fac(order); gen=None
    for a in range(p):
        for b in range(p):
            e=a*p+b
            if e==0: continue
            ok=True
            for r in fs:
                x,k,bs=one,order//r,e
                while k:
                    if k&1: x=mul(x,bs)
                    bs=mul(bs,bs); k>>=1
                if x==one: ok=False; break
            if ok: gen=e; break
        if gen is not None: break
    dl=[None]*q; x=one
    for k in range(order): dl[x]=k; x=mul(x,gen)
    enc=lambda a,b:(a%p)*p+(b%p)
    c3=lambda u: dl[u]%3
    c4=lambda u: dl[u]%4
    Benc=enc(B,0)

    # ARM 3: structural facts
    F1 = all(c4(enc(c,0))==0 for c in range(1,p))            # chi4 trivial on F_p^*
    m1 = enc(-1,0)
    F0 = (c3(m1)==0)                                         # chi3(-1)=1
    cube_ok = True                                           # #{x: x^3=u} = 1+chi3+chibar3
    cnt=[0]*q
    for xv in range(1,q): cnt[mul(mul(xv,xv),xv)]+=1
    for u in range(1,q):
        pred = 1 + (1 if c3(u)==0 else 0)*2 + (0 if c3(u)==0 else -1)
        cube_ok &= (cnt[u]==(3 if c3(u)==0 else 0))
    # ARM 1: S and the (star) right-hand side, exact
    S=(0,0,0,0)
    for xv in range(q):
        t=mul(mul(xv,xv),xv) if xv else 0
        w=(t+Benc)%q if False else None
        # field addition, not integer: encode add
        a1,b1=divmod(t,p); a2,b2=divmod(Benc,p)
        w=enc(a1+a2,b1+b2)
        if w==0: continue
        S=add(S,3*c4(w))
    def J(a):                                                # J(chi3^a, chi4)
        acc=(0,0,0,0)
        for u in range(1,q):
            a1,b1=divmod(u,p); v=enc(1-a1,-b1)
            if v==0: continue
            acc=add(acc,4*a*c3(u)+3*c4(v))
        return acc
    J1,J2=J(1),J(2)
    rhs=(0,0,0,0)
    for k,c in enumerate(mulz(J1,4*c3(Benc))): rhs=add(rhs,k,c)
    for k,c in enumerate(mulz(J2,(4*((-c3(Benc))%3)))): rhs=add(rhs,k,c)
    star=(S==rhs)
    # ARM 2: m-law
    rat=(S[1]==0 and S[2]==0 and S[3]==0)
    m = S[0]//p if rat and S[0]%p==0 else None
    return F1,F0,cube_ok,star,rat,m,c3(Benc),J1

if __name__=="__main__":
    LIM=int(sys.argv[1]) if len(sys.argv)>1 else 120
    ps=[x for x in primes(LIM) if x%4==3 and x>3 and B%x!=0]  # B must lie in F_p^*
    hdr=f"{'p':>5} {'p%12':>5} | F1 chi3(-1) cube (star) | {'S rational':>10} {'m':>4} | chi3(B) | expected m"
    print(hdr); print("-"*len(hdr))
    ok=True
    for p in ps:
        F1,F0,cu,st,rat,m,cB,J1=run(p)
        if p%12==7: exp = -2 if cB==0 else 1
        else:       exp = 2
        good = F1 and F0 and cu and st and rat and (m==exp); ok&=good
        print(f"{p:>5} {p%12:>5} |  {int(F1)}     {int(F0)}     {int(cu)}    {int(st)}  | {int(rat):>10} {m:>4} | {cB:>7} | {exp:>+3} {'OK' if good else 'MISMATCH'}")
    print()
    print(f"S1 reduction (star) + m-law table reproduced first-hand at every prime: {ok}")
