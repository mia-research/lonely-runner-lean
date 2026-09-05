#!/usr/bin/env python3
"""
mlaw_lefschetz_bridge_v1.py -- 2026-09-02

Proves/witnesses the LAST empirical link in the m-law chain:      m = Re(S)/p.
(Flagged 2026-09-02 in RESULT_jacobi_sign_law_proved_secp_class_v1.md: `m = Re(S)/p` was a
"firing control" in RESULT_mu4_eigenvalue_individual_v1.md -- 155/155 OOS agreement, never derived.)

THE ARGUMENT (Weil/Lefschetz point counting on the superelliptic curve).
  C : w^4 = f(x), f = x^3 + B, B in F_p^*.  gcd(4,3)=1 => C is smooth of genus 3 with EXACTLY ONE
  point at infinity.  The quotient (x,w) -> (x, w^2) maps C -> E : y^2 = x^3+B, and
  Jac(C) ~ E x A_new with dim A_new = 2, so  a_C(k) = a_E(k) + a_new(k)  for every k.

  For 4 | #F^* :   #{w : w^4 = u} = sum_{chi^4 = eps} chi(u) = 1 + chi2(u) + chi4(u) + chibar4(u),
  valid at u=0 too (both sides = 1).  Hence over any F_Q with 4 | Q-1:
      #C_aff(F_Q) = Q + sum_x chi2(f(x)) + S + conj(S),   S := sum_x chi4(f(x))
  and #C(F_Q) = #C_aff + 1.  Since #E_aff(F_Q) = Q + sum_x chi2(f(x)), i.e. sum_x chi2(f(x)) = -a_E,
      a_C = a_E - 2*Re(S)   =>   ** a_new = -2*Re(S) **.

  STEP 1 (over F_p, p = 3 mod 4).  gcd(4,p-1) = 2, so w^4=u and w^2=u have the SAME solution count
  and #C(F_p) = #E(F_p), i.e. a_new(1) = 0.  With char(t) = t^4 + b1 t^3 + b2 t^2 + b1 p t + p^2
  (functional equation), a_new(1) = -b1, so ** b1 = 0 **.  (This IS the "mu4 argument", derived.)

  STEP 2 (over F_{p^2}).  4 | p^2-1 always, so the display above applies:  a_new(2) = -2*Re(S).

  STEP 3 (Newton).  a_new(2) = sum alpha_i^2 = e1^2 - 2 e2 = b1^2 - 2 b2 = -2 b2  (by STEP 1).
  Comparing:  -2 b2 = -2 Re(S)  =>  ** b2 = Re(S) **  =>  ** m = b2/p = Re(S)/p **.   QED

WITNESSED HERE, exactly (S in Z[i]; all counts brute-force integer):
  A1  #C(F_p) == #E(F_p)                              (STEP 1, => b1 = 0)
  A2  #C_aff(F_q) == q + T2 + 2*Re(S),  q = p^2       (the character-count display)
  A3  #{w : w^4 = u} == 1 + chi2 + chi4 + chibar4 for EVERY u in F_q, u=0 included
  A4  Re(S) divisible by p, and m = Re(S)/p matches the measured law
  A5  Im(S) == 0   (not needed by the proof; recorded -- it is why "Re" is harmless)
No leakage / ECDLP / keyspace claim.
"""
import sys
B=7
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
def legp(a,p):
    a%=p
    return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)

def run(p):
    q=p*p; one=p
    def mul(u,v):
        a,b=divmod(u,p); c,d=divmod(v,p)
        return ((a*c-b*d)%p)*p+((a*d+b*c)%p)          # F_p[i], i^2=-1  (p = 3 mod 4)
    enc=lambda a,b:(a%p)*p+(b%p)
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

    # ---- A3: fourth-power counts vs the character formula, over F_q
    pow4=[0]*q
    for w in range(1,q): pow4[mul(mul(w,w),mul(w,w))]+=1
    pow4[0]=1                                          # w=0 is the unique 4th root of 0
    A3=True
    for u in range(q):
        if u==0: pred=1
        else:
            k=dl[u]
            c2 = 1 if k%2==0 else -1
            r4 = k%4                                    # chi4(u)+chibar4(u) = 2cos(pi k/2)
            cc = 2 if r4==0 else (-2 if r4==2 else 0)
            pred = 1 + c2 + cc
        if pow4[u]!=pred: A3=False; break

    # ---- S in Z[i], and T2, over F_q
    Bq=enc(B,0); Sre=Sim=0; T2=0; Caff=0
    for a in range(p):
        for b in range(p):
            xx=enc(a,b)
            fx=enc(*divmod(mul(mul(xx,xx),xx),p)) if False else None
            cube=mul(mul(xx,xx),xx)
            a1,b1=divmod(cube,p); a2,b2=divmod(Bq,p)
            u=enc(a1+a2,b1+b2)
            Caff+=pow4[u]
            if u==0: continue
            k=dl[u]
            T2 += 1 if k%2==0 else -1
            r4=k%4
            if   r4==0: Sre+=1
            elif r4==1: Sim+=1
            elif r4==2: Sre-=1
            else:       Sim-=1
    A2 = (Caff == q + T2 + 2*Sre)

    # ---- A1: #C(F_p) vs #E(F_p)   (p = 3 mod 4  =>  gcd(4,p-1)=2)
    p4=[0]*p
    for w in range(1,p): p4[w*w%p*(w*w%p)%p]+=1
    p4[0]=1
    p2=[0]*p
    for w in range(1,p): p2[w*w%p]+=1
    p2[0]=1
    Cp=Ep=0
    for xv in range(p):
        u=(xv*xv%p*xv+B)%p
        Cp+=p4[u]; Ep+=p2[u]
    A1 = (Cp==Ep)

    m = Sre//p if Sre%p==0 else None
    A4 = (m is not None)
    A5 = (Sim==0)
    return A1,A2,A3,A4,A5,Sre,Sim,m,T2,Caff,q

if __name__=="__main__":
    LIM=int(sys.argv[1]) if len(sys.argv)>1 else 110
    ps=[x for x in primes(LIM) if x%4==3 and x>3 and B%x!=0]
    hdr=f"{'p':>5} {'p%12':>5} | A1 A2 A3 A4 A5 | {'Re(S)':>7} {'Im(S)':>6} {'m':>3} | expected m"
    print(hdr); print("-"*len(hdr))
    ok=True
    for p in ps:
        A1,A2,A3,A4,A5,Sre,Sim,m,T2,Caff,q=run(p)
        exp = 2 if p%12==11 else (-2 if pow(B,(p-1)//3,p)==1 else 1)
        good=A1 and A2 and A3 and A4 and A5 and m==exp; ok&=good
        print(f"{p:>5} {p%12:>5} |  {int(A1)}  {int(A2)}  {int(A3)}  {int(A4)}  {int(A5)} | {Sre:>7} {Sim:>6} {str(m):>3} | {exp:>+3} {'OK' if good else 'MISMATCH'}")
    print()
    print(f"Lefschetz bridge witnessed (A1 b1=0, A2 the count display, A3 the character identity): {ok}")
