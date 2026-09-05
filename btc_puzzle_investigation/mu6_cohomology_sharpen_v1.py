#!/usr/bin/env sage
# SHARPEN P-B: is there a genuine j=0 CM fingerprint on H^1_new, cleanly separated from geometry?
# v2 found CM 6/6 vs non-CM 5/6 "splits over Q(zeta12)" -- confounded because Q(i) c Q(zeta12) and the
# GEOMETRIC mu4 already puts ordinary-prime eigenvalues in Q(i). The clean discriminator is NOT "splits
# over Q(zeta12)" but "does the eigenvalue field CONTAIN sqrt(-3)?" -- sqrt(-3) is the CM part (Q(zeta12)
# = Q(i, sqrt-3)); Q(i) alone (any cubic, from w->iw) does NOT contain sqrt-3.
#
# COMMITTED PREDICTION (pre-reg): at ORDINARY primes (p=1 mod12), the CM cover w^4=x^3+7 has sqrt(-3) in
# its H^1_new eigenvalue field at EVERY such p (A_new has CM by Q(zeta12)); a generic non-CM cover does
# NOT (only Q(i), from mu4). FALSIFICATION: CM misses sqrt-3 at any ordinary p, or non-CM hits it at all.
# Two independent non-CM controls. Exact (splitting field over QQ; is_square exact).
from sage.all import *
def Lnew(p,cubic,A,B):
    a2,a1,a0=cubic; T=polygen(ZZ,'T'); s=[]
    for k in (1,2,3):
        q=p**k; Fq=GF(q); d=gcd(4,q-1); e=(q-1)//d; cnt=0
        for x in Fq:
            u=x**3+a2*x**2+a1*x+a0; cnt+= 1 if u==0 else (d if u**e==1 else 0)
        s.append(p**k+1-(cnt+1))
    s1,s2,s3=s; c1=-s1; c2=(s1**2-s2)//2; c3=(-s1**3+3*s1*s2-2*s3)//6
    Lc=1+c1*T+c2*T**2+c3*T**3+p*c2*T**4+p**2*c1*T**5+p**3*T**6
    ap=EllipticCurve(GF(p),[A,B]).trace_of_frobenius()
    q_,r=Lc.quo_rem(1-ap*T+p*T**2); return q_ if r==0 else None
def field_test(Ln):
    Pol=PolynomialRing(QQ,'T'); rec=Pol(list(reversed([QQ(c) for c in Ln.list()])))
    K=rec.splitting_field('a'); return K.absolute_degree(), K(-3).is_square(), K(-1).is_square()
prs=[p for p in prime_range(10,175) if p%12==1]   # ORDINARY primes only (p=1 mod4 and 1 mod3)
print("H^1_new eigenvalue field at ORDINARY primes (p=1 mod12): [K:Q], sqrt(-3) in K?, sqrt(-1) in K?")
print("committed: CM has sqrt(-3) at EVERY ordinary p; generic non-CM does not.")
for label,cubic,A,B in [("CM   x^3+7",(0,0,7),0,7),
                        ("nonCM x^3+2x+5",(0,2,5),2,5),
                        ("nonCM x^3+x+1 ",(0,1,1),1,1)]:
    m3hits=[]; tot=0
    print("\n[%s]"%label)
    for p in prs:
        if (4*A**3+27*B**2)%p==0: print("  p=%-4d SING"%p); continue
        Ln=Lnew(p,cubic,A,B)
        if Ln is None: print("  p=%-4d  L_E does not divide L_C"%p); continue
        deg,m3,m1=field_test(Ln); tot+=1; m3hits.append(m3)
        print("  p=%-4d  [K:Q]=%-2d  sqrt(-3)? %-5s  sqrt(-1)? %s"%(p,deg,m3,m1))
    print("  --> sqrt(-3) present at %d/%d ordinary primes"%(sum(m3hits),tot))
print("\n[done]")
