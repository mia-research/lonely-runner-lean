#!/usr/bin/env sage
# ROUTE 2 (decidable): can E's DLP enter A_new? By Tate, Hom(E,A_new)!=0 iff E and A_new share an
# isogeny factor iff L_E and L_new share a common root, i.e. gcd(L_E, L_new) != 1 over Q.
from sage.all import *
def L_new_of(p, cubic, A, B):
    a2,a1,a0 = cubic; T = polygen(QQ,'T'); s=[]
    for k in (1,2,3):
        q=p**k; Fq=GF(q); d=gcd(4,q-1); e=(q-1)//d; cnt=0
        for x in Fq:
            u=x**3+a2*x**2+a1*x+a0
            cnt += 1 if u==0 else (d if u**e==1 else 0)
        s.append(p**k+1-(cnt+1))
    s1,s2,s3=s; c1=-s1; c2=(s1**2-s2)//2; c3=(-s1**3+3*s1*s2-2*s3)//6
    Lc = 1+c1*T+c2*T**2+c3*T**3+p*c2*T**4+p**2*c1*T**5+p**3*T**6
    ap = EllipticCurve(GF(p),[A,B]).trace_of_frobenius()
    Le = 1-ap*T+p*T**2
    q_,r = Lc.quo_rem(Le)
    return (Le, q_ if r==0 else None)
print("ROUTE 2: gcd(L_E, L_new) -- nonzero-degree gcd would mean a shared isogeny factor (Hom != 0)")
print("  %-7s %-5s %-5s %-10s %-28s" % ("curve","p","p%4","E type","gcd(L_E,L_new)"))
for lab,cub,A,B in (("CM",(0,0,7),0,7), ("nonCM",(0,2,5),2,5)):
    for p in [pp for pp in prime_range(10,90) if pp%3==1]:
        if (4*A**3+27*B**2) % p == 0: continue
        Le,Ln = L_new_of(p,cub,A,B)
        if Ln is None: continue
        g = gcd(Le,Ln)
        ap = EllipticCurve(GF(p),[A,B]).trace_of_frobenius()
        etype = "ORD" if ap % p != 0 else "ss"
        print("  %-7s %-5d %-5d %-10s %-28s" % (lab,p,p%4,etype,g))
