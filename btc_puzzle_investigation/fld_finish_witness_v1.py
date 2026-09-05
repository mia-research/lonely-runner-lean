#!/usr/bin/env python3
"""fld_finish_witness_v1.py -- confirm the FINISH connects to the dagger (†):
   (a) canonical flap FLD_rho (rho = g^{(p-1)/6}, primitive 6th root) = +/- 6h  [dagger closes it]
   (b) FLD_rho = FLD_{rho^5}  (both primitive 6th roots agree; dagger's sgnsum(rho)=sgnsum(rho^-1))
   (c) dagger sign-sum:  Sig(rho)=sum_{s=1}^{H} chi2(s) sgn(rho s mod p - s) = 3h   [= (†)]
   (d) relation FLD_rho^canon(flap) vs 2*Sig(rho)(pure) -- how the flap object ties to (†).
   Exact ints/Fractions."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sympy import isprime, primitive_root
from _sigma_chi2_scan_v1 import chi2_table

def cent(v,p):
    v%=p; return v-p if v>p//2 else v
def classnum_neg(p):
    D=-p; h=0; a=1
    while 3*a*a<=p:
        for b in range(-a,a+1):
            num=b*b-D
            if num%(4*a): continue
            c=num//(4*a)
            if c<a: continue
            if (abs(b)==a or a==c) and b<0: continue
            h+=1
        a+=1
    return h
def FLDcanon(p,c,chi2):
    s=0
    for X in range(1,p):
        d=cent(X,p)-cent((c*X)%p,p)
        if abs(d)>Fr(p,2): s+=(1 if d>0 else -1)*chi2(X)
    return s
def Sig(p,c,chi2):   # dagger pure sign-sum over [1,H]
    H=(p-1)//2; s=0
    for x in range(1,H+1):
        r=(c*x)%p
        s+=chi2(x)*(1 if r>x else -1)
    return s

def main():
    lo=int(sys.argv[1]) if len(sys.argv)>1 else 100
    hi=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    r19=[]; r7all=[]
    for p in range(lo,hi):
        if p%6!=1 or not isprime(p) or p==7: continue
        if p%12!=7: continue
        chi2=chi2_table(p); g=primitive_root(p)
        rho=pow(g,(p-1)//6,p); rho5=pow(rho,5,p)
        Fr_=FLDcanon(p,rho,chi2); Fr5=FLDcanon(p,rho5,chi2); S=Sig(p,rho,chi2)
        d=dict(p=p,m24=p%24,Frho=Fr_,Frho5=Fr5,Sig=S,
                agree=(Fr_==Fr5), flap_eq_2sig=(Fr_==2*S))
        if p%24==19:
            h=classnum_neg(p); d['h']=h; d['is6h']=(abs(Fr_)==6*h); d['sig3h']=(abs(S)==3*h)
            r19.append(d)
        r7all.append(d)
    n=len(r7all); n19=len(r19)
    print(f"p=7 mod12 in [{lo},{hi}): {n}  (of which p=19 mod24: {n19})")
    print(f"  (a) |FLD_rho^canon| = 6h at p=19 mod24        : {sum(r['is6h'] for r in r19)}/{n19}")
    print(f"  (b) FLD_rho == FLD_{{rho^5}} (both prim 6th)   : {sum(r['agree'] for r in r7all)}/{n}")
    print(f"  (c) |Sig(rho)| = 3h  (= the dagger (†))       : {sum(r['sig3h'] for r in r19)}/{n19}")
    print(f"  (d) FLD_rho^canon == 2*Sig(rho)               : {sum(r['flap_eq_2sig'] for r in r7all)}/{n}")

if __name__=='__main__':
    main()
