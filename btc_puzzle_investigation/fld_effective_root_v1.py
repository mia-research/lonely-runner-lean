#!/usr/bin/env python3
"""fld_effective_root_v1.py -- RESOLVE the enlarged null. Claim under test:
   the EFFECTIVE multiplier c_eff = (c if orient='-' else -c) is ALWAYS a primitive 6th root,
   so |FLD| = |FLD_{c_eff}('-')| = 6h is the DAGGER case for EVERY prime -- not 31%.
   Uses: FLD_c('+') = FLD_{-c}('-') exactly.  Exact ints/Fractions."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sympy import isprime, primitive_root, n_order
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def cent(v,p):
    v%=p; return v-p if v>p//2 else v

def FLDc_minus(p,c,chi2):
    s=0
    for x in range(1,p):
        d=cent(x,p)-cent((c*x)%p,p)
        if abs(d)>Fr(p,2): s+=(1 if d>0 else -1)*chi2(x)
    return s

def classnum_neg(p):
    D=-p; h=0; a=1
    while 3*a*a<=p:
        for b in range(-a,a+1):
            num=b*b-D
            if num%(4*a): continue
            cc=num//(4*a)
            if cc<a: continue
            if (abs(b)==a or a==cc) and b<0: continue
            h+=1
        a+=1
    return h

def analyze(p):
    chi2=chi2_table(p)
    eis,eps,beta_cal,R1,R2,DET=build(p)
    sig,orient=sigma_fn(p,eis,eps,R1,R2,DET)
    if sig is None: return None
    def co(w):
        a,b=w; return Fr(a*R2[1]-b*R2[0],DET), Fr(b*R1[0]-a*R1[1],DET)
    u1,v1=co(eis(1)); alpha=int(p*u1)%p; beta=int(p*v1)%p
    c=(beta*pow(alpha,p-2,p))%p
    c_eff = c if orient=='-' else (-c)%p
    ord_ceff = n_order(c_eff,p)
    FLD=sum(sig(x)*chi2(x) for x in range(p))
    FLD_via_ceff = chi2(alpha)*FLDc_minus(p,c_eff,chi2)
    h=classnum_neg(p) if p%24==19 else None
    return dict(p=p,m24=p%24,orient=orient,c=c,c_eff=c_eff,ord_ceff=ord_ceff,
        FLD=FLD,FLD_via_ceff=FLD_via_ceff,
        match=(FLD==FLD_via_ceff),
        ceff_is_prim6=(ord_ceff==6),
        val6h=(abs(FLD)==6*h) if h else (FLD==0))

def main():
    lo=int(sys.argv[1]) if len(sys.argv)>1 else 100
    hi=int(sys.argv[2]) if len(sys.argv)>2 else 4000
    rows=[analyze(p) for p in range(lo,hi) if p%6==1 and isprime(p) and p!=7]
    rows=[r for r in rows if r]
    r7=[r for r in rows if r['m24'] in (7,19)]; n=len(r7)
    print(f"p=7 mod12 in [{lo},{hi}): {n}")
    print(f"  c_eff = (c if '-' else -c) is a PRIMITIVE 6th root (order 6): {sum(r['ceff_is_prim6'] for r in r7)}/{n}")
    print(f"  FLD == chi2(alpha)*FLD_{{c_eff}}('-')  (dagger form)         : {sum(r['match'] for r in r7)}/{n}")
    r19=[r for r in r7 if r['m24']==19]
    print(f"  |FLD| == 6h at p=19 mod24                                    : {sum(r['val6h'] for r in r19)}/{len(r19)}")
    print(f"  FLD == 0 at p=7 mod24                                        : {sum(r['val6h'] for r in r7 if r['m24']==7)}/{sum(1 for r in r7 if r['m24']==7)}")
    from collections import Counter
    print(f"  order of c_eff distribution: {dict(Counter(r['ord_ceff'] for r in r7))}")
    print(f"\n  {'p':>5} {'m24':>3} {'or':>3} {'c':>5} {'c_eff':>5} {'ord':>4} {'FLD':>5} {'viaCeff':>7} {'match':>6}")
    for r in r7[:12]:
        print(f"  {r['p']:>5} {r['m24']:>3} {r['orient']:>3} {r['c']:>5} {r['c_eff']:>5} {r['ord_ceff']:>4} "
              f"{r['FLD']:>5} {r['FLD_via_ceff']:>7} {str(r['match']):>6}")

if __name__=='__main__':
    main()
