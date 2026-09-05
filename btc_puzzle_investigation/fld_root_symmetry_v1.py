#!/usr/bin/env python3
"""fld_root_symmetry_v1.py -- AUDIT the '69% not proved' claim. Compute the canonical flap
   FLD_c for ALL nontrivial 6th roots c=rho^k (k=1..5) and find the relations. If FLD_{cube}
   = +/- FLD_{6th} by a change of variable, the cube-root case reduces to the proved case and
   |FLD|=6h is proved for ALL primes. Exact ints/Fractions."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sympy import isprime, primitive_root
from _sigma_chi2_scan_v1 import chi2_table

def cent(v,p):
    v%=p; return v-p if v>p//2 else v

def FLDc(p,c,chi2):
    """canonical '-' flap: sign(cent(x)-cent(cx)) on |.|>p/2, weighted chi2."""
    s=0
    for x in range(1,p):
        d=cent(x,p)-cent((c*x)%p,p)
        if abs(d)>Fr(p,2):
            s+=(1 if d>0 else -1)*chi2(x)
    return s

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

def analyze(p):
    chi2=chi2_table(p)
    g=primitive_root(p); r6=[pow(g,k*(p-1)//6,p) for k in range(6)]
    F={k:FLDc(p,r6[k],chi2) for k in (1,2,3,4,5)}   # k=3 -> c=-1
    h=classnum_neg(p) if p%24==19 else None
    return dict(p=p,m24=p%24,h=h,F=F,x2_2=chi2(2))

def main():
    lo=int(sys.argv[1]) if len(sys.argv)>1 else 100
    hi=int(sys.argv[2]) if len(sys.argv)>2 else 1200
    rows=[analyze(p) for p in range(lo,hi) if p%6==1 and isprime(p) and p!=7]
    r7=[r for r in rows if r['m24'] in (7,19)]; n=len(r7)
    print(f"p=7 mod12 in [{lo},{hi}): {n}")
    # |FLD_{rho^k}| == 6h for each nontrivial k (k=3 is c=-1, expect 0)
    r19=[r for r in r7 if r['m24']==19]
    for k in (1,2,3,4,5):
        cnt=sum(1 for r in r19 if abs(r['F'][k])==6*r['h']) if k!=3 else sum(1 for r in r19 if r['F'][k]==0)
        tag='|FLD_c|=6h' if k!=3 else 'FLD_c=0'
        print(f"  k={k} (c=rho^{k}): {tag} at p=19mod24 : {cnt}/{len(r19)}")
    # relations (over ALL p=7mod12): FLD_{k} vs FLD_{6-k}=FLD_{c^-1}; and FLD_{k} vs FLD_{k+3}=FLD_{-c}
    def rel(f):
        return f"{sum(1 for r in r7 if f(r))}/{n}"
    print(f"\n  FLD_{{rho^5}} == +/- FLD_{{rho}}      (c^-1)         : {rel(lambda r: abs(r['F'][5])==abs(r['F'][1]))}")
    print(f"  FLD_{{rho^4}} == +/- FLD_{{rho^2}}    (c^-1)         : {rel(lambda r: abs(r['F'][4])==abs(r['F'][2]))}")
    print(f"  FLD_{{rho^2}} == +/- FLD_{{rho}}      (cube vs 6th)  : {rel(lambda r: abs(r['F'][2])==abs(r['F'][1]))}")
    print(f"  FLD_{{rho^4}} == +/- FLD_{{rho}}      (cube vs 6th)  : {rel(lambda r: abs(r['F'][4])==abs(r['F'][1]))}")
    print(f"  ALL of |FLD_{{rho}}|,|rho^2|,|rho^4|,|rho^5| equal   : "
          f"{rel(lambda r: len({abs(r['F'][k]) for k in (1,2,4,5)})==1)}")
    print(f"\n  {'p':>5} {'m24':>3} {'h':>3} {'F_r1':>5} {'F_r2':>5} {'F_r3':>5} {'F_r4':>5} {'F_r5':>5}")
    for r in r7[:16]:
        print(f"  {r['p']:>5} {r['m24']:>3} {str(r['h']):>3} "
              f"{r['F'][1]:>5} {r['F'][2]:>5} {r['F'][3]:>5} {r['F'][4]:>5} {r['F'][5]:>5}")

if __name__=='__main__':
    main()
