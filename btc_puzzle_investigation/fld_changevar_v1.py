#!/usr/bin/env python3
"""fld_changevar_v1.py -- THE FIXED TEST. Verify FLD = chi2(alpha) * FLD_c, where FLD_c is the
   CANONICAL single-multiplier flap FLD for c = beta/alpha = rho^k. This turns bridge (B) into a
   proved change of variable. Then check |FLD_c| = 6h per 6th-root power k. Exact ints/Fractions."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sympy import isprime, primitive_root
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

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

def cent(v,p):
    v%=p; return v-p if v>p//2 else v

def canon_flap_sign(x,c,p,plus=False):
    """sign(cent(x)-cent(cx)) [or +] on flap |.|>p/2, canonical single-multiplier flap.
       u,v = co(eis(.)) are CENTERED lattice coords = cent(.)/p, not frac in [0,1)."""
    x%=p
    if x==0: return 0
    a=cent(x,p); b=cent((c*x)%p,p)
    d=(a+b) if plus else (a-b)
    if abs(d)<=Fr(p,2): return 0
    return 1 if d>0 else -1

def analyze(p):
    chi2=chi2_table(p)
    eis,eps,beta_cal,R1,R2,DET=build(p)
    sig,orient=sigma_fn(p,eis,eps,R1,R2,DET)
    if sig is None: return None
    def co(w):
        a,b=w; return Fr(a*R2[1]-b*R2[0],DET), Fr(b*R1[0]-a*R1[1],DET)
    u1,v1=co(eis(1)); alpha=int(p*u1)%p; beta=int(p*v1)%p
    ainv=pow(alpha,p-2,p); c=(beta*ainv)%p
    g=primitive_root(p); r6=[pow(g,k*(p-1)//6,p) for k in range(6)]
    k=r6.index(c) if c in r6 else None
    FLD=sum(sig(x)*chi2(x) for x in range(p))
    # canonical flap FLD for multiplier c (orient '-': frac(x)-frac(cx); orient '+': need frac(x)+frac(cx)?)
    plus=(orient=='+')
    FLDc=sum(canon_flap_sign(x,c,p,plus)*chi2(x) for x in range(p))
    x2a=chi2(alpha)
    return dict(p=p,m24=p%24,orient=orient,k=k,c=c,alpha=alpha,x2a=x2a,
        FLD=FLD,FLDc=FLDc,ident=(FLD==x2a*FLDc),
        h=(classnum_neg(p) if p%24==19 else None))

def main():
    lo=int(sys.argv[1]) if len(sys.argv)>1 else 100
    hi=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    rows=[analyze(p) for p in range(lo,hi) if p%6==1 and isprime(p) and p!=7]
    rows=[r for r in rows if r]
    r7=[r for r in rows if r['m24'] in (7,19)]; n=len(r7)
    print(f"p=7 mod12 in [{lo},{hi}): {n}")
    print(f"  IDENTITY  FLD == chi2(alpha) * FLD_c  (change of var): {sum(r['ident'] for r in r7)}/{n}")
    r19=[r for r in r7 if r['m24']==19]
    print(f"  |FLD_c| == 6h at p=19 mod24                          : "
          f"{sum(abs(r['FLDc'])==6*r['h'] for r in r19)}/{len(r19)}")
    print(f"  FLD_c == 0 at p=7 mod24                              : "
          f"{sum(r['FLDc']==0 for r in r7 if r['m24']==7)}/{sum(1 for r in r7 if r['m24']==7)}")
    from collections import Counter
    print(f"  k distribution (c=rho^k): {dict(Counter(r['k'] for r in r7))}")
    print(f"  k by class: 6th-root k in 1,5: {sum(1 for r in r7 if r['k'] in (1,5))}  "
          f"cube-root k in 2,4: {sum(1 for r in r7 if r['k'] in (2,4))}")
    # is the identity+value clean across BOTH root classes?
    for cls,ks in [('6th-root (k=1,5)',(1,5)),('cube-root (k=2,4)',(2,4))]:
        sub=[r for r in r19 if r['k'] in ks]
        print(f"    {cls}: |FLD_c|=6h {sum(abs(r['FLDc'])==6*r['h'] for r in sub)}/{len(sub)}")
    print(f"\n  {'p':>5} {'m24':>3} {'or':>3} {'k':>2} {'x2a':>4} {'FLD':>5} {'FLDc':>5} {'x2a*FLDc':>8} {'ident':>6} {'6h':>4}")
    for r in r7[:14]:
        print(f"  {r['p']:>5} {r['m24']:>3} {r['orient']:>3} {str(r['k']):>2} {r['x2a']:>4} "
              f"{r['FLD']:>5} {r['FLDc']:>5} {r['x2a']*r['FLDc']:>8} {str(r['ident']):>6} "
              f"{str(6*r['h']) if r['h'] else '-':>4}")

if __name__=='__main__':
    main()
