#!/usr/bin/env python3
"""fld_dual_mult_v1.py -- is the reduced-basis sigma a CHANGE OF VARIABLE of the rho-flap?
   sigma(s)=sign(frac(alpha s/p)-frac(beta s/p)) [orient '-'] or sign(frac+frac) [orient '+'].
   If beta ≡ rho*alpha (mod p) for a 6th root rho, then s'=alpha s maps sigma to the rho-flap and
   FLD = chi2(alpha)*(flap-lemmas object) -- making (B) a PROVED identity. Exact ints."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sympy import isprime, primitive_root
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def analyze(p):
    chi2=chi2_table(p)
    eis,eps,beta_cal,R1,R2,DET=build(p)
    sig,orient=sigma_fn(p,eis,eps,R1,R2,DET)
    if sig is None: return None
    def co(w):
        a,b=w; return Fr(a*R2[1]-b*R2[0],DET), Fr(b*R1[0]-a*R1[1],DET)
    # u(s)=frac(alpha s/p) ?  find alpha,beta = p*u(1),p*v(1) as residues; verify linearity
    u1,v1=co(eis(1))
    alpha=int(p*u1)%p; beta=int(p*v1)%p
    lin=True
    for s in range(1,p):
        u,v=co(eis(s))
        if int(p*u)%p!=(alpha*s)%p or int(p*v)%p!=(beta*s)%p: lin=False; break
    # 6th roots of unity mod p
    g=primitive_root(p); r6=[pow(g,k*(p-1)//6,p) for k in range(6)]  # {1,rho,...,rho^5}
    # relations: beta ≡ r*alpha ? alpha ≡ r*beta ?
    ainv=pow(alpha,p-2,p); binv=pow(beta,p-2,p)
    ratio_ba=(beta*ainv)%p          # beta/alpha
    ratio_ab=(alpha*binv)%p         # alpha/beta
    ba_is6th = ratio_ba in r6
    ab_is6th = ratio_ab in r6
    which_ba = r6.index(ratio_ba) if ba_is6th else None
    which_ab = r6.index(ratio_ab) if ab_is6th else None
    return dict(p=p,m24=p%24,orient=orient,alpha=alpha,beta=beta,lin=lin,
        ratio_ba=ratio_ba,ratio_ab=ratio_ab,ba_is6th=ba_is6th,ab_is6th=ab_is6th,
        which_ba=which_ba,which_ab=which_ab,x2alpha=chi2(alpha),x2beta=chi2(beta))

def main():
    lo=int(sys.argv[1]) if len(sys.argv)>1 else 100
    hi=int(sys.argv[2]) if len(sys.argv)>2 else 1000
    rows=[analyze(p) for p in range(lo,hi) if p%6==1 and isprime(p) and p!=7]
    rows=[r for r in rows if r]
    r7=[r for r in rows if r['m24'] in (7,19)]; n=len(r7)
    print(f"p=7 mod12 in [{lo},{hi}): {n}")
    print(f"  u(s)=frac(alpha s/p), v(s)=frac(beta s/p) LINEAR: {sum(r['lin'] for r in r7)}/{n}")
    print(f"  beta/alpha is a 6th root of unity              : {sum(r['ba_is6th'] for r in r7)}/{n}")
    print(f"  alpha/beta is a 6th root of unity              : {sum(r['ab_is6th'] for r in r7)}/{n}")
    from collections import Counter
    cba=Counter(r['which_ba'] for r in r7 if r['ba_is6th'])
    print(f"  which 6th-root power (beta/alpha=rho^k): {dict(cba)}   (k: 0=1,1=rho,...,5=rho^5)")
    print(f"\n  {'p':>5} {'m24':>3} {'or':>3} {'alpha':>5} {'beta':>5} {'b/a':>5} {'=rho^?':>6} {'x2(a)':>6}")
    for r in r7[:16]:
        print(f"  {r['p']:>5} {r['m24']:>3} {r['orient']:>3} {r['alpha']:>5} {r['beta']:>5} "
              f"{r['ratio_ba']:>5} {str(r['which_ba']):>6} {r['x2alpha']:>6}")

if __name__=='__main__':
    main()
