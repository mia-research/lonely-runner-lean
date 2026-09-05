#!/usr/bin/env python3
"""fld_lemma_witness_v1.py -- exact numerical witness for EVERY step of the change-of-variable
   lemma, so the written proof asserts nothing unchecked. Exact ints/Fractions only."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sympy import isprime, primitive_root, n_order
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, enorm

def cent(v,p):
    v%=p; return v-p if v>p//2 else v

def unit_coeffs(R1,R2):
    """find integer mu=m+n*omega with R2 = mu*R1 in Z[omega]; return (m,n) or None.
       (m+n w)(x+y w) = (mx - ny) + (nx + (m-n) y) w   [using w^2=w-... NO: w^2=-1-w]"""
    x,y=R1; X,Y=R2
    # X = m x - n y ; Y = n x + (m-n) y  -> solve for m,n
    # from these: Y = n x + m y - n y ; and X = m x - n y
    # solve linear system: [x, -y; y, x - y] [m;n]... let's just brute small m,n
    for m in range(-3,4):
        for n in range(-3,4):
            if (m*x - n*y, n*x + (m-n)*y)==(X,Y): return (m,n)
    return None

def witness(p):
    chi2=chi2_table(p)
    R1,R2=reduced_basis(p)
    DET=R1[0]*R2[1]-R1[1]*R2[0]
    eis,eps,beta_cal,R1b,R2b,DETb=build(p)
    sig,orient=sigma_fn(p,eis,eps,R1b,R2b,DETb)
    if sig is None: return None
    eps_sign = 1 if DET>0 else -1
    # (i) both basis vectors minimal, norm p
    normok = (enorm(R1)==p and enorm(R2)==p)
    # (ii) |DET| = p
    detok = (abs(DET)==p)
    # (iii) R2 = mu*R1, mu a unit (m^2-mn+n^2=1)
    mn=unit_coeffs(R1,R2); unitok = (mn is not None and (mn[0]**2-mn[0]*mn[1]+mn[1]**2)==1)
    # (iv) alpha = eps*R2[1], beta = -eps*R1[1]; u(X)=cent(alpha X)/p, v=cent(beta X)/p
    alpha=(eps_sign*R2[1])%p; beta=(-eps_sign*R1[1])%p
    def co(w):
        a,b=w; return Fr(a*R2b[1]-b*R2b[0],DETb), Fr(b*R1b[0]-a*R1b[1],DETb)
    coordok=True
    for X in range(1,p):
        u,v=co(eis(X))
        if u!=Fr(cent(alpha*X,p),p) or v!=Fr(cent(beta*X,p),p): coordok=False; break
    # (v) beta/alpha in mu6
    c=(beta*pow(alpha,p-2,p))%p; c_in_mu6=(pow(c,6,p)==1 and c!=0)
    ord_c=n_order(c,p)
    # (vi) change of variable FLD = chi2(alpha)*FLD_{c_eff}
    c_eff = c if orient=='-' else (-c)%p
    def FLDc_minus(cc):
        s=0
        for X in range(1,p):
            d=cent(X,p)-cent((cc*X)%p,p)
            if abs(d)>Fr(p,2): s+=(1 if d>0 else -1)*chi2(X)
        return s
    FLD=sum(sig(X)*chi2(X) for X in range(p))
    cvok=(FLD==chi2(alpha)*FLDc_minus(c_eff))
    return dict(p=p,m24=p%24,orient=orient,mn=mn,alpha=alpha,beta=beta,c=c,ord_c=ord_c,
        c_eff=c_eff,ord_ceff=n_order(c_eff,p),
        normok=normok,detok=detok,unitok=unitok,coordok=coordok,c_in_mu6=c_in_mu6,cvok=cvok)

def main():
    lo=int(sys.argv[1]) if len(sys.argv)>1 else 100
    hi=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    rows=[witness(p) for p in range(lo,hi) if p%6==1 and isprime(p) and p!=7]
    rows=[r for r in rows if r]
    r7=[r for r in rows if r['m24'] in (7,19)]; n=len(r7)
    print(f"p=7 mod12 in [{lo},{hi}): {n}")
    for key,desc in [('normok','(i) enorm(R1)=enorm(R2)=p (both minimal)'),
                     ('detok','(ii) |DET|=p'),
                     ('unitok','(iii) R2=mu*R1, mu a unit of Z[omega]'),
                     ('coordok','(iv) u=cent(alpha X)/p, v=cent(beta X)/p, alpha=eps R2_1, beta=-eps R1_1'),
                     ('c_in_mu6','(v) c=beta/alpha in mu6'),
                     ('cvok','(vi) FLD = chi2(alpha)*FLD_{c_eff}')]:
        print(f"  {desc:<62}: {sum(r[key] for r in r7)}/{n}")
    from collections import Counter
    print(f"  order(c)=beta/alpha distribution : {dict(Counter(r['ord_c'] for r in r7))}")
    print(f"  order(c_eff) distribution        : {dict(Counter(r['ord_ceff'] for r in r7))}")
    print(f"  unit mu=(m,n) distribution       : {dict(Counter(r['mn'] for r in r7))}")
    print(f"  orient vs order(c): "
          f"{dict(Counter((r['orient'],r['ord_c']) for r in r7))}")

if __name__=='__main__':
    main()
