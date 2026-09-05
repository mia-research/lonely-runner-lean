#!/usr/bin/env python3
"""Reconcile the two 'S+' definitions and check sigma oddness. Exact ints."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sympy import isprime, primitive_root
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn
from lift_sextant_rhombus_law_proof_v2 import reduced_basis

def analyze(p):
    chi2=chi2_table(p)
    eis,eps,beta,R1,R2,DET=build(p)
    sig,orient=sigma_fn(p,eis,eps,R1,R2,DET)
    if sig is None: return None
    H=(p-1)//2; g=primitive_root(p); rho=pow(g,(p-1)//6,p); lo=(p+1)//2
    s=[sig(x) for x in range(p)]
    # sigma oddness
    odd_ok = all(s[(p-x)%p]==-s[x] for x in range(1,p))
    odd_rate = sum(1 for x in range(1,p) if s[(p-x)%p]==-s[x])
    FLD=sum(s[x]*chi2(x) for x in range(p))
    Splus_full = sum(chi2(x) for x in range(p) if s[x]==1)      # master S+ (full, sigma=+1)
    Sminus_full= sum(chi2(x) for x in range(p) if s[x]==-1)
    signed_half= sum(s[x]*chi2(x) for x in range(1,H+1))        # audit_v2 signed1
    flap_chi2  = sum(chi2(x) for x in range(p) if s[x]!=0)      # sum chi2 over flap
    window=[x for x in range(1,H+1) if lo<=(rho*x)%p<=H+x]
    Sprime=sum(chi2(x) for x in window)
    return dict(p=p,m24=p%24,orient=orient,odd_ok=odd_ok,odd_rate=odd_rate,tot=p-1,
                FLD=FLD,Splus_full=Splus_full,Sminus_full=Sminus_full,signed_half=signed_half,
                flap_chi2=flap_chi2,Sprime=Sprime,
                FLD_eq_2Splus=(FLD==2*Splus_full),
                absSplus_eq_absSprime=(abs(Splus_full)==abs(Sprime)),
                flapchi2_zero=(flap_chi2==0))

def main():
    lo=int(sys.argv[1]) if len(sys.argv)>1 else 100
    hi=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    rows=[analyze(p) for p in range(lo,hi) if p%6==1 and isprime(p) and p!=7]
    rows=[r for r in rows if r]
    r7=[r for r in rows if r['m24'] in (7,19)]; n=len(r7)
    def fr(k): return f"{sum(1 for r in r7 if r[k])}/{n}"
    print(f"p=7 mod12 in [{lo},{hi}): {n}")
    print(f"  sigma ODD (sigma(-x)=-sigma(x)) all x       : {fr('odd_ok')}")
    print(f"  FLD == 2*Splus_full (master's S+)           : {fr('FLD_eq_2Splus')}")
    print(f"  |Splus_full| == |Sprime| (assembly's claim) : {fr('absSplus_eq_absSprime')}")
    print(f"  sum_flap chi2 == 0                          : {fr('flapchi2_zero')}")
    print(f"\n  detail (first 8):")
    print(f"  {'p':>5} {'m24':>3} {'odd?':>5} {'oddrate':>9} {'FLD':>5} {'2Splus':>6} {'Sm_full':>7} "
          f"{'sgnHalf':>7} {'flapX2':>6} {'Sprime':>6}")
    for r in r7[:8]:
        print(f"  {r['p']:>5} {r['m24']:>3} {str(r['odd_ok']):>5} {r['odd_rate']}/{r['tot']:<4} "
              f"{r['FLD']:>5} {2*r['Splus_full']:>6} {r['Sminus_full']:>7} {r['signed_half']:>7} "
              f"{r['flap_chi2']:>6} {r['Sprime']:>6}")

if __name__=='__main__':
    main()
