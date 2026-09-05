#!/usr/bin/env python3
"""fld_audit_v3.py -- REDO the flap-set comparison with the AUTHORITATIVE sigma (sigma_fn),
   not raw sign(u-v). Determines whether master-flap == flap-lemmas window, or different-but-equal-sum.
   Exact ints."""
import sys
from fractions import Fraction as Fr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sympy import isprime, primitive_root
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def cent(v,p):
    v%=p; return v-p if v>p//2 else v

def audit(p):
    chi2=chi2_table(p)
    eis,eps,beta,R1,R2,DET=build(p)
    sig,orient=sigma_fn(p,eis,eps,R1,R2,DET)
    if sig is None: return None
    H=(p-1)//2; g=primitive_root(p); rho=pow(g,(p-1)//6,p); lo=(p+1)//2
    pos={s for s in range(1,H+1) if sig(s)==1}
    neg={s for s in range(1,H+1) if sig(s)==-1}
    flap=pos|neg
    window={s for s in range(1,H+1) if lo<=(rho*s)%p<=H+s}
    # cent-flap positive = {s: cent(s)-cent(rho s)>p/2}; two-sided flap
    centflap={s for s in range(1,H+1) if abs(cent(s,p)-cent((rho*s)%p,p))>p/2}
    centwin ={s for s in range(1,H+1) if cent(s,p)-cent((rho*s)%p,p)>p/2}
    signed_half=sum(sig(s)*chi2(s) for s in range(1,H+1))
    Sprime=sum(chi2(s) for s in window)
    return dict(p=p,m24=p%24,orient=orient,
        win_eq_pos=(window==pos),win_eq_neg=(window==neg),
        win_eq_flap=(window==flap),win_sub_flap=(window<=flap),
        centwin_eq_window=(centwin==window),      # P1 Step1 (internal)
        centflap_eq_flap=(centflap==flap),        # cent-flap == master-flap ?
        sd_win_pos=len(window^pos),sd_win_neg=len(window^neg),
        sd_centflap_flap=len(centflap^flap),
        signed_half=signed_half,Sprime=Sprime,
        id_signed=(signed_half==Sprime),id_mag=(abs(signed_half)==abs(Sprime)))

def main():
    lo=int(sys.argv[1]) if len(sys.argv)>1 else 100
    hi=int(sys.argv[2]) if len(sys.argv)>2 else 2000
    rows=[audit(p) for p in range(lo,hi) if p%6==1 and isprime(p) and p!=7]
    rows=[r for r in rows if r]
    r7=[r for r in rows if r['m24'] in (7,19)]; n=len(r7)
    def fr(k): return f"{sum(1 for r in r7 if r[k])}/{n}"
    orients=set(r['orient'] for r in r7)
    print(f"p=7 mod12 in [{lo},{hi}): {n}   orientations used: {orients}")
    print(f"  P1 Step1: centwin == rho-window (internal)      : {fr('centwin_eq_window')}")
    print(f"  cent-flap  == master-flap (as SETS)             : {fr('centflap_eq_flap')}")
    print(f"  rho-window == master pos-flap                   : {fr('win_eq_pos')}")
    print(f"  rho-window == master neg-flap                   : {fr('win_eq_neg')}")
    print(f"  rho-window == master flap (unsigned)            : {fr('win_eq_flap')}")
    print(f"  rho-window subset master flap                   : {fr('win_sub_flap')}")
    print(f"  signed_half == Sprime (signed)                  : {fr('id_signed')}")
    print(f"  |signed_half| == |Sprime| (magnitude)           : {fr('id_mag')}")
    print(f"\n  {'p':>5} {'m24':>3} {'or':>3} {'sd(win,pos)':>11} {'sd(win,neg)':>11} "
          f"{'sd(cf,fl)':>9} {'sgnHalf':>7} {'Sprime':>6}")
    for r in r7[:12]:
        print(f"  {r['p']:>5} {r['m24']:>3} {r['orient']:>3} {r['sd_win_pos']:>11} {r['sd_win_neg']:>11} "
              f"{r['sd_centflap_flap']:>9} {r['signed_half']:>7} {r['Sprime']:>6}")

if __name__=='__main__':
    main()
