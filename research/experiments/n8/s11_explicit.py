"""S11: build an EXPLICIT admissible E (7 distinct speeds, gcd 1, E_div nonempty,
unit-complete) together with an explicit fibre b inside one of the two windows at which
the four unit runners ALONE cover Z/8 -- destroying the representative table in situ."""
from fractions import Fraction as F
from itertools import product
from math import gcd
from n8_fibre_core import bad, L_of, split, blocked_non, t_of, safe, div_ok

EMAX=120
WINDOWS=[("[2/7,2/5)",F(2,7),F(2,5),(1,4)),("[3/5,5/7)",F(3,5),F(5,7),(3,6))]

def speeds(rho): return list(range(rho,EMAX+1,8))

def find_cover(lo,hi):
    pts={lo,hi}
    for rho in (1,3,5,7):
        for e in speeds(rho):
            j=(e*lo.numerator)//lo.denominator
            while F(j,e)<hi:
                if lo<F(j,e)<hi: pts.add(F(j,e))
                j+=1
    pts=sorted(pts)
    out=[]
    for i in range(len(pts)-1):
        mid=(pts[i]+pts[i+1])/2
        opts={}
        for rho in (1,3,5,7):
            d={}
            for e in speeds(rho):
                t=(e*mid.numerator)//mid.denominator
                d.setdefault(bad(rho,t), e)
            opts[rho]=d
        for combo in product(*[list(opts[r].items()) for r in (1,3,5,7)]):
            u=set()
            for pair,_ in combo: u|=pair
            if len(u)==8:
                es=tuple(e for _,e in combo)
                out.append((pts[i],pts[i+1],es))
                break
        if len(out)>=400: break
    return out

for wname,lo,hi,exp in WINDOWS:
    cands=find_cover(lo,hi)
    built=None
    for (clo,chi,es) in cands:
        e1,e3,e5,e7=es
        if len(set(es))<4: continue
        for z in (2,4,6):                       # the one non-unit class
            for ez in range(z,200,8):
                if ez in es: continue
                for ed in range(8,400,8):       # the divisible runner
                    if ed in es or ed==ez: continue
                    E=tuple(sorted(es+(ez,ed)))
                    if len(E)!=6: continue
                    # need 7 speeds: add a twin in one unit class
                    for tw in range(1,300):
                        if tw%8 not in (1,3,5,7): continue
                        if tw in E: continue
                        EE=tuple(sorted(E+(tw,)))
                        if len(EE)!=7: continue
                        g=0
                        for e in EE: g=gcd(g,e)
                        if g!=1: continue
                        Ed,En=split(EE)
                        R=set(e%8 for e in En)
                        if not ({1,3,5,7}<=R and len(R)==5): continue
                        L=L_of(EE)
                        if L>60_000_000: continue
                        b_lo=clo.numerator*L//clo.denominator
                        for b in range(max(b_lo-1,1), b_lo+3):
                            x=F(b,L)
                            if not (clo<=x<chi): continue
                            blk=set()
                            for e in es: blk|=bad(e,t_of(e,b,L))
                            if len(blk)==8:
                                built=(EE,L,b,x,es,wname,exp,Ed,En); break
                        if built: break
                    if built: break
                if built: break
            if built: break
        if built: break
    if not built:
        print(f"window {wname}: no explicit E constructed under the search bounds"); continue
    EE,L,b,x,es,wn,exp,Ed,En=built
    print(f"=== window {wn}: representative table predicts uncovered {set(exp)} ===")
    print(f"E = {EE}")
    print(f"L = lcm(E) = {L},  N = 8L = {8*L}")
    print(f"E_div = {Ed}   E_non = {En}   R_non = {sorted(set(e%8 for e in En))}")
    print(f"fibre b = {b},  x = b/L = {x} = {float(x):.6f}  in [{F(*exp) if False else ''}{clo if False else ''}]")
    print(f"  window check: {F(2,7) if wn.startswith('[2') else F(3,5)} <= {x} < {F(2,5) if wn.startswith('[2') else F(5,7)} : "
          f"{(F(2,7)<=x<F(2,5)) if wn.startswith('[2') else (F(3,5)<=x<F(5,7))}")
    tot=set()
    for e in sorted(es):
        t=t_of(e,b,L); pr=sorted(bad(e,t))
        print(f"   unit e={e:5d} (rho={e%8}, q={e//8:4d})  t=floor(e*b/L)={t}  t mod 8={t%8}  blocks {pr}")
        tot|=set(pr)
    print(f"   UNION of the four UNIT runners alone = {sorted(tot)}   covers Z/8: {len(tot)==8}")
    print(f"   full blocked set over E_non = {sorted(blocked_non(En,b,L))}   safe: {safe(En,b,L)}")
    print()
