"""S09: the crux (task Point 1).  Find an explicit admissible E and a fibre b INSIDE one of
the two windows at which the FOUR UNIT RUNNERS ALONE already block all of Z/8 -- i.e. the
representative-speed table {1,4} / {3,6} is destroyed by non-representative speeds."""
from itertools import combinations, product
from math import gcd
from fractions import Fraction as F
from n8_fibre_core import L_of, split, safe, bad, blocked_non, t_of

def divisors(n):
    d=[];i=1
    while i*i<=n:
        if n%i==0:
            d.append(i)
            if i!=n//i: d.append(n//i)
        i+=1
    return sorted(d)

def gen_E(L):
    D=divisors(L); Ddiv=[d for d in D if d%8==0]
    if not Ddiv: return
    cls={r:[d for d in D if d%8==r] for r in range(1,8)}
    for z in (2,4,6):
        classes=[1,3,5,7,z]
        if any(not cls[r] for r in classes): continue
        for base in product(*[cls[r] for r in classes]):
            base=tuple(sorted(base))
            for dv in combinations(Ddiv,2):
                E=tuple(sorted(base+dv))
                if len(set(E))==7: yield E
            for dcls in classes:
                for extra in cls[dcls]:
                    if extra in base: continue
                    non=tuple(sorted(base+(extra,)))
                    for dv in Ddiv:
                        E=tuple(sorted(non+(dv,)))
                        if len(set(E))==7: yield E

found=[]
seen=set()
for L in range(8,601,8):
    for E in gen_E(L):
        if E in seen or L_of(E)!=L: continue
        g=0
        for e in E: g=gcd(g,e)
        if g!=1: continue
        seen.add(E)
        Ed,En=split(E)
        # pick ONE representative per unit class (the four unit runners)
        units={}
        for e in En:
            units.setdefault(e%8, []).append(e)
        if not all(r in units for r in (1,3,5,7)): continue
        W=[(-(-2*L//7),(2*L)//5,"[2/7,2/5)","{1,4}"),(-(-3*L//5),(5*L)//7,"[3/5,5/7)","{3,6}")]
        for a,z,wn,exp in W:
            for b in range(a,z):
                for combo in product(*[units[r] for r in (1,3,5,7)]):
                    blk=set()
                    for e in combo: blk |= bad(e, t_of(e,b,L))
                    if len(blk)==8:
                        found.append((E,L,b,wn,exp,combo,F(b,L)))
                        break
                else:
                    continue
                break
            else:
                continue
            break
        if len(found)>=6: break
    if len(found)>=6: break

print("Explicit destructions of the representative table (4 units alone cover Z/8 inside a window):")
for E,L,b,wn,exp,combo,x in found:
    print(f"\n  E={E}  L={L}")
    print(f"  window {wn}: representative table predicts uncovered {exp}")
    print(f"  fibre b={b},  x=b/L={x}  (check {F(2,7)} <= {x} < {F(2,5)}  or  {F(3,5)} <= {x} < {F(5,7)})")
    print(f"  unit runners used (rho -> e): " + ", ".join(f"{e%8}->{e}" for e in combo))
    tot=set()
    for e in combo:
        t=t_of(e,b,L); bb=sorted(bad(e,t))
        print(f"     e={e:4d} (rho={e%8}, q={e//8})  t=floor({e}*{b}/{L})={t}  t mod 8={t%8}  blocks {bb}")
        tot|=set(bb)
    print(f"     UNION over the four units = {sorted(tot)}  -> covers Z/8: {len(tot)==8}")
