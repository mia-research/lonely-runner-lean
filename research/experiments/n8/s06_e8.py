"""S06: hand-built E with E_div == {8} exactly (so B_lit == B_hon and the assumed
framework theorem IS sound).  Test the window claim there."""
from math import gcd
from n8_fibre_core import L_of, split, safe, div_ok, witness_from_fibre, blocked_non, sector

UNITS={1,3,5,7}
def unit_complete(En):
    R=set(e%8 for e in En); return UNITS<=R and len(R)==5

def report(E):
    L=L_of(E); Ed,En=split(E)
    assert Ed==[8], Ed
    lo,hi=-(-L//8),(7*L)//8
    W=[(-(-2*L//7),(2*L)//5),(-(-3*L//5),(5*L)//7)]
    inw=lambda b: any(a<=b<z for a,z in W)
    s=0; sw=0; ex=None; exw=None; tf=0
    for b in range(lo,hi+1):
        if safe(En,b,L):
            s+=1
            if ex is None: ex=b
            if witness_from_fibre(E,b) is None: tf+=1
            if inw(b):
                sw+=1
                if exw is None: exw=b
    print(f"E={E} L={L} R_non={sorted(set(e%8 for e in En))} |B|={hi-lo+1}")
    print(f"   safe fibres in B = {s}  (first {ex});  inside the two windows = {sw} (first {exw})")
    print(f"   witness failures among safe b in B_lit: {tf}   [0 = assumed theorem holds here]")
    return s,sw

cands=[]
base=[1,2,3,5,7,8]
for X in range(9,80):
    if X%8==0 or X in base: continue
    E=tuple(sorted(base+[X]))
    Ed,En=split(E)
    if Ed!=[8]: continue
    if not unit_complete(En): continue
    if L_of(E)>3_000_000: continue
    cands.append(E)
print("candidates with base {1,2,3,5,7,8}:", len(cands))
for E in cands[:14]:
    report(E); print()
