# exact clear-set components of a subset of readings on [1, H]  (zones open; ties give point components)
from fractions import Fraction as F
def zones(r, H):
    out = []; j = 1
    while F(8*j - 1) / r < H:
        out.append((F(8*j - 1) / r, F(8*j + 1) / r, j)); j += 1
    return out
def clear_components(rhos, H=F(9)):
    """closed components [a,b] (a<=b) of {R in [1,H]} not in any open zone of the readings."""
    Z = sorted((a, b) for r in rhos for (a, b, j) in zones(r, H + 1))
    comps = []; cur = F(1)       # cur = left end of the current clear run
    maxend = None
    for a, b in Z:
        if b <= 1: continue
        if maxend is None:
            if a >= cur:
                comps.append((cur, a)); 
            maxend = b
        else:
            if a >= maxend:               # a == maxend: point maxend clear
                comps.append((maxend, a)); maxend = b
            else:
                maxend = max(maxend, b)
        if maxend > H: break
    if maxend is None: comps.append((F(1), H))
    elif maxend <= H: comps.append((maxend, H))
    # clip
    res = []
    for a, b in comps:
        if a > H: continue
        res.append((a, min(b, H)))
    return res
def in_zone7(r, a, b):
    """is [a,b] inside one open zone of reading r?"""
    j = int((a * r) // 8) ; 
    for jj in (j, j + 1):
        if jj >= 1 and F(8*jj - 1) / r < a and b < F(8*jj + 1) / r: return jj
    return None
