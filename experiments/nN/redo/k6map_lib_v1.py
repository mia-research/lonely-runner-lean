# k6map lib (v1): exact K6 components on [1,7]; reuses path() of cascade_path_map_v1.py, clear_components of ceil_k6_lib_v1.py (cross-check), allowed7 idea of ceil_allowed7_v1.py (H=7 here).
import sys
sys.path.insert(0, '.')
from fractions import Fraction as F
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0], globals())
from ceil_k6_lib_v1 import clear_components as cc_ref
def K6(rhos, H=F(7)):
    """closed components [a,b] (a<=b) of {R in [1,H] : in no open zone of the readings}. Independent implementation (sweep over zones sorted by entry)."""
    Z = []
    for r in rhos:
        j = 1
        while F(8*j - 1) / r < H:
            Z.append((F(8*j - 1) / r, F(8*j + 1) / r)); j += 1
    Z.sort()
    out = []; cur = F(1)          # cur: smallest point >= all processed zone exits and >= 1 (candidate clear point)
    for a, b in Z:
        if a >= cur:
            out.append((cur, a))  # [cur, a] clear (a is the open zone's entry; a itself is clear)
        if b > cur: cur = b
        # after a zone: points < b are blocked or already emitted; b itself is clear iff no other zone covers it (handled by later a >= cur test)
        if cur > H: return merge(out)
    if cur <= H: out.append((cur, H))
    return merge(out)
def merge(out):
    # a window [cur,a] followed by next window starting at cur'==a? cannot occur (cur'>=exit>a); drop nothing. Kept for symmetry.
    return out
def check_pointwise(rhos, comps, H=F(7)):
    """exact: every component endpoint is in no open zone; the point just outside each endpoint inside [1,H] is in a zone (strict)."""
    def blocked(R):
        return any(((R * r) % 8) < 1 or ((R * r) % 8) > 7 for r in rhos)
    for a, b in comps:
        if blocked(a) or blocked(b) or blocked((a + b) / 2): return False
    return True
def sixrhos(t): return [F(x) for x in t]
