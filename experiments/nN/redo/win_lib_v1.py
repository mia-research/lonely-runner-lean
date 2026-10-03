# Exact lonely-window machinery.  Zones of reading r: ((8j-1)/r,(8j+1)/r), j>=1, open.  Windows: closed gaps of the union of open zones in [1,L].
from fractions import Fraction as F
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])

def norm(rhos):
    rhos = sorted(F(r) for r in rhos); m = rhos[0]
    return [r / m for r in rhos]

def windows(rhos, L=23):
    L = F(L); zs = []
    for r in rhos:
        j = 1
        while True:
            a = F(8 * j - 1) / r
            if a >= L: break
            b = F(8 * j + 1) / r
            if b > 1: zs.append((a, b))
            j += 1
    zs.sort()
    cur = F(1); out = []
    for a, b in zs:
        if a >= cur:               # closed gap [cur, a]; degenerate when a == cur (point not inside any open zone)
            out.append((cur, a))
            cur = b
        elif b > cur:
            cur = b
    if cur <= L: out.append((cur, L))
    return out

def clear(R, rhos):                 # exact predicate, same convention as path(): blocked iff position in (-1,1) mod 8
    return not any(blocks(R, r) for r in rhos)

def verify(rhos, ws, L=23):
    """independent exact check: endpoints and midpoints of windows clear; midpoint of each gap blocked (gaps incl. before first/after last)."""
    for lo, hi in ws:
        if not clear(lo, rhos) or not clear(hi, rhos) or not clear((lo + hi) / 2, rhos): return False
    pts = [F(1)] + [x for w in ws for x in w] + [F(L)]
    # gaps between consecutive windows: (hi_i, lo_{i+1}) must be blocked at midpoint and (when nonempty) at every tested interior point
    for i in range(len(ws) - 1):
        a, b = ws[i][1], ws[i + 1][0]
        if not (a < b): return False
        if clear((a + b) / 2, rhos): return False
    if ws and ws[0][0] > 1 and clear((1 + ws[0][0]) / 2, rhos): return False
    if ws and ws[-1][1] < L and clear((ws[-1][1] + L) / 2, rhos): return False
    if not ws and clear((1 + F(L)) / 2, rhos): return False
    return True
