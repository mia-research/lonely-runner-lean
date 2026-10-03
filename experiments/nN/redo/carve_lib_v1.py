# carve_lib_v1: carving profile of seven readings.  K_1=[1,7]; K_k = K_{k-1} ∩ C_k (closed windows, one-point windows kept).
# All Fractions.  Reuses path() (cascade_path_map_v1), clear_components/in_zone7 (ceil_k6_lib_v1), windows() (win_lib_v1) for cross-checks.
import sys, random
sys.path.insert(0, '.')
from fractions import Fraction as F
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0], globals())
from ceil_k6_lib_v1 import clear_components, in_zone7

def clear_pieces(r, H=F(7)):
    """closed pieces of C_r ∩ [1,H]: complement of the open zones ((8j-1)/r,(8j+1)/r), j>=1."""
    out = []; lo = F(0)
    j = 1
    while True:
        a = F(8*j - 1) / r
        if a >= H: break
        out.append((lo, a)); lo = F(8*j + 1) / r; j += 1
    out.append((lo, H if lo <= H else lo))
    res = []
    for a, b in out:
        a2 = max(a, F(1)); b2 = min(b, H)
        if a2 <= b2: res.append((a2, b2))
    return res

def inter(A, B):
    """intersection of two sorted lists of disjoint closed intervals; single points kept."""
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo <= hi: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out

def carve(rhos, order=None):
    """rhos sorted; order = permutation of indices 1..6 (reading 0 is the window [1,7]).  Returns list of K_k (k=1..7)."""
    K = [(F(1), F(7))]; seq = [K]
    for y in (order if order is not None else range(1, 7)):
        K = inter(K, clear_pieces(rhos[y])); seq.append(K)
    return seq

def profile(rhos):
    seq = carve(rhos); K7 = seq[-1]
    ns = tuple(len(K) for K in seq)
    onept = sum(1 for a, b in K7 if a == b)
    longest = max((b - a for a, b in K7), default=None)
    return seq, ns, onept, longest

def checks(rhos, rnd, nord=2):
    """exact checks.  returns dict."""
    rhos = sorted(rhos)
    seq, ns, onept, longest = profile(rhos)
    K7 = seq[-1]; K6 = seq[-2]
    d = dict(ns=ns, onept=onept, longest=longest)
    ok_order = True
    for _ in range(nord):
        o = list(range(1, 7)); rnd.shuffle(o)
        if carve(rhos, o)[-1] != K7: ok_order = False
    d['order_ok'] = ok_order
    # independent: clear set of all seven readings, from ceil_k6_lib (zones, sweep)
    d['cc_ok'] = (clear_components(rhos[1:], F(7)) == K7) if True else None
    steps, Rl = path(rhos)
    d['crosser'] = (len(K7) == 0)
    if K7: d['landing_ok'] = (Rl == K7[0][0])
    else: d['landing_ok'] = (Rl > 7)
    # K6 (readings 1..6) cross-check with clear_components
    d['k6_ok'] = (clear_components(rhos[:6], F(7)) == K6)
    # gate condition: every component of K6 inside one open zone of reading 7
    d['gate_cond'] = all(in_zone7(rhos[6], a, b) is not None for a, b in K6)
    d['lmax6'] = max((b - a for a, b in K6), default=None)
    d['W'] = all((b - a) < 2 / rhos[6] for a, b in K6)
    d['n6'] = len(K6)
    return d
