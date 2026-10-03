# tmpl_lib_v1 -- K6 template of an arrangement (exact Fractions).  Reuses clear_components / in_zone7 (ceil_k6_lib_v1.py).
import sys
from fractions import Fraction as F
exec(open('ceil_k6_lib_v1.py').read())
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])   # path(), outcome()

def _lap(x):
    """x Fraction; return j>=1 if x == 8j, else None"""
    if x.denominator == 1 and x.numerator > 0 and x.numerator % 8 == 0: return x.numerator // 8
    return None

def left_labels(v, rhos6):
    L = []
    if v == 1: L.append(('R1',))
    for y, r in enumerate(rhos6, 1):
        j = _lap(v * r - 1)          # exit (8j+1)/r == v
        if j: L.append(('x', y, j))
    return tuple(L)

def right_labels(v, rhos6):
    L = []
    if v == 7: L.append(('R7',))
    for y, r in enumerate(rhos6, 1):
        j = _lap(v * r + 1)          # entry (8j-1)/r == v
        if j: L.append(('e', y, j))
    return tuple(L)

def windows(rhos):
    return clear_components(list(rhos[:6]), F(7))

def template(rhos):
    """returns (template, windows).  template = tuple of (left labels, right labels, one-point flag), left to right."""
    r6 = list(rhos[:6]); W = windows(rhos); T = []
    for a, b in W:
        la, lb = left_labels(a, r6), right_labels(b, r6)
        assert la and lb, (rhos, a, b, la, lb)
        T.append((la, lb, a == b))
    return tuple(T), W

def gate(rhos, W):
    return all(in_zone7(rhos[6], a, b) is not None for a, b in W)

def lab(l):
    return '&'.join('R1' if t[0] == 'R1' else 'R7' if t[0] == 'R7' else '%s%d.%d' % t for t in l)
def tstr(T):
    return ' '.join('[%s,%s%s' % (lab(l), lab(r), ']pt' if p else ']') for l, r, p in T)

def r2_set(rhos):
    """exact set of rho_7 > rho_6 for which every window of K6 lies in one open zone of reading 7:
    intersection over windows [a,b] of the union over j>=1 of the open intervals ((8j-1)/a,(8j+1)/b)  (nonempty iff 8j(b-a) < a+b).
    returns (sorted list of open intervals, unbounded flag); unbounded=True (list None) iff every window is a single point."""
    W = windows(rhos); r6 = rhos[5]
    wide = [(a, b) for a, b in W if a < b]; pts = [(a, b) for a, b in W if a == b]
    if not wide: return None, True
    def jtop(a, b):      # largest j with 8j(b-a) < a+b (0 if none)
        q = (a + b) / (8 * (b - a)); j = int(q)
        if j == q: j -= 1
        return j
    B = min((8 * jtop(a, b) + 1) / b for a, b in wide if jtop(a, b) >= 1) if all(jtop(a, b) >= 1 for a, b in wide) else None
    if B is None: return [], False
    sets = []
    for a, b in W:
        s = []; j = max(1, int((r6 * b - 1) // 8))      # first j with (8j+1)/b could exceed r6
        while True:
            lo = F(8 * j - 1) / a
            if lo >= B: break
            hi = F(8 * j + 1) / b
            if lo < hi and hi > r6: s.append((lo, hi))
            j += 1
        sets.append(s)
    cur = [(r6, B)]
    for s in sets:
        s = sorted(s); new = []
        for l1, h1 in cur:
            for l2, h2 in s:
                lo, hi = max(l1, l2), min(h1, h2)
                if lo < hi: new.append((lo, hi))
        cur = sorted(new)
        if not cur: break
    return cur, False
