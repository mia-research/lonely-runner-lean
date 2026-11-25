"""E949: read island_vs_pass_v1 pickles: need and extent by reading and class (floats steer only; the split tests are exact)."""
import pickle, glob
from fractions import Fraction as Fr
from collections import Counter, defaultdict
out = []
for f in sorted(glob.glob('island_vs_pass_v1_part*.pkl')): out += pickle.load(open(f, 'rb'))
med = lambda xs: sorted(xs)[len(xs) // 2] if xs else None
D = defaultdict(list); c = Counter()
for idx, k, kc, role, v0, L_, R_, a, b, P in out:
    eL = (v0 - L_) / v0; eR = (R_ - v0) / v0
    left = [(l, h, m) for l, h, m in P if h <= v0]
    nL = (v0 - max(left)[1]) / v0 if left else None
    D[(k, kc, 'extent left')].append(float(eL)); D[(k, kc, 'extent right')].append(float(eR))
    if nL is not None: D[(k, kc, 'need left')].append(float(nL))
    # the gap in R between W_k's start a and the reading's last exit before a, relative to a (exact)
    from math import floor
    E = Fr(1, 8); m = floor(v0 * a + E); x = (m + E) / v0
    D[(k, kc, 'gap (a - last exit)/a')].append(float((a - x) / a))
    D[(k, kc, 'window length (b - a)/a')].append(float((b - a) / a))
    c[(k, kc)] += 1
for key in sorted(D, key=str):
    xs = D[key]; print('%-45s n %5d  median %.3g  min %.3g  max %.3g (floats, steer only)' % (key, len(xs), med(xs), min(xs), max(xs)))
