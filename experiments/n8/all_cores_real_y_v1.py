# E643 [PROVISIONAL: covering]: for every 6-subset C of [1, N] with gcd 1, is [3/8, y0] covered by the intervals served by C's own windows (y0 = 1/(4 w), w the widest window)?
# Exact Fractions.  usage: N.  A set is "certified" when no gap remains; the uncertified sets are listed.
import sys, math, itertools
from fractions import Fraction as F
from classes_lib_v1 import clear_iv, meet
N = int(sys.argv[1])
def certified(core):
    g = 0
    for d in core: g = math.gcd(g, d)
    T = F(1, g)
    J = clear_iv(F(core[0]), T)
    for s in core[1:]:
        J = meet(J, clear_iv(F(s), T))
        if not J: return None
    J = [(lo, hi) for lo, hi in J if hi >= lo and lo > 0]
    if not J: return None
    w = max(hi - lo for lo, hi in J); y0 = 1 / (4 * w)
    iv = []
    for lo, hi in J:
        for n in range(0, 80):
            a_, b_ = lo + F(n) * T, hi + F(n) * T
            k = 0
            while F(8 * k + 1, 8) / b_ <= y0:
                iv.append((F(8 * k + 1, 8) / b_, F(8 * k + 7, 8) / a_)); k += 1
    iv.sort(); cur = F(3, 8)
    for lo, hi in iv:
        if hi <= cur: continue
        if lo > cur: return False
        cur = hi
        if cur >= y0: return True
    return cur >= y0
bad = []; tot = 0; none = 0
for C in itertools.combinations(range(1, N + 1), 6):
    g = 0
    for d in C: g = math.gcd(g, d)
    if g != 1: continue
    tot += 1
    r = certified(C)
    if r is None: none += 1
    elif not r: bad.append(C)
print('N', N, 'gcd-1 six-subsets', tot, 'no window', none, 'uncertified (gap)', len(bad), bad[:20])
