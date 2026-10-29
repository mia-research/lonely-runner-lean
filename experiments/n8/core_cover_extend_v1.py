# E640: how many left-over sets at larger N are already contained in one of the 53 chosen cores, and how many new cores the rest would need.  Exact.  usage: N [XMAX]
import pickle, itertools, math, collections, sys
from fractions import Fraction as F
from core_lib_v1 import *
N = int(sys.argv[1]); XMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 400
cores = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt').read().split()]
left = pickle.load(open('residual_window_left_N%d.pkl' % N, 'rb'))
def covered(S, cs): return any(set(C) <= set(S) for C in cs)
rest = [S for S in left if not covered(S, cores)]
print('N', N, 'left-over', len(left), 'inside the 53 cores', len(left) - len(rest), 'remaining', len(rest))
cache = {}
def info(C):
    if C not in cache:
        try:
            lo, hi = widest_window(list(C)); w = hi - lo
            cache[C] = (w, math.ceil(1 / (4 * w))) if w > 0 else None
        except ValueError: cache[C] = None
    return cache[C]
cands = collections.defaultdict(set)
for S in rest:
    for C in itertools.combinations(S, 6):
        r = info(C)
        if r and r[1] <= XMAX: cands[C].add(S)
unc = set(rest); chosen = []
while unc:
    best = max(cands, key=lambda C: len(cands[C] & unc), default=None)
    if best is None or not (cands[best] & unc): break
    chosen.append((best, len(cands[best] & unc), info(best))); unc -= cands[best]
print('new cores needed', len(chosen), 'uncovered by any admissible core', len(unc))
for C, n, (w, x0) in chosen[:15]: print(','.join(map(str, C)), 'covers', n, 'x0', x0)
print('uncovered', sorted(unc)[:10])
