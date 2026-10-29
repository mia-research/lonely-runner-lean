# E640: choose frozen cores (six whole numbers) covering the left-over sets of E639 (N = 28, 142 sets): a set S is covered by the core C when C is a six-subset of S (the family theorem covers every further reading x >= 1).
# Greedy set cover by cores with a widest window and x0 = ceil(1/(4 w)) <= XMAX; prints the cores, the sets each covers, and the sets no admissible core covers.  Exact Fractions.
import pickle, itertools, math, collections, sys
from fractions import Fraction as F
from core_lib_v1 import *
XMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 400
left = pickle.load(open('residual_window_left_N28.pkl', 'rb'))
cache = {}
def info(C):
    if C not in cache:
        try:
            lo, hi = widest_window(list(C)); w = hi - lo
            cache[C] = (w, math.ceil(1 / (4 * w))) if w > 0 else None
        except ValueError:
            cache[C] = None
    return cache[C]
cands = collections.defaultdict(set)
for S in left:
    for C in itertools.combinations(S, 6):
        r = info(C)
        if r and r[1] <= XMAX: cands[C].add(S)
uncovered = set(left); chosen = []
while uncovered:
    best = max(cands, key=lambda C: len(cands[C] & uncovered), default=None)
    if best is None or not (cands[best] & uncovered): break
    chosen.append((best, len(cands[best] & uncovered), info(best))); uncovered -= cands[best]
print('left-over sets', len(left), 'cores chosen', len(chosen), 'uncovered', len(uncovered))
for C, n, (w, x0) in chosen: print(','.join(map(str, C)), 'covers', n, 'w', w, 'x0', x0)
print('uncovered sets', sorted(uncovered)[:20])
