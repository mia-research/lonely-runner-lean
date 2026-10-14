"""E168: the g = 1 sets through the cascade.  Whole-number readings <= N, spread > 7, every 6-subset with gcd 1 (no reading
is off the common grid of the other six: OneFreeEightN does not apply).  For each: the cascade's landing t*; the nearest
runner's lap at t* (which of its clear stretches [(8k+1)/(8 d_min), (8k+7)/(8 d_min)]); the flank (who sets t*); whether
the other six are clear at 1/7 at t* or only at 1/8 (their margin); how far into the stretch t* lies.  Exact.
Protections: progress file; caffeinate by the caller."""
import itertools, sys
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from collections import Counter
from multiprocessing import Pool
E8 = F(1, 8); E7 = F(1, 7)
def nd(x):
    x = x % 1; return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
N = int(sys.argv[1])
def chunk(first):
    C = Counter()
    for rest in itertools.combinations(range(first + 1, N + 1), 6):
        T = (first,) + rest
        if T[-1] <= 7 * T[0]: continue
        if any(reduce(gcd, T[:i] + T[i + 1:]) != 1 for i in range(7)): continue
        t = cascade(T); m = T[0]
        k = floor(m * t); frac = (m * t - k - E8) / F(6, 8)       # position inside the stretch, 0..1
        f = next(d for d in T if (d * t) % 1 == E8)
        six7 = all(nd(d * t) >= E7 for d in T[1:])
        C[('nearest runner on lap %s' % (k if k < 3 else '>=3'), 'flank %s' % ('nearest runner' if f == m else 'another runner'),
           'six clear at 1/7' if six7 else 'six clear only at 1/8', 'into the stretch %s' % ('<1/4' if frac < F(1, 4) else '<1/2' if frac < F(1, 2) else '>=1/2'))] += 1
    open('g1_cascade_v1.progress', 'a').write("chunk %d done\n" % first)
    return C
if __name__ == '__main__':
    open('g1_cascade_v1.progress', 'w').write("start\n")
    C = Counter()
    with Pool(8) as p:
        for c in p.imap_unordered(chunk, range(1, N - 5)): C.update(c)
    tot = sum(C.values()); print("g = 1 sets, readings <= %d, spread > 7: %d" % (N, tot))
    for k, v in sorted(C.items(), key=lambda kv: -kv[1]): print("  %7d  %s" % (v, k))
    open('g1_cascade_v1.progress', 'a').write("ALLDONE\n")
