"""E167: case 3 in general (two runners in one slot, every other runner at any laps), whole numbers.  Readings: 7 distinct
positive integers <= N, gcd 1, exactly one reading p = 0 mod 8 (it shares the subject's slot at every class instant
j/8).  Claim: at one of the eight separation instants j/8 +- 1/(8p), j in {1,3,5,7}, every reading is clear.  Exact.
Protections: progress file; caffeinate by the caller; control: the proved DoubledSlotN member (1,2,3,4,5,6,8) passes."""
import itertools, sys
from fractions import Fraction as F
from math import gcd
from functools import reduce
from collections import Counter
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1; return min(x, 1 - x)
def sep_ok(T, p):
    for j in (1, 3, 5, 7):
        for sg in (1, -1):
            t = F(j, 8) + sg * F(1, 8 * p)
            if t > 0 and all(nd(d * t) >= E8 for d in T): return (j, sg)
    return None
N = int(sys.argv[1])
def chunk(first):
    C = Counter(); fails = []
    for rest in itertools.combinations(range(first + 1, N + 1), 6):
        T = (first,) + rest
        zs = [d for d in T if d % 8 == 0]
        if len(zs) != 1 or reduce(gcd, T) != 1: continue
        r = sep_ok(T, zs[0]); C['one separation works' if r else 'no single separation'] += 1
        if not r and len(fails) < 20: fails.append(T)
    open('pair_sep_general_v1.progress', 'a').write("chunk %d: %s\n" % (first, dict(C)))
    return C, fails
if __name__ == '__main__':
    assert sep_ok((1, 2, 3, 4, 5, 6, 8), 8), "CONTROL FAILED"
    open('pair_sep_general_v1.progress', 'w').write("control passed\n")
    C = Counter(); F_ = []
    with Pool(8) as p:
        for c, f in p.imap_unordered(chunk, range(1, N - 5)): C.update(c); F_ += f
    print("readings <= %d, exactly one on 0 mod 8, gcd 1:" % N, dict(C))
    print("examples with no single separation:", sorted(F_)[:20])
