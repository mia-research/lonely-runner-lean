"""E389b (2026-10-05), nesting_random_six_v1: the E389 statement on six-reading arrangements NOT taken from the tree.
Statement tested (exact): for six readings 1 = r1 < ... < r6, let N_A = {v in (r6, 7 r6] : every window of K6 in [1,7] lies in a
zone of v} (non-empty K6 required) and N_B the same for the windows of K'_6 in [9,15]; is N_A ∩ N_B empty?
Population: random six, readings r2..r6 uniform on exact grids of 10^-6 inside [1.2, 8.3] sorted (r6 in [4, 8.3] enforced).
Misses (N_A ∩ N_B non-empty) listed individually.
"""
import sys, random
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from core import clear_set
from nesting_overlap_v1 import nest_set

def work(seed):
    rng = random.Random(seed); stats = [0, 0, 0, 0]; miss = []
    for _ in range(300):
        r = sorted(F(rng.randint(1200000, 8300000), 10 ** 6) for _ in range(5))
        x = [F(1)] + r
        if x[5] < 4 or len(set(x)) < 6:
            continue
        stats[0] += 1
        kA = clear_set(x, F(1), F(7))
        if not kA:
            stats[1] += 1; continue
        lo, hi = x[5], 7 * x[5]
        nA = nest_set(kA, lo, hi)
        if not nA:
            continue
        stats[2] += 1
        kB = clear_set(x, F(9), F(15))
        nAB = nest_set(kA + kB, lo, hi)
        if nAB:
            stats[3] += 1; miss.append((tuple(x), nAB[:2]))
    return stats, miss

if __name__ == '__main__':
    with Pool(4) as pool:
        res = pool.map(work, range(400))
    s = [sum(r[0][i] for r in res) for i in range(4)]
    out = open('nesting_random_six_v1.out', 'w'); out.write(__doc__ + "\n")
    out.write("sixes %d; K6 empty in [1,7]: %d; N_A non-empty (a reading 7 can cross [1,7]): %d; of those, N_A∩N_B non-empty: %d\n" % tuple(s))
    for r in res:
        for m in r[1]:
            out.write("  MISS six=%s e.g. v-interval %s\n" % ([float(a) for a in m[0]], [(float(a), float(b)) for a, b in m[1]]))
    out.close(); print(open('nesting_random_six_v1.out').read()[len(__doc__):][:2500])
