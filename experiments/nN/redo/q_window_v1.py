"""Case C, first-band form, restated on the six other readings F (casec_trace_v1): with T = 1/(8 g_1), g_1's first band
is [T, 7T] and g_1 ranges over g_1 < min F, 24 g_1 < max F.  So Case C (neighbour bound R <= 7) is exactly
   Q(F):  for every T >= T0 = max(1/(8 min F), 3/max F), F has a lonely instant (threshold 1/8, closed) in [T, 7T].
The first lonely instant at or after T is the cascade from T; the worst T is the start s of a blocked stretch [s, e]
(or T0 inside one), so  Q(F)  <=>  e <= 7 max(s, T0) for every blocked stretch with e > T0.
Exact (Fraction), BSM (open zones; touching zones leave the point clear), integer F, one period [0, 1/gcd] suffices
beyond T0 since the pattern repeats.  Report max e/max(s,T0) per F and the worst sets."""
import random, sys
from fractions import Fraction as F
from math import gcd, floor, ceil
from functools import reduce
from multiprocessing import Pool

def worst_ratio(Fs):
    m, M = min(Fs), max(Fs); T0 = max(F(1, 8 * m), F(3, M))
    P = F(1, reduce(gcd, Fs)); hi = T0 + P + F(1, m)      # one full period past T0, plus a lap of min F
    Z = []
    for d in Fs:
        for k in range(floor(d * T0 - F(1, 8)) , ceil(d * hi + F(1, 8)) + 1):
            lo_, hi_ = (k - F(1, 8)) / d, (k + F(1, 8)) / d
            if hi_ > T0 and lo_ < hi: Z.append((lo_, hi_))
    Z.sort()
    best = F(0); arg = None; cur_s = None; cur_e = None
    for lo_, hi_ in Z:
        if cur_e is None or lo_ >= cur_e:            # a gap (or touching): close the previous stretch
            if cur_e is not None:
                r = cur_e / max(cur_s, T0)
                if r > best: best, arg = r, (cur_s, cur_e)
            cur_s, cur_e = lo_, hi_
        else:
            cur_e = max(cur_e, hi_)
    if cur_e is not None:
        r = cur_e / max(cur_s, T0)
        if r > best: best, arg = r, (cur_s, cur_e)
    return best, arg, T0

def job(Fs):
    b, arg, T0 = worst_ratio(Fs)
    return Fs, b, arg, T0

if __name__ == '__main__':
    rnd = random.Random(2611); sets = []
    for _ in range(3000):                      # random six-sets
        top = rnd.choice((40, 100, 300))
        sets.append(sorted(rnd.sample(range(1, top + 1), 6)))
    for _ in range(1000):                      # near-progressions and clumps
        c = rnd.randint(5, 60); Fs = sorted(set(max(1, c * k + rnd.randint(-c // 5, c // 5)) for k in range(1, 7)))
        if len(Fs) == 6: sets.append(Fs)
        D = rnd.randint(20, 300); Fs = sorted(set([rnd.randint(1, D // 2)] + [D + rnd.randint(0, 8) for _ in range(5)]))
        if len(Fs) == 6: sets.append(Fs)
    with Pool() as pool: res = pool.map(job, sets)
    res.sort(key=lambda r: -r[1])
    over = [r for r in res if r[1] > 7]
    print(f"six-sets {len(res)}; Q(F) holds (every blocked stretch past T0 ends within 7 x its start): {len(res) - len(over)}; fails: {len(over)}")
    print(f"max ratio {float(res[0][1]):.4f}")
    for Fs, b, arg, T0 in res[:15]:
        print(f"  F {Fs}: ratio {float(b):.4f}  stretch [{float(arg[0]*min(Fs)*8):.3f}, {float(arg[1]*min(Fs)*8):.3f}] in R_F = 8 min(F) t;  T0 in R_F {float(T0*min(Fs)*8):.3f}")
