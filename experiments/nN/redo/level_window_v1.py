"""The third ingredient of the derived block rule: within one level, a block of f readings with NO
nearly synchronised pair (every consecutive ratio >= 1 + 1/9) and scale-free (max/min < 9): is the
longest stretch with no joint clear instant bounded in turns of its slowest reading?
kappa = sup (longest joint-blocked run) * min(block), exact (open zones, BSM: touching zones leave their
endpoint clear), over one full period, exhaustive over integer blocks with elements in [N, 9N), for
N = 10, 20, 40 (the block is a lemma-level object: one runner's fast readings)."""
import sys, time
from itertools import combinations
from fractions import Fraction as F
from math import gcd
from functools import reduce
from multiprocessing import Pool
def longest_blocked(Fs):
    g = reduce(gcd, Fs)
    z = sorted((F(8 * k - 1, 8 * d), F(8 * k + 1, 8 * d)) for d in Fs for k in range(0, d // g + 2))
    best = F(0); lo, hi = z[0]
    for a, b in z[1:]:
        if a < hi: hi = max(hi, b)
        else: best = max(best, hi - lo); lo, hi = a, b
    return max(best, hi - lo)
def ok_block(Fs): return all(9 * Fs[i + 1] >= 10 * Fs[i] for i in range(len(Fs) - 1)) and Fs[-1] < 9 * Fs[0]
def work(args):
    f, N, first = args
    best = (F(0), None)
    for rest in combinations(range(first + 1, 9 * N), f - 1):
        Fs = (first,) + rest
        if not ok_block(Fs): continue
        v = longest_blocked(Fs) * first
        if v > best[0]: best = (v, Fs)
    return best
if __name__ == "__main__":
    for f in (3, 4, 5, 6):
        for N in (10, 20, 40):
            if f >= 5 and N > 20: continue
            t0 = time.time()
            with Pool(8) as p: parts = p.map(work, [(f, N, a) for a in range(N, 2 * N)])
            best = max(parts, key=lambda x: x[0])
            print(f"f={f}, least reading in [{N},{2*N}), no pair within 1/9, max/min < 9: kappa = {float(best[0]):.4f} at {best[1]}  ({time.time()-t0:.0f}s)", flush=True)
