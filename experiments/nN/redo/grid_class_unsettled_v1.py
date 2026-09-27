"""E129: why the single-class criterion leaves 10% of the band to 24.  For each unsettled set: over all candidate grids
(j, m <= 4): does every grid capture some reading (n = 0 mod 8)?  Or is there a capture-free grid that still fails (then
the failure is deviation or edges)?  Also: is the set in the doubled-slot shape (a reading within 1/2 of 8 at the AP
scale, i.e. n = 8 for j = 0, m = 1)?"""
import itertools, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.argv = [sys.argv[0], '24', '9', '4']
from grid_class_criterion_v1 import settles, rnd
def job(T):
    s = [F(d, T[0]) for d in T]
    if settles(s): return None
    free = []
    for m in range(1, 5):
        for j in range(7):
            lam = s[j] / m; n = [rnd(v / lam) for v in s]
            if min(n) >= 1 and all(v % 8 for v in n): free.append((j, m))
    ap8 = rnd(s[-1]) == 8
    return ('every grid captures a reading' if not free else 'a capture-free grid exists but fails', ap8)
if __name__ == '__main__':
    sets = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1] <= 9 * T[0]]
    with Pool(10) as p: res = [r for r in p.map(job, sets, chunksize=100) if r]
    print("unsettled band sets to 24:", len(res))
    print("  ", Counter(r[0] for r in res))
    print("   top reading rounds to 8 at the AP scale (captured there):", Counter(r[1] for r in res))
