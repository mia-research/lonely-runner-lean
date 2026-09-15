"""T4 exhaustive at small speeds. Every n-subset of [1, V] (gcd of differences irrelevant: readings are ratio-native), every
runner. L* = least lattice with a lonely instant; live = least live lattice; B = floor(s_max/n) + 1. Reports the distributions
of L*, of L* − live, of L* − B, and the extreme cases. Exact integer arithmetic (least_lonely from t4_gap_adversarial_v1)."""
import itertools, sys
from collections import Counter
from fractions import Fraction as F
from multiprocessing import Pool
from t4_gap_adversarial_v1 import least_lonely
def job(args):
    n, v = args
    out = []
    for i in range(n):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        m = min(ds)
        live, L, p = least_lonely(ds, m, n, Lmax=60)
        smax = F(max(ds), m); B = int(smax // n) + 1
        out.append((L, live, B, p, i))
    return v, out
if __name__ == '__main__':
    for n, V in ((5, 30), (8, 20)):
        tasks = [(n, v) for v in itertools.combinations(range(1, V + 1), n)]
        cL = Counter(); cgap = Counter(); cex = Counter(); ext_gap = []; ext_ex = []; none = 0
        with Pool() as pool:
            for v, out in pool.imap_unordered(job, tasks, chunksize=200):
                for L, live, B, p, i in out:
                    if L is None: none += 1; continue
                    cL[L] += 1; cgap[L - live] += 1; cex[L - B] += 1
                    ext_gap.append((L - live, L, live, B, p, v, i)); ext_ex.append((L - B, L, live, B, p, v, i))
                    if len(ext_gap) > 4000:
                        ext_gap = sorted(ext_gap, reverse=True)[:20]; ext_ex = sorted(ext_ex, reverse=True)[:20]
        ext_gap = sorted(ext_gap, reverse=True)[:6]; ext_ex = sorted(ext_ex, reverse=True)[:6]
        print(f'n={n}, all {len(tasks)} subsets of [1,{V}], every runner; no lonely lattice up to 60: {none}')
        print(f'   L*: {dict(sorted(cL.items()))}')
        print(f'   L* − first live: {dict(sorted(cgap.items()))}')
        print(f'   L* − B: {dict(sorted(cex.items()))}')
        print('   largest L* − first live (gap, L*, live, B, p, speeds, subject index):', ext_gap)
        print('   largest L* − B:', ext_ex)
        sys.stdout.flush()
