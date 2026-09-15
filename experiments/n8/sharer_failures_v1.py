"""What the failures of "a sharer's own flank is free" say. Order 8, every 8-subset of [1,20], every runner. For each sharer pair
(s, e) with d_s = 8m·d_e: is flank s free? If shadowed, the smallest set of runners holding every opening of s in the way, with
their ratios d_j/d_s reduced, and whether e itself is in that set. Aggregated by signature (m, ratios of the smallest set mod 1)."""
import itertools, math, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from flank_near_extreme_v1 import blocks_all
def job(args):
    n, v = args
    out = []
    for i in range(n):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        flanks = sorted(set(ds))
        for s in flanks:
            for e in flanks:
                if s == e or s % (n * e): continue
                m = s // (n * e)
                others = [d for d in ds if d != s]
                if not blocks_all(s, others, n):
                    out.append(('free', m, None, None)); continue
                best = None
                for size in range(1, len(others) + 1):
                    for S in itertools.combinations(others, size):
                        if blocks_all(s, list(S), n): best = S; break
                    if best: break
                sig = tuple(sorted(str(F(d, s)) for d in best))
                out.append(('shadowed', m, sig, e in best))
    return out
if __name__ == '__main__':
    n = 8
    free_m = Counter(); shad = Counter(); e_in = Counter()
    with Pool() as pool:
        for out in pool.imap_unordered(job, [(n, v) for v in itertools.combinations(range(1, 21), n)], chunksize=300):
            for kind, m, sig, ein in out:
                if kind == 'free': free_m[m] += 1
                else: shad[(m, sig)] += 1; e_in[ein] += 1
    print('free sharer flanks by m:', dict(free_m))
    print('shadowed sharer flanks: e itself in the smallest blocking set?', dict(e_in))
    print('shadowed sharer flanks by (m, ratios d_j/d_s of the smallest blocking set):')
    for (m, sig), c in shad.most_common(25): print(f'   m={m} {sig}: {c}')
