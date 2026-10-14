"""Corrected rule from the failures. Sharer pair: d_s = 8m·d_e. Read at the shared flank's gap d_e, each other runner j has ratio
d_j/d_e. "Even-slot runner": ratio to the sharer d_j/d_s has reduced denominator 2 or 4 (for m = 1: an integer slot 2, 4 or 6 mod
8 relative to e). Test, over every 8-subset of [1,20] and every runner:
  (N) shadowed sharer flank ⇒ an even-slot runner exists;
  (S) how often an even-slot runner exists while the sharer flank is still free.
Also the same with "denominator 2 or 4" replaced by "denominator 2" and by "denominator 4" separately, and by m."""
import itertools, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from flank_near_extreme_v1 import blocks_all
def job(args):
    n, v = args
    c = Counter()
    for i in range(n):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        flanks = sorted(set(ds))
        for s in flanks:
            for e in flanks:
                if s == e or s % (n * e): continue
                m = s // (n * e)
                others = [d for d in ds if d != s]
                free = not blocks_all(s, others, n)
                dens = {F(d, s).denominator for d in others}
                ev = bool(dens & {2, 4}); d2 = 2 in dens; d4 = 4 in dens
                c[(m, 'free' if free else 'shadowed', 'even' if ev else 'no even', d2, d4)] += 1
    return c
if __name__ == '__main__':
    n = 8; tot = Counter()
    with Pool() as pool:
        for c in pool.imap_unordered(job, [(n, v) for v in itertools.combinations(range(1, 21), n)], chunksize=300):
            tot.update(c)
    for m in (1, 2):
        sh_no = sum(v for k, v in tot.items() if k[0] == m and k[1] == 'shadowed' and k[2] == 'no even')
        sh_ev = sum(v for k, v in tot.items() if k[0] == m and k[1] == 'shadowed' and k[2] == 'even')
        fr_no = sum(v for k, v in tot.items() if k[0] == m and k[1] == 'free' and k[2] == 'no even')
        fr_ev = sum(v for k, v in tot.items() if k[0] == m and k[1] == 'free' and k[2] == 'even')
        print(f'm={m}: shadowed with no even-slot runner {sh_no}; shadowed with one {sh_ev}; free with none {fr_no}; free with one {fr_ev}')
        for d2 in (False, True):
            for d4 in (False, True):
                sh = sum(v for k, v in tot.items() if k[0] == m and k[1] == 'shadowed' and k[3] == d2 and k[4] == d4)
                fr = sum(v for k, v in tot.items() if k[0] == m and k[1] == 'free' and k[3] == d2 and k[4] == d4)
                print(f'    denominator-2 runner {d2!s:5}, denominator-4 runner {d4!s:5}: shadowed {sh}, free {fr}')
