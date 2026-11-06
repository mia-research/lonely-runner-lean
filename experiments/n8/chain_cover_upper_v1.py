# E824: an explicit cover of [3/8, y0]: every piece of the first window A (least lo, shift 0) with start <= y0, the pieces of the other windows/shifts that cover each gap between consecutive A pieces, the head [3/8, a_0] and the tail [b_K, y0].  Its size is an upper bound on the chain length; compare (exact).
import sys, pickle, collections
from multiprocessing import Pool
from fractions import Fraction as F
from chain_lo_v1 import win
def cover(others, lo, hi_stop, need):
    # least number of `others` pieces covering [lo, hi_stop] (closed), None if impossible; others sorted by start
    cur = lo; m = 0; i = 0; best = None
    while cur < hi_stop:
        while i < len(others) and others[i][0] <= cur:
            if best is None or others[i][1] > best: best = others[i][1]
            i += 1
        if best is None or best <= cur: return None
        cur = best; m += 1
    return m
def job(core):
    J, T = win(core)
    jw = max(J, key=lambda w: w[1] - w[0]); y0 = 1 / (4 * (jw[1] - jw[0]))
    A = min(J); lo, hi = A
    others = []
    for l2, h2 in J:
        for n in range(0, 80):
            d = F(n) * T
            if (l2, h2, n) == (lo, hi, 0) or h2 + d == 0: continue
            k = 0
            while F(8 * k + 1, 8) / (h2 + d) <= y0 * 2:
                others.append((F(8 * k + 1, 8) / (h2 + d), F(8 * k + 7, 8) / (l2 + d))); k += 1
    others.sort()
    ks = []; k = 0
    while F(8 * k + 1, 8) / hi <= y0: ks.append(k); k += 1
    a = lambda k: F(8 * k + 1, 8) / hi; b = lambda k: F(8 * k + 7, 8) / lo
    total = len(ks); parts = {'A': len(ks), 'gaps': 0, 'head': 0, 'tail': 0}
    ok = True
    if a(0) > F(3, 8):
        m = cover(others, F(3, 8), a(0), None); parts['head'] = m
        if m is None: ok = False
        else: total += m
    for k in ks[:-1]:
        if a(k + 1) > b(k):
            m = cover(others, b(k), a(k + 1), None)
            if m is None: ok = False
            else: total += m; parts['gaps'] += m
    if b(ks[-1]) < y0:
        m = cover(others, b(ks[-1]), y0, None); parts['tail'] = m
        if m is None: ok = False
        else: total += m
    return core, (total if ok else None), parts
if __name__ == '__main__':
    cores = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt') if l.strip()]
    cp = {r[0]: r for r in pickle.load(open('chain_pieces_v1.pkl', 'rb'))}
    with Pool(10) as p: res = p.map(job, cores)
    d = collections.Counter()
    for core, tot, parts in res:
        n = len(cp[core][3]); d[None if tot is None else tot - n] += 1
    print('cores', len(res), 'explicit cover size minus chain length (counts):', sorted(d.items(), key=lambda x: (x[0] is None, x[0])))
    print('violations of chain <= explicit cover:', sum(1 for core, tot, p in res if tot is not None and len(cp[core][3]) > tot))
    for core, tot, parts in res:
        if tot is not None and tot - len(cp[core][3]) == 2: print('cover - chain = 2:', core, 'chain', len(cp[core][3]), 'cover', tot, parts)
    for core, tot, parts in res[:4]: print(core, 'chain', len(cp[core][3]), 'cover', tot, parts)
