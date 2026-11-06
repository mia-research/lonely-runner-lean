# E825: the gaps of the first window: for each gap the reach from its left end among the other pieces, the longest other piece starting at or below it; for the gaps that need 2 pieces, the pieces containing each end.  Streaming (no piece list is stored).
import pickle
from multiprocessing import Pool
from fractions import Fraction as F
from chain_lo_v1 import win
def job(item):
    core, ms = item
    J, T = win(core); A = min(J)
    pmax = max(a for k, b, a, m in ms)
    reach = [None] * len(ms); longest = [None] * len(ms); cb = [[] for _ in ms]; ca = [[] for _ in ms]
    for lo, hi in J:
        for n in range(0, 80):
            d = F(n) * T
            if (lo, hi, n) == (A[0], A[1], 0) or hi + d == 0: continue
            k = 0
            while True:
                p = F(8 * k + 1, 8) / (hi + d)
                if p > pmax: break
                q = F(8 * k + 7, 8) / (lo + d)
                for i, (kk, b, a, m) in enumerate(ms):
                    if p <= b:
                        if reach[i] is None or q > reach[i]: reach[i] = q
                        if longest[i] is None or q - p > longest[i]: longest[i] = q - p
                        if m == 2 and b <= q: cb[i].append((q, p, (lo, hi), n, k))
                    if m == 2 and p <= a <= q: ca[i].append((p, q, (lo, hi), n, k))
                k += 1
    rows = []
    for i, (k, b, a, m) in enumerate(ms):
        det = (sorted(cb[i], reverse=True)[:4], sorted(ca[i])[:4]) if m == 2 else None
        rows.append((core, k, b, a, m, reach[i], longest[i], det))
    return rows
if __name__ == '__main__':
    gp = pickle.load(open('chain_gaps_v1.pkl', 'rb'))
    with Pool(5) as p: res = p.map(job, [(c, ms) for c, A, y0, ms in gp])
    rows = [r for rr in res for r in rr]
    print('gaps', len(rows))
    fails = [r for r in rows if r[4] == 2]
    for core, k, b, a, m, reach, longest, det in fails:
        g = a - b
        print('FAIL', core, 'lap', k, 'gap', (b, a), 'width', g, 'reach from left end', reach, 'short by', a - reach, 'longest other piece starting at or below the left end', longest, 'ge gap width?', longest >= g)
        print('   pieces containing the left end (end, start, window, shift, lap):', det[0])
        print('   pieces containing the right end (start, end, window, shift, lap):', det[1])
    ok = [r for r in rows if r[4] == 1]
    marg = sorted((r[5] - r[3]) / (r[3] - r[2]) for r in ok)
    print('successful gaps', len(ok), 'margin (reach - right end) / gap width: min', marg[0], 'p10', marg[len(marg) // 10], 'median', marg[len(marg) // 2], 'max', marg[-1])
    print('successful gaps with longest piece < gap width:', sum(1 for r in ok if r[6] < r[3] - r[2]), '; failing gaps with longest piece < gap width:', sum(1 for r in fails if r[6] < r[3] - r[2]))
