"""Reproduce the MEASURED least-m distribution on integer Case B sets <= 24."""
import sys, time
from collections import Counter
from multiprocessing import Pool
from core import integer_caseB, least_m


def work(A):
    r = least_m(A, M=6)
    band = 7 * A[0] < A[6] <= 9 * A[0]
    return (A, None if r is None else r[0], band)


if __name__ == '__main__':
    sets = list(integer_caseB(24))
    print('integer Case B sets:', len(sets), 'band:', sum(1 for A in sets if A[6] <= 9 * A[0]))
    t = time.time()
    cnt, bandcnt, bad = Counter(), Counter(), []
    with Pool(9) as p:
        for k, (A, m, band) in enumerate(p.imap_unordered(work, sets, chunksize=500)):
            cnt[m] += 1
            if band:
                bandcnt[m] += 1
            if m is None or m >= 3:
                bad.append((A, m))
            if k % 20000 == 0:
                with open('reproduce_v1.progress', 'w') as f:
                    f.write(f'{k} {time.time()-t:.0f}s {dict(cnt)}\n')
    print('least m (all):', dict(sorted(cnt.items(), key=lambda t: (t[0] is None, t[0] or 0))))
    print('least m (band):', dict(sorted(bandcnt.items(), key=lambda t: (t[0] is None, t[0] or 0))))
    for A, m in sorted(bad, key=lambda t: (t[1] or 99, t[0])):
        print('  m>=3:', A, m)
    print('time', round(time.time() - t), 's')
