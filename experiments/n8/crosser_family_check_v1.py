"""E946 check: the 235 (crosser, reading) pairs of crosser_family_v1 where B_k is not the end of the six-window holding
the largest sampled landing (2026-11-25).  Exact Fractions.  For each: B_k against 8 * that window's end and against the
largest sampled landing; if B_k is larger, the escaping cells were missed by the samples, so the pass intervals of
every window from W_k up to B_k's window are sampled too and the largest landing is recomputed.
"""
import pickle, glob
from fractions import Fraction as Fr
from math import floor
from collections import Counter
exec(open('crosser_family_v1.py').read().split("step = int(sys.argv[1])")[0])
c = Counter(); bad = []
for f in sorted(glob.glob('crosser_family_v1_part*.pkl')):
    for idx, fam in pickle.load(open(f, 'rb')):
        for k1, (only, inwin, ismax, eq, cl) in fam.items():
            if not eq: bad.append((idx, k1, cl))
print(len(bad), 'pairs')
for idx, k1, cl in bad:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, s0 = sig(rs); k = k1 - 1
    six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]
    ws = windows(six, E, T1); nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y)
    Bk, n = bmove(six, lo, rs[k + 1] if k < 6 else None)
    nB = next(i for i, (x, y, z) in enumerate(ws) if 8 * y == Bk)
    pts = [lo + (hi - lo) * Fr(i, 150) for i in range(1, 150)] + [rs[k]]
    for x, y, z in ws[:nB + 1]:
        P = passes(x, y, lo, hi, limit=5000)
        if P: pts += [(l + h) / 2 for l, h, m in P]
    # positions passing every window before B_k's window: the walk's own set A at that point
    A = [(l, h) for l, h, m in passes(ws[nB - 1][0], ws[nB - 1][1], lo, hi, limit=5000) or []]
    for jj in range(nB - 1): A = passes_in(ws[jj][0], ws[jj][1], A)
    pts += [(l + h) / 2 for l, h in A]
    pts = sorted(set(p for p in pts if lo < p < hi))
    L = max(8 * sig(sorted(six + [v]))[0] for v in pts)
    wend = next(8 * y for x, y, z in ws if x <= L / 8 <= y)
    c[(cl, 'B_k vs 8 end of the window of the largest landing, resampled', 'equal' if Bk == wend else ('B_k larger' if Bk > wend else 'B_k SMALLER'))] += 1
    c[(cl, 'largest landing <= B_k', L <= Bk)] += 1
for kk, val in sorted(c.items(), key=str): print(val, '|', kk)
