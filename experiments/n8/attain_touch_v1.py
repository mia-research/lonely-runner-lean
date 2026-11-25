"""E949: the class-X readings whose pass set P and earlier-window set A meet (attain_pin_v2's 545 'P meets A'), all crossers
(2026-11-25).  Exact Fractions.  For each class-X reading: is P and A disjoint with a positive gap, touching only (a facing
end of P equals a facing end of A; open intervals, so disjoint), or overlapping with positive length (would contradict
class X)?  For touching: the reading the common point is a multiple of, its role, and the ratio."""
import sys
exec(open('attain_pin_v2.py').read().split("step, off = int")[0])
from collections import Counter
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); o = rs.index(path[-1]) + 1
    for k in range(1, 7):
        if cls[k + 1] != 'X': continue
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        P = [(l, h) for l, h, m in passes(a, b, lo, hi)]; A = [(lo, hi)]
        for jj in range(n):
            if not A: break
            A = passes_in(ws[jj][0], ws[jj][1], A)
        if not A: c[('A empty',)] += 1; continue
        ov = [(max(l1, l2), min(h1, h2)) for l1, h1 in P for l2, h2 in A if max(l1, l2) <= min(h1, h2)]
        if not ov: c[('disjoint, positive gap',)] += 1; continue
        if any(x < y for x, y in ov): c[('positive overlap (contradicts X)',)] += 1; print('OVERLAP', idx, k + 1); continue
        x = ov[0][0]; j, q = ident(x, rs)
        role = 'neighbour' if q == 1 else ('closer' if j in closers else ('opener' if j == o else 'other'))
        c[('touching only', 'common point is a multiple of', role)] += 1
        c[('touching only', 'ratio', role, str(q))] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
