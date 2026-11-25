"""E949: the touching class-X readings (attain_touch_v1), their two coinciding ends written out (2026-11-25).  Exact.
At the common point x: the P end is (8m+1)/(8b) or (8m-1)/(8a) for W_k = [a, b]; the A end is (8m'+1)/(8b') or
(8m'-1)/(8a') for an earlier six-window [a', b'].  Each window edge is identified as a zone edge of one frozen reading
(exit (8l+1)/(8r) for a start, entry (8l-1)/(8r) for an end).  Printed per kind: (P end formula, A end formula)."""
import sys
exec(open('attain_pin_v2.py').read().split("step, off = int")[0])
from collections import Counter
def edge_id(t, rs, kind):
    for j in range(7):
        x = 8 * t * rs[j]
        if x.denominator == 1 and ((kind == 'start' and x % 8 == 1) or (kind == 'end' and x % 8 == 7)): return (j + 1, int(x))
    return None
c = Counter()
for idx, R0, closers, cls, att in rows:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    for k in range(1, 7):
        if cls[k + 1] != 'X': continue
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        P = [(l, h, m) for l, h, m in passes(a, b, lo, hi)]; A = [(lo, hi)]
        for jj in range(n):
            if not A: break
            A = passes_in(ws[jj][0], ws[jj][1], A)
        if not A: continue
        ov = [max(l1, l2) for l1, h1, m in P for l2, h2 in A if max(l1, l2) == min(h1, h2)]
        if not ov: continue
        x = ov[0]
        pe = [('P: lap %d exit at W end' % m, edge_id(b, rs, 'end')) for l, h, m in P if h == x] + [('P: lap %d entry at W start' % m, edge_id(a, rs, 'start')) for l, h, m in P if l == x]
        ae = []
        for jj in range(n):
            a2, b2 = ws[jj][0], ws[jj][1]
            for mm in range(1, 40):
                if Fr(8 * mm + 1) / (8 * b2) == x: ae.append(('A: lap %d exit at window %d end' % (mm, jj), edge_id(b2, rs, 'end')))
                if Fr(8 * mm - 1) / (8 * a2) == x: ae.append(('A: lap %d entry at window %d start' % (mm, jj), edge_id(a2, rs, 'start')))
        c[(tuple(pe), tuple(ae))] += 1
for kk, v in sorted(c.items(), key=lambda kv: -kv[1])[:25]: print(v, '|', kk)
print(sum(c.values()), 'touching readings')
