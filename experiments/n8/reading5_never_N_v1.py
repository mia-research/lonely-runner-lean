"""E950: why reading 5 is never class N (E945: reading 5 is C 2,846, L 694, P 18, X 1,381, N 0) (2026-11-25).  Exact.
For every crosser where reading 5 is not the closer: reading 5's status at the gate state R = 9 (in the way or clear, and
the lap), the closer's rank, reading 5's class, and for class X the facing ends (attain_pin_v2) in roles."""
exec(open('attain_pin_v2.py').read().split("step, off = int")[0])
from collections import Counter
c = Counter()
for idx, R0, closers, cls, att in rows:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); o = rs.index(path[-1]) + 1
    k = 4; kc = cls[5]
    x9 = rs[k] * Fr(9, 8); m9 = round(x9); inw = blocked(rs[k], Fr(9, 8))
    c[('reading 5 class', kc, 'at R = 9', 'in the way lap %d' % m9 if inw else 'clear', 'closer', tuple(closers), 'opener', o)] += 1
    c[('reading 5 class', kc, 'in the way at R = 9', inw)] += 1
    if kc == 'X':
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        P = [(l, h) for l, h, m in passes(a, b, lo, rs[k + 1])]; A = [(lo, rs[k + 1])]
        for jj in range(n):
            if not A: break
            A = passes_in(ws[jj][0], ws[jj][1], A)
        best = None
        for lp, hp in P:
            for la, ha in A:
                if hp <= la: d, xP, xA, side = la - hp, hp, la, 'P below A (slow side)'
                elif ha <= lp: d, xP, xA, side = lp - ha, lp, ha, 'P above A (fast side)'
                else: continue
                if best is None or d < best[0]: best = (d, xP, xA, side)
        if best:
            jA, qA = ident(best[2], rs); jP, qP = ident(best[1], rs)
            c[('reading 5 X', best[3], 'A end reading', jA, 'P end reading', jP, 'ratio' if jA == jP else '', str(qP / qA) if jA == jP else '')] += 1
for kk, v in sorted(c.items(), key=lambda kv: -kv[1])[:45]: print(v, '|', kk)
