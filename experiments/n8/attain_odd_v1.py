"""E949: two small sets, exactly (2026-11-25).
(1) Openers whose six-window W_o starts at R* (attain_roles_v1: 26): which frozen reading's exit is at exactly R*?
(2) Class-X readings whose P facing end attain_pin_v2 identified with the moved reading or an 'other' reading: is k the
opener (then W_k's start is another reading's exit), and is the P end also a multiple of the window-edge reading?"""
exec(open('attain_pin_v2.py').read().split("step, off = int")[0])
from collections import Counter
c = Counter()
for idx, R0, closers, cls, att in rows:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); o = rs.index(path[-1]) + 1
    if o >= 2 and o not in closers:
        six = rs[:o - 1] + rs[o:]; ws = windows(six, E, T1); wk = next((x, y) for x, y, z in ws if x <= T <= y)
        if wk[0] == T:
            ex = [j + 1 for j in range(7) if j != o - 1 and ((8 * T * rs[j]) % 8 == 1 and (8 * T * rs[j]).denominator == 1)]
            c[('(1) opener W starts at R*', 'frozen readings exiting at exactly R*', tuple(ex))] += 1
    for k in range(1, 7):
        if cls[k + 1] != 'X': continue
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        P = [(l, h) for l, h, m in passes(a, b, lo, hi)]; A = [(lo, hi)]
        for jj in range(n):
            if not A: break
            A = passes_in(ws[jj][0], ws[jj][1], A)
        if not A: continue
        best = None
        for lp, hp in P:
            for la, ha in A:
                if hp <= la: d, xP, side = la - hp, hp, 'below'
                elif ha <= lp: d, xP, side = lp - ha, lp, 'above'
                else: continue
                if best is None or d < best[0]: best = (d, xP, side)
        if best is None: continue
        jP, qP = ident(best[1], rs)
        role = 'opener' if jP == o else ('closer' if jP in closers else ('moved' if jP == k + 1 else 'other'))
        if role in ('moved', 'other'):
            edge_t = b if best[2] == 'below' else a
            ej = [j + 1 for j in range(7) if j != k and (8 * edge_t * rs[j]).denominator == 1]
            also = [j for j in ej if (best[1] / rs[j - 1]).denominator < 2000 and (best[1] / rs[j - 1]).numerator < 2000]
            c[('(2) P end', role, 'k is opener', k + 1 == o, 'window edge set by', tuple(ej), 'P end also a small multiple of it', bool(also), 'edge is', 'W end' if best[2] == 'below' else 'W start')] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
