"""E949: each non-closer reading's gate island against the pass set of its six-window W_k (2026-11-25).  Exact Fractions.
For the gate crossers (E340) and each non-closer reading k (k = 2..7, k = 7 in (r_6, 2 r_7)): the island (as E947 v2:
150 equal points + actual + pass-interval midpoints; ends bisected 90 times on the gate), its relative extent on each side
of the actual position, e_L = (r_k - left end)/r_k and e_R = (right end - r_k)/r_k, and the relative shift needed to reach
the nearest pass interval of W_k on each side, n_L and n_R (None if no pass interval on that side inside the neighbours).
Pass intervals: ((8m-1)/(8a), (8m+1)/(8b)) for W_k = [a, b] (E930), the reading's zone at lap m covering W_k.
Recorded per class (E945: L, P, X attain; N escapes) and role (opener / other): which side the nearest pass interval lies
on; whether n <= e on that side (the island reaches it); the lap m of the nearest pass interval against the lap of the
reading's zone nearest W_k at the actual position; and, for the reading's actual zone nearest W_k, whether it lies
before W_k (exit before a) or after (entry after b)."""
import pickle, glob, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('island_ends_v2.py').read().split("mode = sys.argv[1]")[0])
step, off = int(sys.argv[1]), int(sys.argv[2])
c = Counter(); out = []
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); o = rs.index(path[-1]) + 1
    for k in range(1, 7):
        if (k + 1) in closers: continue
        role = 'opener' if k + 1 == o else 'other'; kc = cls[k + 1]
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]; v0 = rs[k]
        ws = windows(six, E, T1); nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[nW][0], ws[nW][1]
        P = passes(a, b, lo, hi, limit=5000) or []
        pts = [lo + (hi - lo) * Fr(i, 150) for i in range(1, 150)] + [v0]
        for x, y, z in ws[:nW + 2]:
            Q = passes(x, y, lo, hi, limit=5000)
            if Q: pts += [(l + h) / 2 for l, h, m in Q]
        pts = sorted(set(p for p in pts if lo < p < hi))
        cr = {v: gate(sorted(six + [v])) for v in pts}
        ia = pts.index(v0); i0 = ia
        while i0 > 0 and cr[pts[i0 - 1]]: i0 -= 1
        i1 = ia
        while i1 < len(pts) - 1 and cr[pts[i1 + 1]]: i1 += 1
        g = lambda v: gate(sorted(six + [v]))
        L_ = edge(g, pts[i0], pts[i0 - 1]) if i0 > 0 else lo
        R_ = edge(g, pts[i1], pts[i1 + 1]) if i1 < len(pts) - 1 else hi
        eL = (v0 - L_) / v0; eR = (R_ - v0) / v0
        left = [(l, h, m) for l, h, m in P if h <= v0]; right = [(l, h, m) for l, h, m in P if l >= v0]
        inside = [(l, h, m) for l, h, m in P if l < v0 < h]
        nL = (v0 - max(left)[1]) / v0 if left else None; mL = max(left)[2] if left else None
        nR = (min(right)[0] - v0) / v0 if right else None; mR = min(right)[2] if right else None
        # actual zone nearest W_k
        mlo = ceil(v0 * a - E); zone_before = (8 * mlo - 1) / (8 * v0) > b   # the lap whose zone would contain a starts after b
        m_act = floor(v0 * a + E)  # lap of the zone that ended last at or before a (exit <= a)
        c[('class', kc, role)] += 1
        if inside: c[('class', kc, 'actual position inside a pass interval')] += 1
        sideL = nL is not None and nL <= eL; sideR = nR is not None and nR <= eR
        c[('class', kc, 'island reaches a pass interval', 'left' if sideL else '-', 'right' if sideR else '-')] += 1
        near = min([x for x in ((nL, 'L', mL, eL), (nR, 'R', mR, eR)) if x[0] is not None], default=None)
        if near:
            n_, sd, mm, ee = near
            c[('class', kc, 'nearest pass interval side', sd, 'lap vs actual last exit lap', mm - m_act)] += 1
            rb = 'reach' if n_ <= ee else ('need/extent < 2' if n_ < 2 * ee else ('< 10' if n_ < 10 * ee else '>= 10'))
            c[('class', kc, 'nearest: need vs island extent on that side', rb)] += 1
        else:
            c[('class', kc, 'no pass interval inside the neighbours')] += 1
        out.append((idx, k + 1, kc, role, v0, L_, R_, a, b, P[:40]))
pickle.dump(out, open('island_vs_pass_v1_part%d.pkl' % off, 'wb'))
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
