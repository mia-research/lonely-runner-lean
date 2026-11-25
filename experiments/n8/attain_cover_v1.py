"""E949: per crosser, the exact reason some reading attains min B_k (2026-11-25).  Exact Fractions.
Reasons, first that holds, at the member: L (|W_k| >= 1/(4 lo): no zone in the neighbour range covers W_k), P (W_k's pass set
in the neighbour range is empty), X-A-empty (no position passes every earlier six-window), X-touch (P and A meet only at a
common end point, excluded by open zones), X-gap (P and A disjoint with a positive gap at the member).  Cell-wide reasons
come from attain_lp_cert_v1 (exact Farkas certificates); this script records the member-level reasons for every crosser."""
exec(open('attain_pin_v2.py').read().split("step, off = int")[0])
from collections import Counter
c = Counter()
for idx, R0, closers, cls, att in rows:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); reasons = set()
    for k1 in att:
        k = k1 - 1; kc = cls[k1]
        if kc in 'LP': reasons.add(kc); continue
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        P = [(l, h) for l, h, m in passes(a, b, lo, hi)]; A = [(lo, hi)]
        for jj in range(n):
            if not A: break
            A = passes_in(ws[jj][0], ws[jj][1], A)
        if not A: reasons.add('X-A-empty'); continue
        ov = [(max(l1, l2), min(h1, h2)) for l1, h1 in P for l2, h2 in A if max(l1, l2) <= min(h1, h2)]
        reasons.add('X-touch' if ov else 'X-gap')
    c[('reasons present', tuple(sorted(reasons)))] += 1
    c[('has a member-level exact reason', bool(reasons))] += 1
    c[('all attaining are X', all(cls[k] == 'X' for k in att))] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
