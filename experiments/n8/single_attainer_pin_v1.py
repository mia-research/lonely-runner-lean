"""E949: the 24 single-attainer crossers (reading 5 alone, class X; closer 7, opener 6).  Exact Fractions.
For reading 5: (1) the island's right end, solved exactly as in island_ends_v6 (the exit = entry equality at the divergent
move), written as ratio x r_j; (2) the left end of the nearest pass interval of W_5 = [a, b] on the right,
(8m-1)/(8a), with a the opener's exit, so it is r_6 (8m-1)/(8m_6+1); (3) the ratio of (2) to (1) when both are
multiples of the same frozen reading."""
import pickle, glob
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('island_ends_v2.py').read().split("mode = sys.argv[1]")[0])
def run(rs):
    T, path = cascade(rs, E); t = E; st = [t]; setter = [None]
    for p in path:
        lap = floor(p * t + E); t = (lap + E) / p; st.append(t); setter.append(rs.index(p))
    return T, path, st, setter
def solve_end(six, k, a, b):
    ra = sorted(six + [a]); rb = sorted(six + [b]); Ta, pa, sa, ea = run(ra); Tb, pb, sb, eb = run(rb)
    ia = [ra.index(x) for x in pa]; ib = [rb.index(x) for x in pb]
    p = next((u for u in range(min(len(ia), len(ib))) if ia[u] != ib[u]), min(len(ia), len(ib)))
    t = sa[p]; s_ = ea[p]; ka = ra.index(a)
    A_ = {q for q in range(7) if blocked(ra[q], t)}; B_ = {q for q in range(7) if blocked(rb[q], sb[p])}
    d = sorted(A_ ^ B_); ci = d[0]; xr = ra[ci] * t; mp = round(xr); sig = 1 if xr > mp else -1
    if ci == ka:
        m = ra[s_] * t - E; return (8 * mp + sig) * ra[s_] / (8 * m + 1), ('A', s_ + 1, int(m), mp, sig)
    m = a * t - E; return (8 * m + 1) * ra[ci] / (8 * mp + sig), ('B', ci + 1, int(m), mp, sig)
c = Counter()
for idx, R0, closers, cls, att in [r for r in rows if len(r[4]) == 1]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    k = 4; six = rs[:k] + rs[k + 1:]; lo, hi, v0 = rs[k - 1], rs[k + 1], rs[k]
    g = lambda v: gate(sorted(six + [v]))
    b_ = v0; st = (hi - v0) / 4000
    while g(b_) and b_ < hi: b_ += st
    a_ = b_ - st
    for _ in range(100):
        m_ = (a_ + b_) / 2
        if g(m_): a_ = m_
        else: b_ = m_
    end, rel = solve_end(six, k, a_, b_)
    ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); wa, wb = ws[n][0], ws[n][1]
    P = [(l, h, m) for l, h, m in passes(wa, wb, lo, hi) if l >= v0]
    l0, h0, m0 = min(P)
    m6 = 8 * T * rs[5] - 1  # R* = (8 m6' + 1)/r_6 -> 8 m6' + 1 = R* r_6
    j = rel[1]
    print('E340', idx, '| island right end', rel, 'end/r_%d =' % j, end / rs[j - 1], '| pass left end (8m-1)/(8a), m =', m0, '; a*8*r_6 =', 8 * wa * rs[5], '| pass/end =', l0 / end, '~ %.6f' % float(l0 / end))
    c[('island end relation', rel)] += 1; c[('pass/end', str(l0 / end))] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
