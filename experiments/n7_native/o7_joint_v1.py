#!/usr/bin/env python3
"""Joint slow closure for six runners (lonely instant at 1/7), per instance.  Split P = (S, F) at index j: slow block
S = (v1..vj), fast block F = (v_{j+1}..v6) written as F = c Q + e (Q a small integer pattern, c = min F_k/Q_k, e >= 0).
`pattern_window` (w = 0) gives a lonely instant of F in [alpha, alpha + 1/c] if, with laps m fixed, every pair satisfies
(m_d + 1/7 - e_d t)/Q_d <= (m_d' + 6/7 - e_d' t)/Q_d' on [alpha, alpha + 1/c]; S must be in band on the same interval
(fixed laps).  All constraints are linear in t, so they hold on the interval iff they hold at both ends.
Search: floats over alpha (grid inside S's lonely intervals) and laps (from an admissible base phase y at alpha);
every reported closure is re-verified in exact Fractions.  Usage: o7_joint_v1.py N seed"""
import math, random, sys
from fractions import Fraction as Fr
from collections import Counter
S7, S67 = Fr(1, 7), Fr(6, 7)
def lonely_iv(S):
    """lonely intervals of S at 1/7 over [0,1), floats (search only)"""
    cur = None
    for v in S:
        B = [((m + 1 / 7) / v, (m + 6 / 7) / v) for m in range(v)]
        if cur is None: cur = B; continue
        i = j = 0; out = []
        while i < len(cur) and j < len(B):
            lo, hi = max(cur[i][0], B[j][0]), min(cur[i][1], B[j][1])
            if hi > lo: out.append((lo, hi))
            if cur[i][1] < B[j][1]: i += 1
            else: j += 1
        cur = out
    return cur
def patterns(F, qmax=12):
    out = []
    for q1 in range(1, qmax + 1):
        Q = [max(1, round(q1 * f / F[0])) for f in F]
        c = min(Fr(f, q) for f, q in zip(F, Q))
        e = [f - c * q for f, q in zip(F, Q)]
        out.append((max(e) / c, Q, c, e))
    out.sort(key=lambda z: z[0]); return out
def y_admissible(F, Q, e, t):
    """admissible base phases y in [0,1) at time t (floats): Q_d y + e_d t in band for all d"""
    cur = [(0.0, 1.0)]
    for q, ed in zip(Q, e):
        ed = float(ed); B = []
        for m in range(-1, q + int(ed * t) + 2):
            lo = (m + 1 / 7 - ed * t) / q; hi = (m + 6 / 7 - ed * t) / q
            lo, hi = max(lo, 0.0), min(hi, 1.0)
            if hi > lo: B.append((lo, hi))
        B.sort(); i = j = 0; out = []
        while i < len(cur) and j < len(B):
            lo, hi = max(cur[i][0], B[j][0]), min(cur[i][1], B[j][1])
            if hi > lo: out.append((lo, hi))
            if cur[i][1] < B[j][1]: i += 1
            else: j += 1
        cur = out
        if not cur: break
    return cur
def exact_ok(S, F, Q, c, e, alpha, y):
    """exact check: fixed laps from (alpha, y); pairwise pattern constraints and S band at both ends of [alpha, alpha+1/c]"""
    a0, a1 = alpha, alpha + 1 / c
    m = [math.floor(q * y + ed * alpha) for q, ed in zip(Q, e)]
    for t in (a0, a1):
        L = max((mm + S7 - ed * t) / q for mm, q, ed in zip(m, Q, e))
        U = min((mm + S67 - ed * t) / q for mm, q, ed in zip(m, Q, e))
        if L > U: return False
    for v in S:
        n = math.floor(v * a0)
        if not (n + S7 <= v * a0 and v * a1 <= n + S67): return False
    return True
def closes(P, qmax=12, grid=400):
    for j in range(1, 6):
        S, F = P[:j], P[j:]
        ivs = lonely_iv(S)
        for sig, Q, c, e in patterns(F, qmax)[:4]:
            ic = 1 / float(c)
            for lo, hi in ivs:
                if hi - lo <= ic: continue
                n = max(2, min(grid, int((hi - lo) / ic * 4)))
                for k in range(n):
                    a = lo + (hi - lo - ic) * k / (n - 1)
                    ys = y_admissible(F, Q, e, a)
                    for ylo, yhi in ys:
                        ym = (ylo + yhi) / 2
                        if exact_ok(S, F, Q, c, e, Fr(a).limit_denominator(10**9), Fr(ym).limit_denominator(10**9)):
                            return j, Q
    return None
if __name__ == "__main__":
    N, seed = int(sys.argv[1]), int(sys.argv[2]); rnd = random.Random(seed)
    c = Counter(); bad = []; done = 0
    while done < N:
        v1 = rnd.randint(1, 8); v5 = rnd.randint(100 * v1 + 1, 1500)
        v6 = rnd.randint(v5 + 1, 6 * v5 - 1)
        mid = sorted(rnd.sample(range(v1 + 1, v5), 3)); P = (v1, *mid, v5, v6)
        if math.gcd(*P) != 1: continue
        done += 1; r = closes(P)
        c[r[0] if r else 0] += 1
        if not r and len(bad) < 20: bad.append(P)
    print(f"six-runner slow region sample (v5 > 100 v1, v6 < 6 v5), {N} sets: closed by split {dict(sorted(c.items()))}; "
          f"not closed {c[0]}")
    print("   not closed:", bad)
