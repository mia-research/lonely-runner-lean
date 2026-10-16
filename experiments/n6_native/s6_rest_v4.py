#!/usr/bin/env python3
"""Observation. Coprime §6 with D < 15 (and the g | v4 reductions with D' < 15): the orbit at meeting times is
{(j, lam j) mod D}, so the class is (D, lam), lam = delta v1^-1 mod D. Runner 4's arcs depend only on
U = v3/v2 = (c+1)/c, Q = v4/v3 in [1, 4/(5-U)) (near-runner), M = v4/(3 v5) in (0, 1/3]:
  after:  A  = [1/6 - 5Q/6 + M, 5/6 - M - QU/6],     runner 1 phase in [1/6, 5/9]
  before: A' = A + (v4 s0 + v4 s1) = A + QU/6 + 5Q/6, runner 1 phase in [4/9, 5/6]
(as in s6_rest_v1.arcs). Per class: the share of a parameter grid (c in 1..6 and c = 1000; 60 Q values; 30 M values)
where some available phase pair (j/D, lam j/D) is on the arc, and where the failures sit."""
from fractions import Fraction as F
from collections import defaultdict
def frac(x): return x - (x.numerator // x.denominator)
def on_arc(p, lo, hi): return hi - lo >= 1 or (hi >= lo and frac(p - lo) <= hi - lo)
def closed(D, lam, U, Q, M):
    lo, hi = F(1, 6) - 5 * Q / 6 + M, F(5, 6) - M - Q * U / 6
    sh = Q * U / 6 + 5 * Q / 6
    for j in range(D):
        p1, p4 = F(j, D), F(lam * j % D, D)
        if F(1, 6) <= p1 <= F(5, 9) and on_arc(p4, lo, hi): return True
        if F(4, 9) <= p1 <= F(5, 6) and on_arc(p4, lo + sh, hi + sh): return True
    return False
if __name__ == "__main__":
    cs = [1, 2, 3, 4, 5, 6, 1000]
    out = []; fails_by = defaultdict(list)
    for D in range(2, 15):
        row = []
        for lam in range(D):
            tot = bad = 0
            for c in cs:
                U = F(c + 1, c); Qmax = 4 / (5 - U)
                for qi in range(60):
                    Q = 1 + (Qmax - 1) * F(qi, 60)
                    for mi in range(1, 31):
                        M = F(mi, 90); tot += 1
                        if not closed(D, lam, U, Q, M):
                            bad += 1
                            if len(fails_by[(D, lam)]) < 3: fails_by[(D, lam)].append((c, float(Q), float(M)))
            row.append((lam, round(bad / tot, 3)))
        out.append((D, row))
        print(f"D = {D:2d}: failure share by lam:", " ".join(f"{l}:{b}" for l, b in row), flush=True)
    print("classes with no failures:", sum(1 for D, r in out for l, b in r if b == 0), "of", sum(len(r) for D, r in out))
    for k, v in sorted(fails_by.items()):
        if k[1] in (0, 1, k[0] - 1): print("  sample failures", k, v)

