#!/usr/bin/env python3
"""E38: the sharp two-runner window length. Runner 4 reads a4 + u, runner 5 reads a5 + rho u (u in runner-4 laps,
rho = d5/d4 >= 1). First common clear time f(a4, a5) = least u >= 0 with both readings in the closed band
[1/6, 5/6] mod 1. L(rho) = sup over (a4, a5) of f. Exact for a given start: list clear pieces of each runner and
take the earliest overlap. Sup over starts: f is piecewise linear in the starts, so the sup is approached at
starts just past exits; we scan a4, a5 on a fine rational grid plus the critical starts (just past an exit),
and report the sup with its argmax, for a set of rho."""
from fractions import Fraction as F
s6, s56 = F(1, 6), F(5, 6)
def pieces(a, rate, upto):
    a = a % 1; out = []
    # time to next entry / exit
    if s6 <= a <= s56: e, x = F(0), (s56 - a) / rate
    else: e = ((s6 - a) % 1) / rate; x = e + F(2, 3) / rate
    while e <= upto:
        out.append((e, x)); e, x = x + F(1, 3) / rate, x + F(1, 3) / rate + F(2, 3) / rate
    return out
def first(a4, a5, rho):
    p4 = pieces(a4, F(1), F(4)); p5 = pieces(a5, rho, F(4))
    return min(max(a, c) for a, b in p4 for c, d in p5 if max(a, c) <= min(b, d))
def L(rho, N=120):
    best = (F(-1), None)
    eps = F(1, 10**6)
    starts = [F(i, N) for i in range(N)] + [s56 + eps]
    for a4 in starts:
        for a5 in starts + [s56 + eps - rho * k / 1000 for k in range(0, 1)]:
            f = first(a4, a5, rho)
            if f > best[0]: best = (f, (a4, a5))
    return best
for rho in [F(1), F(11, 10), F(6, 5), F(3, 2), F(2), F(5, 2), F(3), F(4), F(5), F(8)]:
    f, arg = L(rho)
    print(f"rho = {rho} ({float(rho):.3f}): sup first common time ~ {float(f):.5f}; candidates 1/3+1/(3rho) = {float(F(1,3)+1/(3*rho)):.5f}, 1/3+2/(3rho) = {float(F(1,3)+2/(3*rho)):.5f}; argmax a4={float(arg[0]):.4f} a5={float(arg[1]):.4f}")
