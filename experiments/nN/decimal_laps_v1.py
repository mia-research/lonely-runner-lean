"""Laps against the precision of one speed (the user's example: 1.223 vs 1.223768466552443220).

The AP 1..7 is isolated only on the regular 8-gon.  Deform one runner: disparities x, 2, 3, 4, 5, 6, 7
(subject at 0) with x the truncations of 1.223768466552443220 to 1, 2, ..., 18 decimals, and, as a
second family, 1, 2, 3, 4, 5, 6, 7*x.  For each, the framework's cascade run exactly (Fractions):
from the bound 1/(8 d_min), while some runner is in the way (||d t|| < 1/8), move to the largest of
their next openings (N + 1/8)/d >= t.  Reported: the first lonely instant T (Theorem 11), its
certificate (flank e = the runner at exactly 1/8, lap j = floor(e T)), and the number of moves.
"""
from fractions import Fraction as F
import math
X = "1.223768466552443220"
def nd(x): x = x % 1; return min(x, 1 - x)
def cascade(ds, cap=100000):
    t = F(1, 8) / min(ds); moves = 0
    while moves < cap:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: break
        nxt = []
        for d in way:
            N = math.floor(d * t - F(1, 8))
            o = (N + F(1, 8)) / d
            if o < t: o = (N + 1 + F(1, 8)) / d
            nxt.append(o)
        t = max(nxt); moves += 1
    fl = [d for d in ds if nd(d * t) == F(1, 8)]
    e = max(fl, key=lambda d: d) if fl else None
    return t, e, (math.floor(e * t) if e else None), moves
for label, build in (("x, 2, 3, 4, 5, 6, 7", lambda x: [x, 2, 3, 4, 5, 6, 7]),
                     ("1, 2, 3, 4, 5, 6, 7x", lambda x: [1, 2, 3, 4, 5, 6, 7 * x])):
    print(label)
    for n in range(0, 19):
        x = F(X[:2 + n]) if n else F(1)
        t, e, j, m = cascade(build(x))
        print(f"   x = {str(float(x)) if n < 17 else X[:2 + n]:22s} T = {float(t):.10f}  certificate flank {float(e) if e else None!s:22.20s} lap j = {j}  moves {m}")

# The lap against the SIZE of the deviation from the AP: sweep x finely, report where (flank, lap) changes.
print("\nsweep: 1, 2, 3, 4, 5, 6, 7x and x, 2, ..., 7 and 1, 2, 3, x*4, 5, 6, 7 -- where the certificate changes")
for label, build in (("7x", lambda x: [1, 2, 3, 4, 5, 6, 7 * x]), ("x (runner 1)", lambda x: [x, 2, 3, 4, 5, 6, 7]),
                     ("4x (runner 4)", lambda x: [1, 2, 3, 4 * x, 5, 6, 7])):
    prev = None; out = []; maxj = 0
    for k in range(0, 3001):
        x = F(1) + F(k, 1000)                     # x from 1.000 to 4.000 in steps of 0.001
        t, e, j, m = cascade(build(x))
        key = (j, m)
        maxj = max(maxj, j)
        if key != prev: out.append(f"x={float(x):.3f}: lap {j}, moves {m}"); prev = key
    print(f"   {label}: max lap {maxj}; changes ({len(out)}): " + "; ".join(out[:40]) + (" ..." if len(out) > 40 else ""))

print("\nshrinking the deviation: 1, 2, 3, 4, 5, 6, 7(1 + delta) and 1, 2, 3, 4(1 + delta), 5, 6, 7")
for label, build in (("7(1+delta)", lambda x: [1, 2, 3, 4, 5, 6, 7 * x]), ("4(1+delta)", lambda x: [1, 2, 3, 4 * x, 5, 6, 7])):
    for k in range(1, 13):
        x = 1 + F(1, 10 ** k)
        t, e, j, m = cascade(build(x))
        print(f"   {label}, delta = 1e-{k:<2d}: T = {float(t):.12f}  lap {j}  moves {m}")
    x = F("1.223768466552443220") - 1
    for s in range(1, 8):
        d = x / 10 ** s
        t, e, j, m = cascade(build(1 + d))
        print(f"   {label}, delta = 0.2237684665...e-{s}: lap {j}  moves {m}")
