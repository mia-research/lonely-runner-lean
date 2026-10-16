#!/usr/bin/env python3
"""Phase 2: pinch closed form, reversal classes and admissible speeds. For each normalised pinch (a, m, b, m') of
o7_pinch_v2 (laps reduced so that min(m // a, m' // b) = 0), interval [tL, tU] = [(7m+1)/(7a), (7m'+6)/(7b)]:
 - reversal t -> -t swaps the 1/7 and 6/7 edges: (a, m, b, m') -> (b, b-1-m', a, a-1-m), interval [-tU, -tL];
 - admissible speeds at scale 1: x in band on all of [tL, tU] iff, with n = floor(x tL), x tL - n >= 1/7 and
   x tU <= n + 6/7. Since x (tU - tL) <= 5/7, x <= 5/(7 (tU - tL)) = 5ab/delta: a finite list (closed form);
 - certificate check: each listed T6 set S = c P lies in its pinch at some shift k: every speed of S / c ... i.e.
   every v in S is in band on [(tL + k)/c, (tU + k)/c] (exact)."""
import math, re
from fractions import Fraction as Fr
T6 = sorted({tuple(map(int, m.group(1).split(","))) for m in re.finditer(r"T6 \(([0-9, ]+)\)", open("o7_map_v2_60.out").read())})
groups = []
for l in open("o7_pinch_v2.out"):
    if l.startswith("  in ("):
        a, m, b, mp = map(int, re.findall(r"-?\d+", l)[:4])
        sets = [(tuple(map(int, x.group(1).split(","))), int(x.group(2) or 1))
                for x in re.finditer(r"\(([0-9, ]+)\)(?: x(\d+))?", l.split(": ", 1)[1].split("length")[1])]
        groups.append(((a, m, b, mp), sets))
def norm(p):
    a, m, b, mp = p; s = min(m // a, mp // b)
    return (a, m - s * a, b, mp - s * b)
def rev(p):
    a, m, b, mp = p
    return norm((b, b - 1 - mp, a, a - 1 - m))
def inband(x, lo, hi):
    n = math.floor(x * lo)
    return x * lo - n >= Fr(1, 7) and x * hi <= n + Fr(6, 7)
keys = [norm(p) for p, _ in groups]
print(f"{len(keys)} normalised pinches; reversal pairs present:", sorted({(p, rev(p)) for p in keys if rev(p) in keys and p < rev(p)}))
nchk = 0
for (p0, sets), p in zip(groups, keys):
    a, m, b, mp = p; tL, tU = Fr(7 * m + 1, 7 * a), Fr(7 * mp + 6, 7 * b); d = (7 * mp + 6) * a - (7 * m + 1) * b
    adm = [x for x in range(1, 5 * a * b // d + 1) if inband(x, tL, tU)]
    for S, c in sets:
        ok = any(all(inband(v, (tL + k) / c, (tU + k) / c) for v in S) for k in range(c * max(a, b)))
        assert ok, (S, p); nchk += 1
    print(f"  {p}: [tL, tU] = [{tL}, {tU}], delta {d}, bound 5ab/delta = {Fr(5 * a * b, d)}, "
          f"admissible speeds at scale 1 ({len(adm)}): {adm}")
print(f"certificate check: {nchk} of {len(T6)} T6 sets lie in band on their pinch interval (exact)")
