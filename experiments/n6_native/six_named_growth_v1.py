#!/usr/bin/env python3
"""Growth of the least |c| for which a named multiplier c*inv(x) (x element, difference or sum, a unit
mod e) is good, in the coprime case, by bucket of e = max S. Also the fraction of sets needing |c| > 1.
CRT clearance as in six_named_multipliers_v1.py. Exact integers."""
import sys, math, importlib.util
from itertools import combinations
from collections import defaultdict
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def clear_all(S, e, m):
    einv = 1 if e % 6 == 1 else 5
    for d in S:
        w = (d * m) % e; c = (einv * (d - w)) % 6
        if not (1 <= c <= 4 or (c == 5 and w == 0)): return False
    return True
stat = defaultdict(lambda: [0, 0, 0, None])   # sets, needing >1, max c, argmax
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if math.gcd(e, 6) != 1: continue
    xs = {x % e for x in list(S[:-1]) + [b - a for a, b in combinations(S, 2)] + [a + b for a, b in combinations(S[:-1], 2)]}
    invs = [pow(x, -1, e) for x in xs if x and math.gcd(x, e) == 1]
    best = None
    for c in range(1, e):
        if any(clear_all(S, e, (sg * v) % e) for v in invs for sg in (c, -c)): best = c; break
    b = stat[(e - 1) // 12]
    b[0] += 1
    if best is None: continue
    if best > 1: b[1] += 1
    if best > b[2]: b[2], b[3] = best, S
for k in sorted(stat):
    s, gt1, mx, arg = stat[k]
    print(f"  e in [{12*k+1},{12*k+12}]: sets={s}, need |c|>1: {gt1} ({gt1/s:.4f}), max least |c| = {mx} at {arg}")
