#!/usr/bin/env python3
"""Phase-free test. For primitive SixResidual S = R + {e}: fold the lonely set L of R (threshold 1/6, one
period) modulo the opening spacing 1/e, i.e. map t -> e*t mod 1. If the folded set covers all of [0,1),
EVERY arithmetic progression of spacing 1/e meets L, whatever its phase, so a purely geometric argument
about L suffices. Otherwise some phase misses L, and the specific phase 1/6 of the flank openings must
enter any proof. Reports the fraction of sets with full folded coverage, by bucket of e, and the
minimum covered fraction. Exact Fractions."""
import sys, math, importlib.util
from itertools import combinations
from fractions import Fraction as F
from collections import defaultdict
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
LO, HI = int(sys.argv[1]), int(sys.argv[2])
def lonely_set(R):
    ivs = [(F(0), F(1))]
    for p in R:
        bands = [(F(6*k + 1, 6*p), F(6*k + 5, 6*p)) for k in range(p)]
        ivs = [(max(a, c), min(b, d)) for a, b in ivs for c, d in bands if max(a, c) <= min(b, d)]
    return ivs
def folded_cover(L, e):
    pieces = []
    for a, b in L:
        x, y = a * e, b * e
        if y - x >= 1: return F(1)
        fx = x - (x.numerator // x.denominator); fy = fx + (y - x)
        if fy <= 1: pieces.append((fx, fy))
        else: pieces += [(fx, F(1)), (F(0), fy - 1)]
    pieces.sort(); tot = F(0); cur = None
    for a, b in pieces:
        if cur is None or a > cur[1]:
            if cur: tot += cur[1] - cur[0]
            cur = [a, b]
        else: cur[1] = max(cur[1], b)
    if cur: tot += cur[1] - cur[0]
    return tot
st = defaultdict(lambda: [0, 0, 2.0, None])
for e in range(LO, HI + 1):
    for R in combinations(range(1, e), 4):
        S = R + (e,)
        if math.gcd(*S) != 1 or not r.six_residual(S): continue
        cov = folded_cover(lonely_set(R), e)
        b = st[(e - 1) // 6]; b[0] += 1
        if cov == 1: b[1] += 1
        if float(cov) < b[2]: b[2], b[3] = float(cov), S
for k in sorted(st):
    n, full, mn, arg = st[k]
    print(f"e in [{6*k+1},{6*k+6}]: sets={n}, full folded coverage={full} ({full/n:.3f}), min covered fraction={mn:.3f} at {arg}")
