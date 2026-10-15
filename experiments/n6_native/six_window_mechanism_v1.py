#!/usr/bin/env python3
"""Mechanism test. For primitive SixResidual S = R + {e} (e = max): L = lonely set at threshold 1/6 of the
other four elements R within one period [0,1) (exact union of intervals). The largest flank's openings
t_j = (j + 1/6)/e, j < e, are an arithmetic progression of spacing 1/e, and e is clear at each of them.
Checks, exactly:
  (i)   G == #{j : t_j in L}  (the flank works iff L contains a progression point);
  (ii)  window condition: longest component lambda of L (wrapping at 1 joined) satisfies lambda >= 1/e
        -> then G >= 1 automatically; count how many sets it covers, and min lambda*e;
  (iii) G versus e*mu(L): mean and range of G/(e mu).
Exact Fractions."""
import sys, math, importlib.util
from itertools import combinations
from fractions import Fraction as F
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def lonely_set(R):
    ivs = [(F(0), F(1))]
    for p in R:
        bands = [(F(6*k + 1, 6*p), F(6*k + 5, 6*p)) for k in range(p)]
        new = []
        for a, b in ivs:
            for c, d in bands:
                lo, hi = max(a, c), min(b, d)
                if lo <= hi: new.append((lo, hi))
        ivs = new
    ivs.sort()
    merged = []
    for a, b in ivs:
        if merged and a <= merged[-1][1]: merged[-1] = (merged[-1][0], max(merged[-1][1], b))
        else: merged.append((a, b))
    return merged
n = mism = win = 0; min_le = None; ratios = []
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    n += 1; e = S[-1]; R = S[:-1]
    L = lonely_set(R)
    G = sum(1 for j in range(e) if all(e <= (d*(6*j+1)) % (6*e) <= 5*e for d in S))
    Gs = sum(1 for j in range(e) if any(a <= F(6*j+1, 6*e) <= b for a, b in L))
    mism += G != Gs
    comps = [b - a for a, b in L]
    if L and L[0][0] == 0 and L[-1][1] == 1 and len(L) > 1: comps.append(L[0][1] - L[0][0] + L[-1][1] - L[-1][0])
    lam = max(comps) if comps else F(0)
    if lam * e >= 1: win += 1
    v = lam * e
    if min_le is None or v < min_le[0]: min_le = (v, S)
    mu = sum(comps[:len(L)])
    if G: ratios.append(G / float(e * mu))
print(f"HI={HI}: residual sets={n}; (i) mismatches G vs AP points in L: {mism}")
print(f"  (ii) window lambda >= 1/e holds for {win} sets ({win/n:.4f}); min lambda*e = {float(min_le[0]):.3f} at {min_le[1]}")
ratios.sort()
print(f"  (iii) G/(e*mu): min {ratios[0]:.3f}, median {ratios[len(ratios)//2]:.3f}, max {ratios[-1]:.3f}")
