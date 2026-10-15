#!/usr/bin/env python3
"""Coprime case (largest e, gcd(e,6)=1) of primitive SixResidual. Good multipliers m in Z/e: by CRT,
opening j <-> m = (6j+1) mod e is a bijection, and d is clear iff
    c_d = einv*(d - (d*m mod e)) mod 6 in {1..4}  (or c_d = 5 and d*m = 0 mod e).
Named candidates: m = c * inv(d) mod e for d in S, gcd(d,e)=1, c in [-K, K] \ {0}.
Reports, per set, the least |c| for which a named candidate is good, and its distribution."""
import sys, math, importlib.util
from itertools import combinations
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1]); K = int(sys.argv[2])
def clear_all(S, e, m):
    einv = 1 if e % 6 == 1 else 5
    for d in S:
        w = (d * m) % e; c = (einv * (d - w)) % 6
        if not (1 <= c <= 4 or (c == 5 and w == 0)): return False
    return True
dist = Counter(); n = 0; worst = []
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if math.gcd(e, 6) != 1: continue
    n += 1
    if not any(clear_all(S, e, m) for m in range(e)): dist["no good m"] += 1; continue
    best = None
    for c in range(1, K + 1):
        for sg in (c, -c):
            for d in S[:-1]:
                if math.gcd(d, e) != 1: continue
                m = (sg * pow(d, -1, e)) % e
                if clear_all(S, e, m): best = c; break
            if best: break
        if best: break
    dist[best if best else f">{K}"] += 1
    if not best and len(worst) < 6: worst.append(S)
print(f"HI={HI}, K={K}: coprime-case sets={n}; least |c| with a good named multiplier c*inv(d):")
for k in sorted(dist, key=str): print("  ", k, dist[k])
print("  examples beyond K:", worst)
