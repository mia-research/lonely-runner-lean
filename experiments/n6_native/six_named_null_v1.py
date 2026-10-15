#!/usr/bin/env python3
"""Control for the named-multiplier finding (coprime case, gcd(e,6)=1, where m = 6j+1 <-> m mod e is a
bijection). For each set and cutoff C: N_C = set of named multipliers {+-c * inv(x) mod e : x element,
difference or sum, unit mod e, 1 <= c <= C}. Reports:
  coverage |N_C| / e, and whether N_C contains a good multiplier (observed);
  the probability that a uniformly random subset of Z/e of size |N_C| contains a good multiplier,
  1 - C(e - G, |N_C|) / C(e, |N_C|), with G the number of good multipliers (exact, no sampling).
Compares observed hit rate with the expected rate under the null, averaged over sets."""
import sys, math, importlib.util
from itertools import combinations
from fractions import Fraction
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def clear_all(S, e, m):
    einv = 1 if e % 6 == 1 else 5
    for d in S:
        w = (d * m) % e; c = (einv * (d - w)) % 6
        if not (1 <= c <= 4 or (c == 5 and w == 0)): return False
    return True
for C in (1, 2, 5):
    n = 0; obs = 0; exp_sum = 0.0; cov_sum = 0.0; full = 0
    for S in combinations(range(1, HI + 1), 5):
        if math.gcd(*S) != 1 or not r.six_residual(S): continue
        e = S[-1]
        if math.gcd(e, 6) != 1: continue
        good = {m for m in range(e) if clear_all(S, e, m)}
        if not good: continue
        n += 1
        xs = {x % e for x in list(S[:-1]) + [b - a for a, b in combinations(S, 2)] + [a + b for a, b in combinations(S[:-1], 2)]}
        invs = [pow(x, -1, e) for x in xs if x and math.gcd(x, e) == 1]
        N = {(sg * c * v) % e for v in invs for c in range(1, C + 1) for sg in (1, -1)}
        cov_sum += len(N) / e; full += len(N) == e
        obs += bool(N & good)
        G = len(good); k = len(N)
        p_miss = math.comb(e - G, k) / math.comb(e, k) if k <= e - G else 0.0
        exp_sum += 1 - p_miss
    print(f"HI={HI} C={C}: sets={n}; mean coverage |N|/e={cov_sum/n:.3f}; sets with full coverage={full}; "
          f"observed hit rate={obs/n:.4f}; expected under random list of same size={exp_sum/n:.4f}")
