"""The near-lattice rule (owner: replace the lattice with an invariant scale, as the cascade does).  Exact.
S = seven positive whole-number readings, reduced, every six coprime (the class the exact off-lattice rule leaves).
For x in S, D = S \\ {x}: tau = D's first lonely instant at 1/7 (exact cascade at threshold 1/7), margin mu =
min_d circDist(d tau) - 1/8 >= 1/56.  A step Delta = a/b (b <= B): each d in D drifts by ||d Delta|| per step; x moves by
frac(x Delta).  The rule fires if some k <= K has t = tau + k Delta lonely for all seven (checked exactly).
Also recorded: the drift bound k * max_d ||d Delta|| <= mu at the firing k (the analytic sufficient condition), and the
sets on which it never fires (the structured remainder), with their small integer relations."""
import random
from fractions import Fraction as F
from math import gcd, floor
from functools import reduce
from arrangement_lib import nd
def cascade_q(ds, q):
    t = F(1, q * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, q)]
        if not way: return t
        t = max((F(floor(d * t - F(1, q)) + 1) + F(1, q)) / d for d in way)
def near_lattice(S, B=40, K=6):
    for x in S:
        D = [d for d in S if d != x]; tau = cascade_q(D, 7)
        mu = min(nd(d * tau) for d in D) - F(1, 8)
        for b in range(2, B + 1):
            for a in range(1, b):
                if gcd(a, b) != 1: continue
                Dl = F(a, b); drift = max(nd(d * Dl) for d in D)
                for k in range(1, K + 1):
                    t = tau + k * Dl
                    if all(nd(d * t) >= F(1, 8) for d in S):
                        return x, Dl, k, drift, mu, k * drift <= mu
    return None
rnd = random.Random(7); tested = fired = analytic = 0; left = []
while tested < 300:
    S = sorted(rnd.sample(range(1, 400), 7)); g = reduce(gcd, S); S = [s // g for s in S]
    if not all(reduce(gcd, [d for d in S if d != x]) == 1 for x in S): continue
    tested += 1; r = near_lattice(S)
    if r: fired += 1; analytic += r[5]
    else: left.append(S)
print(f"generic sets (reduced, every six coprime), random in [1,400]: {tested}")
print(f"  near-lattice rule fires (Delta = a/b, b <= 40, k <= 6): {fired}; of these the drift bound k*drift <= margin holds: {analytic}")
print(f"  not fired: {len(left)}  e.g. {left[:5]}")
for S in [(2,12,15,21,32,34,38), (4,5,6,8,14,32,37), (4,5,6,14,17,32,38), (4,7,8,15,29,36,37)]:
    r = near_lattice(list(S))
    print(f"  residual {S}: " + (f"fires: x={r[0]}, Delta={r[1]}, k={r[2]}, drift={r[3]}, margin={r[4]}, bound holds={r[5]}" if r else "does not fire"))
