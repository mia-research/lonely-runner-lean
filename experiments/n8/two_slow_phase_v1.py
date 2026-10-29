# H06 with two slow participants, phase structure (E634).  Rates r1 < r2 in (0,1) (r = s/g), common offset u0 >= 0 (the F quotient instant).
# Return k in N is good when both dist(r_j (u0 + k)) >= 1/8.  Exact Fractions.  For every pair of rates and offset: least good k, or None up to KMAX.
import math, sys
from fractions import Fraction as F
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
D = int(sys.argv[1]); KMAX = int(sys.argv[2])
worst = (0, None); fails = []
rates = [F(a, D) for a in range(1, D)]
offs = [F(b, D) for b in range(0, D)]
for i, r1 in enumerate(rates):
    for r2 in rates[i + 1:]:
        for u0 in offs:
            k = 0
            while k <= KMAX and not (dist(r1 * (u0 + k)) >= E and dist(r2 * (u0 + k)) >= E): k += 1
            if k > KMAX: fails.append((r1, r2, u0))
            elif k > worst[0]: worst = (k, (r1, r2, u0))
print('D', D, 'pairs of rates', len(rates) * (len(rates) - 1) // 2, 'offsets', len(offs))
print('failures', len(fails), [(str(a), str(b), str(c)) for a, b, c in fails[:8]])
print('worst least k', worst[0], [str(x) for x in worst[1]] if worst[1] else None)
