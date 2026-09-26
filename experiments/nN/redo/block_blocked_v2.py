"""WP3 continued.  Which scale sets the longest blocked stretch L of a six-runner block?  Candidate law:
    L <= C / max(1, ...) -- tested as the products  L * min(F),  L * sigma5(F),  L * min(min F, sigma5(F)),
where sigma5(F) = the smallest spread of any FIVE of the six (a runner blocks an open quarter of the circle, so at least
five are needed to hold the slot continuously; four quarters that only touch leave clear points).
Families designed to separate the scales: one slow runner + a tight five-train; two slow + a tight four-train;
tight six-trains; spread blocks; random blocks.  Exact; Boundary Set Method (block_blocked_v1.longest_blocked)."""
import random
from fractions import Fraction as F
from itertools import combinations
from block_blocked_v1 import longest_blocked
rnd = random.Random(8)
def sig5(Fs):
    return min(max(c) - min(c) for c in combinations(sorted(Fs), 5))
def row(Fs):
    L = longest_blocked(Fs); m = min(Fs); s5 = sig5(Fs)
    return L * m, L * s5, L * min(m, s5)
def report(name, blocks):
    rs = [row(b) for b in blocks]
    print(f"  {name:48s} n={len(rs):3d}  max L*minF {float(max(r[0] for r in rs)):9.3f}  "
          f"max L*sigma5 {float(max(r[1] for r in rs)):8.3f}  max L*min(minF,sigma5) {float(max(r[2] for r in rs)):6.3f}")
for N in (1000, 10000):
    report(f"one slow a<=50 + tight five-train at N={N}", [[rnd.randint(5, 50)] + [N + e for e in sorted(rnd.sample(range(0, 40), 5))] for _ in range(30)])
for N in (1000, 10000):
    report(f"two slow + tight four-train at N={N}", sorted_ := [sorted(rnd.sample(range(5, 60), 2)) + [N + e for e in sorted(rnd.sample(range(0, 30), 4))] for _ in range(30)])
for N in (1000, 10000):
    report(f"tight six-train at N={N}", [[N + e for e in sorted(rnd.sample(range(0, 60), 6))] for _ in range(30)])
report("evenly spaced k*d+dev, d=200", [[k * 200 + rnd.randint(-40, 40) for k in range(1, 7)] for _ in range(30)])
report("random 6-sets in [1,1000]", [sorted(rnd.sample(range(1, 1001), 6)) for _ in range(60)])
report("random 6-sets in [1,100]", [sorted(rnd.sample(range(1, 101), 6)) for _ in range(60)])
