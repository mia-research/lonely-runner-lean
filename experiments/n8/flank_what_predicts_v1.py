"""What predicts a shadowed flank: the NUMBER of non-integer ratios, or their DENOMINATORS?

The withdrawn Proposition 6.11 framed the open case as |J| >= 4 (four or more non-integer
ratios).  Two things already contradict that framing:
  * CORRECTIONS_2026_09_17_v2 section 2: live flanks fail at every j from 2 up.
  * flank_route_limit_v1: with SEVEN random real differences -- so six ratios that are
    generically irrational, i.e. |J| = 6 -- the flank route is trivial, median k = 0 and
    max k = 4 over 3,000 arrangements.

If |J| were the difficulty, |J| = 6 would be the hardest case, and it is the easiest.
This measures the alternative: that shadowing is governed by the ratio DENOMINATORS.
"""
import math
from fractions import Fraction
from itertools import combinations

n = 8
TH = Fraction(1, n)

def circ_q(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def flank_stats(ds, e):
    others = [d for d in ds if d != e]
    rs = [Fraction(d, e) for d in others]
    fr = [r - (r.numerator // r.denominator) for r in rs]
    J = [f for f in fr if f != 0]
    if any(f == 0 and (r / n).denominator == 1 for f, r in zip(fr, rs)):
        pass
    # dead flank: some ratio is a nonzero multiple of n
    if any(f == 0 and r != 0 and r.numerator % n == 0 for f, r in zip(fr, rs)):
        return None
    per = 1
    for f in fr:
        per = per * f.denominator // math.gcd(per, f.denominator)
    if per > 200000:
        return None
    shadowed = True
    for k in range(per):
        if all(circ_q(k * f + r / n) >= TH for f, r in zip(fr, rs)):
            shadowed = False
            break
    maxden = max((f.denominator for f in J), default=1)
    return len(J), maxden, shadowed

byJ = {}
byden = {}
tot = shad = 0
for S in combinations(range(1, 19), 7):
    for e in S:
        st = flank_stats(S, e)
        if st is None:
            continue
        J, maxden, sh = st
        tot += 1
        shad += sh
        a = byJ.setdefault(J, [0, 0]); a[0] += 1; a[1] += sh
        b = byden.setdefault(maxden, [0, 0]); b[0] += 1; b[1] += sh

print(f"live flanks examined (7-subsets of [1,18]) : {tot}")
print(f"shadowed                                   : {shad}  ({100*shad/tot:.2f}%)")
print()
print("BY |J|, the withdrawn criterion's variable:")
print(f"  {'|J|':>4} {'flanks':>9} {'shadowed':>9} {'rate':>8}")
for J in sorted(byJ):
    c, s = byJ[J]
    print(f"  {J:>4} {c:>9} {s:>9} {100*s/c:>7.2f}%")
print()
print("BY LARGEST RATIO DENOMINATOR:")
print(f"  {'den':>4} {'flanks':>9} {'shadowed':>9} {'rate':>8}")
for d in sorted(byden):
    c, s = byden[d]
    if c >= 50:
        print(f"  {d:>4} {c:>9} {s:>9} {100*s/c:>7.2f}%")

print()
print("READING.")
print("  |J| does NOT predict shadowing. The rate PEAKS at |J| = 4 (27.0%) and FALLS to")
print("  9.0% at |J| = 6. The withdrawn Proposition 6.11 named |J| >= 4 as the open case;")
print("  |J| = 6 is close to the easiest non-trivial value, and with seven random REAL")
print("  differences -- |J| = 6 almost surely -- the route is trivial (median k = 0).")
print()
print("  The DENOMINATOR does predict it, and the trend is monotone apart from parity:")
print("  46.97% at denominator 2 down to 0.11% at 17. At comparable size EVEN beats ODD")
print("  (2: 47.0, 4: 45.8, 6: 18.0, 8: 19.0  vs  3: 25.7, 5: 20.7, 7: 12.4, 9: 7.2),")
print("  which is what an arc of half-width 1/8 about 0 should do: an even denominator")
print("  puts orbit points on the antipode and the symmetric points.")
print()
print("  This agrees with Proposition 6.10 -- the only shadowing PAIRS have both")
print("  fractional parts 1/2, i.e. denominator 2 -- and with the recorded shadowing")
print("  triples (2,4,4), (3,3,3), (3,6,6), (5,5,5): all small, mostly even.")
print()
print("CONSEQUENCE FOR WHERE THE HOLE IS.")
print("  Difficulty sits at SMALL RATIO DENOMINATORS, which is exactly where the lattice")
print("  machinery applies: a rational ratio of denominator c lies on the c-lattice, so")
print("  circDist_periodic_of_lattice makes the flank's verdict periodic and the question")
print("  finite. Each such arrangement is therefore DECIDABLE -- these runs decide them by")
print("  exhausting one period. What is missing is not a new case split but a UNIFORM")
print("  statement over denominators. A proof must be uniform in c, not a split on |J|.")
