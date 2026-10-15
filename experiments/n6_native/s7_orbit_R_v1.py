#!/usr/bin/env python3
"""E55: the step 'main route fails only on G4, G7' as one number per orbit. Orbit G = <(a, b)> in (Z/n)^2, a, b not 0
mod n (§7: D divides neither v1 nor v3), order n. Point (x, y) = (i/n, j/n) is in BHK's P for ratio rho = v1/v3 iff
1/6 <= x <= 5/6, 1/6 <= y <= 5/6, and rho <= min((y - 1/6)/(x - 1/6), (5/6 - y)/(5/6 - x)) (each bound only when its
denominator is positive). R(G) = max over points of that bound (0 if no point in the strip). Main route fails iff
rho > R(G). §7 has rho < 1/3. Part 1: check R against the meeting-time data (s7_exceptional_v2_80.out lists sets where
the main route fails; every other §7 set succeeds). Part 2: all orbits for n <= N with R(G) < 1/3."""
import sys, math
from fractions import Fraction as F
from collections import Counter
s6, s56 = F(1, 6), F(5, 6)
def R_of(points):
    best = F(-1)
    for x, y in points:
        if not (s6 <= x <= s56 and s6 <= y <= s56): continue
        b = []
        if x > s6: b.append((y - s6) / (x - s6))
        if x < s56: b.append((s56 - y) / (s56 - x))
        r = min(b) if b else F(10**9)
        best = max(best, r)
    return best
def orbit(a, b, n): return {(F(a * k % n, n), F(b * k % n, n)) for k in range(n)}
N = int(sys.argv[1])
# Part 1: against data to 40
import itertools
mism = Counter()
exc = set(tuple(map(int, l.split()[1:6])) for l in open("s7_exceptional_v2_80.out") if l.startswith("EXC"))
for v1 in range(1, 41):
    for v2 in range(v1 + 1, 41):
        for v3 in range(v2 + 1, 41):
            if not 3 * v1 < v3: continue
            D = v3 - v2
            if v1 % D == 0 or v3 % D == 0: continue
            g = math.gcd(math.gcd(D, v1), v3); n = D // g
            R = R_of(orbit(v3 // g % n, v1 // g % n, n))
            fails = F(v1, v3) > R
            # any v4, v5 give the same meeting-time verdict (main route depends on v1..v3 only); compare with data
            sample = [(v1, v2, v3, v4, v5) for v4 in range(v3 + 1, 41) for v5 in range(v4 + 1, 41)
                      if math.gcd(math.gcd(math.gcd(v1, v2), math.gcd(v3, v4)), v5) == 1]
            for S in sample[:3]:
                mism[(fails, S in exc)] += 1
print("Part 1, (R predicts failure, data says failure):", dict(mism))
# Part 2
seen = set(); low = []
for n in range(2, N + 1):
    for a in range(1, n):
        for b in range(1, n):
            if math.gcd(math.gcd(a, b), n) != 1: continue
            P = frozenset(orbit(a, b, n))
            if (n, P) in seen: continue
            seen.add((n, P))
            R = R_of(P)
            if R < F(1, 3): low.append((n, a, b, R))
print(f"Part 2: orbits of order n <= {N} not on an axis: {len(seen)}; with R(G) < 1/3: {len(low)}")
for n, a, b, R in low: print(f"   n = {n}, generator ({a}, {b}), R = {R}")
