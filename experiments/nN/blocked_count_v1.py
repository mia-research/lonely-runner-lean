"""The blocked-numerator count at a live lattice D.

Candidates t_j = (8j+1)/(8D), j in Z/D.  d*t_j = d/(8D) + d*j/D, so in the discrete time j the runner
d moves on the circle with step d/D: with h = gcd(d, D) it visits the h/D-lattice through
phi = d/(8D), each point h times.  Blocked (circDist < 1/8, band test D <= d*a mod 8D <= 7D):
    B(d) = h * #{ k in [0, D/h) : || d/(8D) + k*h/D || < 1/8 }         (formula F)
Special cases: D | d  -> one point (d/D)/8, B = 0 on a live lattice (d/D not = 0 mod 8).
Checks: F against brute force on every (d, D), d < 2000, D <= 40.  Then, on the clearing lattice
D* of each set: the union bound sum_d B(d) vs D; the number of 'blind' runners (D | d); and the
same at L_0 when L_0 fails.  Objects as in ladder_live_steps_v1.
"""
import json, random
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce
from collections import Counter

def blocked_brute(d, D): return sum(1 for j in range(D) if not (D <= d * (8 * j + 1) % (8 * D) <= 7 * D))
def blocked_formula(d, D):
    h = gcd(d, D); phi = F(d, 8 * D)
    def near0(x):
        x = x % 1; return min(x, 1 - x) < F(1, 8)
    return h * sum(1 for k in range(D // h) if near0(phi + F(k * h, D)))
bad = [(d, D) for D in range(1, 41) for d in range(1, 2000) if blocked_brute(d, D) != blocked_formula(d, D)]
print(f"formula F vs brute force, d < 2000, D <= 40: {len(bad)} disagreements {bad[:5]}")
# range of B(d)/D for d coprime to D, and for D | d
co = Counter(); 
for D in range(2, 41):
    for d in range(1, 8 * D * 3):
        if gcd(d, D) == 1: co[(blocked_brute(d, D) - (2 * D - 1) / 8.0).__round__(3) >= -1] += 1
lo_hi = [(D, min(blocked_brute(d, D) for d in range(1, 16 * D) if gcd(d, D) == 1),
          max(blocked_brute(d, D) for d in range(1, 16 * D) if gcd(d, D) == 1)) for D in range(2, 17)]
print("coprime runners, (D, min B, max B):", lo_hi)

def clears(S, D, a): return all(D <= d * a % (8 * D) <= 7 * D for d in S)
def dead(S, D): return any(d % (8 * D) == 0 for d in S)
def ladder(S):
    D = 1; L0 = None
    while True:
        if not dead(S, D):
            if L0 is None: L0 = D
            if any(clears(S, D, 8 * j + 1) for j in range(D)): return L0, D
        D += 1
def profile(label, sets):
    ub = Counter(); blind = Counter(); cov = Counter()
    for S in sets:
        L0, D = ladder(S)
        B = [blocked_brute(d, D) for d in S]
        ub['union bound sum B < D' if sum(B) < D else 'union bound fails'] += 1
        blind[sum(1 for d in S if d % D == 0)] += 1
        cov[sum(1 for b in B if b == 0)] += 1
    print(f"{label} ({len(sets)}), at D*: {dict(ub)}")
    print(f"   runners with D | d (blind, clear for every j): {sorted(blind.items())}")
    print(f"   runners blocking no numerator at D*: {sorted(cov.items())}")
rnd = random.Random(27)
def prim(hi, n):
    out = set()
    while len(out) < n:
        S = tuple(sorted(rnd.sample(range(1, hi + 1), 7)))
        if reduce(gcd, S) == 1: out.add(S)
    return sorted(out)
profile("rule-miss sets 41..60", [tuple(S) for S in json.load(open('hard_sets_41_60.json'))])
profile("random primitive [1,10^3]", prim(10**3, 3000))
profile("random primitive [1,10^6]", prim(10**6, 3000))
