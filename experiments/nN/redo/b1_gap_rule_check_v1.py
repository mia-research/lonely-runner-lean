"""E119: check of the DERIVED B1 rule (not an enumeration of the category): in 7 d_min < d_max < 9 d_min, if a reading
e >= 9 d_max/15 has no reading in (7e/9, e), the subject is lonely at 9/(8e).  Soundness is checked (every rule hit
is lonely there), and the derived failure condition (a 9/7-chain across the top 40%) against the lap-1 failures."""
import itertools
from fractions import Fraction as F
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def lonely(T, t): return all(nd(d * t) >= E8 for d in T)
N = 30; hit = unsound = 0; k1_not_rule = rule_miss = tot = 0
for T in itertools.combinations(range(1, N + 1), 7):
    a, b = T[0], T[-1]
    if not (7 * a < b < 9 * a): continue
    tot += 1
    es = [e for e in T if 15 * e >= 9 * b and not any(7 * e < 9 * d < 9 * e for d in T)]
    if es:
        hit += 1
        unsound += not all(lonely(T, F(9, 8 * e)) for e in es)
    k1 = any(lonely(T, F(9, 8 * e)) for e in T)
    if k1 and not es: k1_not_rule += 1
    if not k1 and es: rule_miss += 1
print("B1 sets to", N, ":", tot, "| derived rule applies:", hit, "| rule instants not lonely:", unsound,
      "| lap-1 lonely but rule silent:", k1_not_rule)
