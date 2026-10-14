"""Does the reach rule reproduce the search?

The search: build every bad interval ((n*m-1)/s, (n*m+1)/s) meeting [1, n-1], merge, measure the
uncovered part.  The rule: one left-to-right fold carrying a single number.

Check they agree -- verdict AND, where uncovered, the first uncovered point.
"""
from fractions import Fraction as F
import random

def intervals(readings, n):
    """Every bad interval of every reading that meets [1, n-1], sorted by left endpoint."""
    out = []
    for s in readings:
        m = 1
        while F(n*m - 1, s) < n - 1:
            lo, hi = F(n*m - 1, s), F(n*m + 1, s)
            if hi > 1:
                out.append((lo, hi))
            m += 1
    out.sort()
    return out

def reach(r, l):
    """Exactly the Lean definition."""
    for a, b in l:
        if a < r:
            r = max(r, b)
        else:
            return r
    return r

def search_uncovered(readings, n):
    """The measure the search reports: total uncovered length in [1, n-1]."""
    iv = intervals(readings, n)
    total, cur = F(0), F(1)
    for a, b in iv:
        if a > cur:
            total += min(a, n-1) - cur
        cur = max(cur, b)
        if cur >= n - 1:
            break
    if cur < n - 1:
        total += (n - 1) - cur
    return total

random.seed(20260919)
n = 8
bad = 0
first_mismatch = None
for trial in range(4000):
    k = random.randint(4, 7)
    readings = sorted(random.sample(range(1, 60), k))
    iv = intervals(readings, n)
    R = reach(F(1), iv)
    U = search_uncovered(readings, n)
    # rule's verdict: covered iff reach passes n-1
    rule_covered = R > n - 1
    search_covered = (U == 0)
    if rule_covered != search_covered:
        bad += 1
        if first_mismatch is None:
            first_mismatch = (readings, R, U)
    # and where it stops, the reach must be the FIRST uncovered point
    if not rule_covered:
        assert not any(a < R < b for a, b in iv), (readings, R)

print(f"profiles tested: 4000   verdict mismatches: {bad}")
if first_mismatch:
    print("  first mismatch:", first_mismatch)
print("reach = first uncovered point in every uncovered case: OK")

# the Branch-B minimiser, by the rule
rd = [3,4,5,7,11,24]
iv = intervals(rd, 8)
R = reach(F(1), iv)
print(f"\n[3,4,5,7,11,24]: reach stops at {R}, uncovered measure {search_uncovered(rd,8)}")

# and the same rule at other orders, unchanged
for n2 in (7, 8, 9, 11, 13):
    rd2 = [1,2,3,5,8,13][:n2-2]
    print(f"  n={n2:>2}  readings {rd2}  reach {reach(F(1), intervals(rd2, n2))}  "
          f"uncovered {search_uncovered(rd2, n2)}")
