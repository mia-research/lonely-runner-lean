"""Covering as pure congruences -- no real numbers, no division.

reach_mem says the witness is 1 or a right endpoint (n*m+1)/s.  finite_check says testing those
points settles covering.  So write "reading s' covers the endpoint (n*m+1)/s" without dividing:

    |s'(nm+1)/s - n k| < 1   <=>   |s'(nm+1) - n k s| < s   <=>   s'(nm+1) mod (n s) in (-s, s).

Check that against the real-interval computation, and measure how big the candidate set actually is.
"""
from fractions import Fraction as F
import random

def endpoints(S, n):
    """The candidate witness set: 1, and every right endpoint (n m + 1)/s inside [1, n-1]."""
    E = [F(1)]
    for s in S:
        m = 0
        while F(n*m + 1, s) <= n - 1:
            if F(n*m + 1, s) >= 1:
                E.append(F(n*m + 1, s))
            m += 1
    return sorted(set(E))

def covered_real(x, S, n):
    """x is inside some bad interval ((nm-1)/s, (nm+1)/s)."""
    for s in S:
        y = x * s          # want dist(y, n*Z) < 1
        k = round(F(y, n))
        if abs(y - n*k) < 1:
            return True
    return False

def covered_cong(num, den, S, n):
    """x = num/den with den = s.  No division: s'(num) mod (n*den) within den of 0."""
    for s in S:
        v = (s * num) % (n * den)
        if v < den or v > n*den - den:
            return True
    return False

random.seed(20260919)
n = 8
mism = 0
sizes = []
for _ in range(3000):
    k = random.randint(4, 7)
    S = sorted(random.sample(range(2, 60), k))
    E = endpoints(S, n)
    sizes.append(len(E))
    for x in E:
        a, b = x.numerator, x.denominator
        if covered_real(x, S, n) != covered_cong(a, b, S, n):
            mism += 1
print(f"congruence form vs real form, on every candidate of 3000 profiles: "
      f"{sum(sizes)} points, {mism} mismatches")
print(f"candidate-set size: min {min(sizes)}, median {sorted(sizes)[len(sizes)//2]}, max {max(sizes)}")

# and the finite check must agree with the full sweep
import importlib.util
spec = importlib.util.spec_from_file_location("rr", "experiments/n8/reach_rule_v1.py")
bad = 0
def intervals(S, n):
    out = []
    for s in S:
        m = 1
        while F(n*m - 1, s) < n - 1:
            if F(n*m + 1, s) > 1:
                out.append((F(n*m - 1, s), F(n*m + 1, s)))
            m += 1
    out.sort(); return out
def sweep_covers(S, n):
    r = F(1)
    for a, b in intervals(S, n):
        if a < r: r = max(r, b)
        else: return False
    return r > n - 1
for _ in range(3000):
    k = random.randint(4, 7)
    S = sorted(random.sample(range(2, 60), k))
    fin = all(covered_cong(x.numerator, x.denominator, S, n) for x in endpoints(S, n)[1:]) \
          and covered_cong(1, 1, S, n)
    if fin != sweep_covers(S, n):
        bad += 1
print(f"finite congruence check vs full sweep, 3000 profiles: {bad} mismatches")
