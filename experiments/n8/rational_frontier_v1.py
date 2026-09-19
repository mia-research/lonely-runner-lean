"""What IS the rational-reading frontier, in our own objects?

Readings s_i = d_i/d_min are RATIOS, so scale-invariant: scaling speeds does not make them integers.
But with Q = lcm of their denominators, s_i = a_i/Q with a_i integers, and
        ||s_i t|| >= 1/8   <=>   ||a_i tau|| >= 1/8   with tau = t/Q.
Since s_1 = 1, a_1 = Q.  And s_i >= 1 so a_i >= Q.

CLAIM: rational-reading profiles are exactly integer-SPEED profiles whose minimum speed is Q > 1
-- i.e. integer speeds WITHOUT a unit speed.  Test the equivalence, and see which of our theorems
survive the loss of the unit reading.
"""
from fractions import Fraction as F
from itertools import combinations
from math import lcm, gcd
import random

def clear(speeds, tau):
    for s in speeds:
        y = F(s)*tau
        if abs(y - 8*round(y/8)) < 1: return False
    return True

def has_witness_rational(S):
    """S rational readings with S[0]=1.  Search exactly via the candidate set."""
    Q = lcm(*[F(x).denominator for x in S])
    A = [int(F(x)*Q) for x in S]
    return has_witness_int(A), A, Q

def has_witness_int(A):
    """Integer speeds: candidates tau = (8k+1)/(8a) over a in A (witness_normalised)."""
    for a in A:
        k = 0
        while F(8*k+1, 8*a) <= F(7,8):
            tau = F(8*k+1, 8*a)
            if tau >= F(1,8) and clear(A, tau): return True
            k += 1
    return False

rng = random.Random(20260919)
print("1. equivalence check: rational readings vs their cleared-denominator integer speeds")
mism = 0; tot = 0
for _ in range(4000):
    S = [F(1)] + sorted(F(rng.randint(2,40), rng.randint(1,6)) for _ in range(6))
    if len(set(S)) != 7 or min(S) != 1: continue
    tot += 1
    r, A, Q = has_witness_rational(S)
    # direct search on the readings themselves, same candidate family
    direct = False
    for s in S:
        k = 0
        while F(8*k+1, 8)/s <= F(7,8):
            tau = F(8*k+1, 8)/s
            if tau >= F(1,8) and clear(S, tau): direct = True; break
            k += 1
        if direct: break
    if r != direct: mism += 1
print(f"   {tot:,} rational profiles, mismatches = {mism}")

print("\n2. what is lost: the unit reading")
print("   integer speeds with a unit (min = 1):  unit_never_blocks applies, blockers <= n-3")
print("   integer speeds with min = Q > 1:       it does NOT, blockers <= n-2")
# measure: does the minimum speed ever block a candidate when min > 1?
blocked = tot2 = 0
for _ in range(20000):
    A = sorted(rng.sample(range(2, 200), 7))
    a0 = A[0]
    for a in A:
        k = 0
        while F(8*k+1, 8*a) <= F(7,8):
            tau = F(8*k+1, 8*a)
            if tau >= F(1,8):
                tot2 += 1
                y = F(a0)*tau
                if abs(y - 8*round(y/8)) < 1: blocked += 1
            k += 1
print(f"   minimum speed (>1) blocks a candidate in {blocked:,} of {tot2:,} cases"
      f"  ({100*blocked/max(tot2,1):.2f}%)  -- it is NOT a non-blocker")
