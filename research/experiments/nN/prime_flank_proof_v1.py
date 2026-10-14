"""THE MECHANISM, as an explicit construction.

Let n be PRIME and let no disparity be divisible by n (non-resonance).  Then n is invertible
mod n on e, so choose s in {1,...,n} with  e*s = 1 (mod n)  and set  j = (e*s - 1)/n,
a non-negative integer with j < e (since e*s <= n*e).

Then for every disparity d:
      d*(n*j + 1) = d*e*s,   and   d*e*s mod (n*e) = e * ((d*s) mod n),
which lies in [e, (n-1)e]  iff  n does not divide d*s.
n is prime, n does not divide d, and n does not divide s (s = e^{-1} mod n is nonzero), so done.

This works at ANY flank e, not only the largest -- and it FAILS at composite n precisely because
n | d*s does not follow from n|d and n|s.  That is why prime orders have no gap.
"""
import math
from itertools import combinations

def witness_j(e, n):
    s = pow(e, -1, n)          # e*s = 1 mod n ; s in 1..n-1
    assert (e * s) % n == 1
    return (e * s - 1) // n, s

def lonely_at(c, e, j, n):
    M = n*e; lo, hi = e, (n-1)*e
    return all(lo <= (d*(n*j+1)) % M <= hi for d in c)

print("check the construction on every non-resonant set, several PRIME orders")
print(f"{'n':>3} {'card':>5} {'range':>9} {'non-resonant sets':>18} {'construction works':>19}")
bad_ex = []
for n in (5, 7, 11, 13):
    for card, hi in ((4, 26), (5, 20), (6, 16)):
        if card > n - 1: continue
        tot = ok = 0
        for c in combinations(range(1, hi+1), card):
            g = c[0]
            for x in c[1:]: g = math.gcd(g, x)
            if g != 1: continue
            if any(d % n == 0 for d in c): continue     # resonant: excluded by hypothesis
            tot += 1
            e = c[-1]
            j, s = witness_j(e, n)
            if 0 <= j < e and lonely_at(c, e, j, n): ok += 1
            elif len(bad_ex) < 5: bad_ex.append((n, c, j, s))
        print(f"{n:>3} {card:>5} {('[1,'+str(hi)+']'):>9} {tot:>18} {ok:>19}"
              + ("" if ok == tot else "   *** MISMATCH ***"))
print()
if bad_ex: print("counterexamples:", bad_ex)
else: print("no counterexamples: the construction clears every non-resonant set at a prime order.")
print()
print("=== and it must fail at COMPOSITE n: n | d*s without n|d or n|s ===")
for n in (8, 9, 10, 12):
    witnesses = [(d, s) for d in range(1, n) for s in range(1, n)
                 if (d * s) % n == 0 and d % n and s % n]
    print(f"   n = {n:>2}: {len(witnesses):>3} pairs (d,s) with n | d*s but n∤d, n∤s"
          f"   e.g. {witnesses[:3]}")
for n in (5, 7, 11, 13):
    witnesses = [(d, s) for d in range(1, n) for s in range(1, n)
                 if (d * s) % n == 0 and d % n and s % n]
    print(f"   n = {n:>2} (prime): {len(witnesses)} such pairs")
