"""Which property of n drives the largest-flank failure rate: parity, divisor count, or primality?

Fix the blocker count k and sweep n.  For each n record the failure rate, alongside:
  parity, d(n) = number of divisors, whether n is prime, and the caged share (Thm 4.13).
"""
import math
from itertools import combinations

def works(c, n):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def ndiv(n): return sum(1 for d in range(1, n+1) if n % d == 0)
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n**.5)+1))
def caged(n): return sum(1 for d in range(1, n) if math.gcd(d, n) > 1) / (n - 1)

for k, hi in ((5, 18), (6, 15)):
    card = k + 1
    sets = [c for c in combinations(range(1, hi+1), card) if prim(c)]
    print(f"=== k = {k} blockers (card {card}), exhaustive primitive subsets of [1,{hi}]: {len(sets)} sets ===")
    print(f"{'n':>3} {'par':>5} {'prime':>6} {'d(n)':>5} {'caged':>6} {'failures':>9} {'rate':>9}")
    prev = None
    for n in range(card, 2*k + 4):
        bad = sum(1 for c in sets if not works(c, n))
        rate = bad / len(sets)
        arrow = ""
        if prev is not None and prev > 0:
            arrow = f"   x{prev/bad:.1f} better" if bad > 0 else "   -> 0"
        print(f"{n:>3} {'even' if n%2==0 else 'odd':>5} {str(isprime(n)):>6} {ndiv(n):>5} "
              f"{caged(n):>6.3f} {bad:>9} {rate:>9.5f}{arrow}")
        prev = bad
    print()
