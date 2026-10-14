"""Do we need 9 and 10, or do we already have enough to generalise?

Almost every rule is ALREADY general n in Lean: flankWorks_of_prime (prime n), the band ladder,
the self-similar reduction, the shifted/witness certificates, the irrational reduction, and
ratWorks_le_order.  So the generalisation question is not "run more orders" but:

    WHEN DOES THE WHOLE RULE FAMILY FAIL AT ONCE?

For the divisibility rules q = 2..n the answer is a clean arithmetic condition with no measure in
it: rule q fails exactly when some disparity is divisible by q.  So ALL of them fail exactly when
the disparities COVER every q in [2,n] by divisibility -- and since q prime forces it, every
prime p <= n must divide some disparity.  That is a set-cover condition, decidable, order-general.
"""
from itertools import combinations
import random, math
def primes_upto(n): return [p for p in range(2,n+1) if all(p%r for r in range(2,p))]
def all_div_rules_fail(ds, n):
    return all(any(d % q == 0 for d in ds) for q in range(2, n+1))
def primes_covered(ds, n):
    return all(any(d % p == 0 for d in ds) for p in primes_upto(n))
random.seed(5)
N = 40000
print(f"{N} random primitive (n-1)-tuples per order, entries from [1,300]")
print(f"{'n':>3} {'type':>16} {'primes<=n':>10} {'all q-rules fail':>17} {'primes all covered':>19}")
for n in (5,6,7,8,9,10,11,12):
    k=n-1; fails=0; pc=0; got=0; examples=[]
    while got < N:
        ds = tuple(sorted(random.sample(range(1,301), k)))
        g = ds[0]
        for x in ds[1:]: g = math.gcd(g,x)
        if g != 1: continue
        got += 1
        f = all_div_rules_fail(ds, n)
        if f:
            fails += 1
            if len(examples) < 2: examples.append(ds)
        if primes_covered(ds, n): pc += 1
    ps = primes_upto(n)
    typ = "prime" if len(ps)>0 and ps[-1]==n else ("prime power" if any(n==p**e for p in ps for e in (2,3,4)) else "composite")
    print(f"{n:>3} {typ:>16} {str(ps):>10} {fails:>17} {pc:>19}")
    if examples: print(f"       all-fail examples: {examples}")
