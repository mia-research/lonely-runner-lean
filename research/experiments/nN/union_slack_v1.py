"""How much slack does n=5 have?  Union of blocked sets vs e, and where the overlap lives.

Structure found by the tracer:
  * every non-flank blocker blocks j=0, and its run around 0 is roughly (-(e/d)/n, (e/d)/n),
    so those runs are NESTED in d -- the largest blocker gives the smallest.
  * one blocker never blocks more than e/2 openings (max ratio n/4 at every order).
Inclusion-exclusion with only the j=0 overlap gives union <= 6e/5 - 4e/(5 d_max), which beats e
only when the largest blocker is < 4.  So more overlap must be forced.  Measure it.
"""
import math
from itertools import combinations

def blocked_set(d, e, n):
    M = n*e
    return {j for j in range(e) if not (e <= (d*(n*j+1)) % M <= (n-1)*e)}

def stats(c, n):
    e = c[-1]; bs = [blocked_set(d,e,n) for d in c[:-1]]
    S1 = sum(len(b) for b in bs)
    U = set().union(*bs) if bs else set()
    return len(U)/e, S1/e, len(bs)

print("=== union / e  (must stay < 1 for the door to hold) ===")
print(f"{'n':>3} {'range':>9} {'sets':>9} {'max union/e':>12} {'max sum/e':>10} {'#union=1':>9}   witness at max union")
for n, hi in [(5,40),(5,60),(5,80),(6,26),(6,34),(7,20),(8,16)]:
    k = n-1
    mu, ms, full, tot, w = 0.0, 0.0, 0, 0, None
    for c in combinations(range(1,hi+1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g,x)
        if g != 1: continue
        tot += 1
        u, s, _ = stats(c, n)
        if u >= 1.0: full += 1
        if u > mu: mu, w = u, c
        ms = max(ms, s)
    print(f"{n:>3} {('[1,'+str(hi)+']'):>9} {tot:>9} {mu:>12.5f} {ms:>10.3f} {full:>9}   {w}")

print()
print("=== at n=5: how does max union/e depend on e? (slack vs size) ===")
print(f"{'e':>5} {'sets':>8} {'max union/e':>12} {'min survivors':>14}  witness")
for e in range(4, 61):
    mu, mn, tot, w = 0.0, 10**9, 0, None
    for rest in combinations(range(1,e), 3):
        c = rest + (e,)
        g = c[0]
        for x in c[1:]: g = math.gcd(g,x)
        if g != 1: continue
        tot += 1
        u, s, _ = stats(c, 5)
        surv = e - round(u*e)
        if u > mu: mu, w = u, c
        mn = min(mn, surv)
    if tot and e % 6 == 0 or e < 10:
        print(f"{e:>5} {tot:>8} {mu:>12.5f} {mn:>14}  {w}")
