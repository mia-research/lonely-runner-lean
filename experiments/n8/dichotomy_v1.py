"""The exact problem IS our n=8 problem with 6 speeds {1, s_1..s_5} plus integrality q = m*x/8.

witness_normalised: the witness is x = 1, or x = (8k+1)/s for one of the speeds.
  x = u (an odd integer in 1..7)  ->  q = u*m/8, integral iff 8 | m.
  x = (8k+1)/s                    ->  q = b*(8k+1)/8 where b = m/s, integral iff 8 | b.
So integrality is governed by 8 | m and by which b_i are divisible by 8 -- the SAME collision
criterion, one level up.  Split on it and see which construction covers which case.
"""
from itertools import combinations
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q, m, bs): return all(I(b)[0] <= q % b <= I(b)[1] for b in bs + [m])

def spine_q(m, bs):
    """x = u odd in {1,3,5,7} -> q = u*m/8.  Needs 8 | m."""
    if m % 8: return None
    for u in (1,3,5,7):
        q = u*m//8
        if ok(q, m, bs): return q
    return None

def endpoint_q(m, bs):
    """x = (8k+1)/s -> q = b(8k+1)/8, needs 8 | b for some modulus b."""
    for b in bs:
        if b % 8: continue
        k = 0
        while True:
            q = b*(8*k+1)//8
            if q >= m: break
            if ok(q, m, bs): return q
            k += 1
    return None

tab = Counter(); tot = 0
for m in range(24, 320):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        bs = sorted(m//s for s in c); tot += 1
        has8 = any(b % 8 == 0 for b in bs)
        m8 = (m % 8 == 0)
        got = (spine_q(m, bs) is not None) or (endpoint_q(m, bs) is not None)
        tab[(m8, has8, got)] += 1
print(f"divisor-closed, exhaustive m < 320 : {tot:,}\n")
print(f"{'8|m':>5} {'some 8|b_i':>11} {'covered by the two easy constructions':>40}")
for (m8, h8, got), n in sorted(tab.items()):
    print(f"{str(m8):>5} {str(h8):>11}   {'YES' if got else 'NO ':>8}  {n:>8,}  ({100*n/tot:5.2f}%)")
cov = sum(n for (a,b,g),n in tab.items() if g)
print(f"\n  total covered by spine-or-endpoint : {cov:,}  ({100*cov/tot:.2f}%)")
print(f"  residual needing something else    : {tot-cov:,}  ({100*(tot-cov)/tot:.2f}%)")
