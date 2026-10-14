"""Native: with p < q (the largest-flank condition), where does shadowing first appear?
q <= 7 gave 0 over 74,613 multisets; q <= 9 gave 33.  If the boundary is exactly q = 8 = n,
that is the n-1 constant again -- the same place small_b_blocks_iff breaks."""
from itertools import combinations_with_replacement
from math import gcd, lcm

def blocks(p, A, q):
    M = 8*q; r = (p*A) % M
    return min(r, M-r) < q
def shadowed(pairs):
    L = lcm(*[q for _, q in pairs])
    return all(any(blocks(p, 8*k+1, q) for p, q in pairs) for k in range(L))

print(f"{'max q':>6} {'movers':>7} {'multisets':>12} {'shadowing':>10}  first example")
for Q in range(2, 10):
    pool = [(p, q) for q in range(2, Q+1) for p in range(1, q) if gcd(p, q) == 1]
    if not pool: continue
    n = 0; sh = 0; ex = None
    for m in combinations_with_replacement(pool, 6):
        n += 1
        if shadowed(list(m)):
            sh += 1
            if ex is None: ex = m
    print(f"{Q:>6} {len(pool):>7} {n:>12,} {sh:>10}  {ex if ex else ''}")
print()
print("  8 = n.  small_b_blocks_iff holds for 2 <= b <= n-1 = 7 and breaks at b = n = 8.")
