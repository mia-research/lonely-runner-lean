"""H sharpened: can six movers with p < q (every numerator below its modulus) shadow?
Attack exhaustively over small moduli, where structure is strongest, then adversarially."""
from itertools import product, combinations_with_replacement
import random

def blocks(p, A, q):
    M = 8*q; r = (p*A) % M
    return min(r, M-r) < q
def shadowed(pairs, kmax=None):
    from math import lcm
    L = lcm(*[q for _, q in pairs])          # the condition is periodic in k with period lcm(q)
    return all(any(blocks(p, 8*k+1, q) for p, q in pairs) for k in range(L))

print("1. EXHAUSTIVE over all multisets of 6 movers with q <= 7, p < q, gcd(p,q)=1")
from math import gcd
pool = [(p, q) for q in range(2, 8) for p in range(1, q) if gcd(p, q) == 1]
print(f"   mover pool: {len(pool)}  -> {len(list(combinations_with_replacement(pool,6))):,} multisets")
found = []
for m in combinations_with_replacement(pool, 6):
    if shadowed(list(m)): found.append(m)
print(f"   shadowing multisets: {len(found)}")
for f in found[:5]: print(f"      {f}")

print("\n2. EXHAUSTIVE, q <= 9")
pool9 = [(p, q) for q in range(2, 10) for p in range(1, q) if gcd(p, q) == 1]
cnt = 0; found9 = []
for m in combinations_with_replacement(pool9, 6):
    cnt += 1
    if shadowed(list(m)): found9.append(m)
print(f"   multisets {cnt:,}   shadowing: {len(found9)}")
for f in found9[:5]: print(f"      {f}")

print("\n3. adversarial, larger moduli: maximise the first clear k")
rng = random.Random(20260919)
def first_clear(pairs, kmax=200000):
    for k in range(kmax):
        if not any(blocks(p, 8*k+1, q) for p, q in pairs): return k
    return None
best = (-1, None)
poolB = [(p, q) for q in range(2, 200) for p in (rng.randrange(1, q),) if gcd(p, q) == 1]
for _ in range(60):
    m = [rng.choice(poolB) for _ in range(6)]
    cur = first_clear(m, 20000)
    if cur is None: print(f"   SHADOWED: {m}"); break
    for _ in range(150):
        w = list(m); j = rng.randrange(6); w[j] = rng.choice(poolB)
        c = first_clear(w, 20000)
        if c is None: m = w; cur = 10**9; break
        if c > cur: m, cur = w, c
    if cur > best[0]: best = (cur, list(m))
print(f"   max first-clear k reached: {best[0]}")
