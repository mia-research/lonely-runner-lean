"""The deformation picture (manuscript sections 4.2-4.4): what loneliness becomes at a reference instant.

Section 4.3: write the speeds as A + e against a progression A_k = v0 + k*d, and fix t = r/(n*d) with
gcd(r, n) = 1.
  Theorem 4.5: the progression part places the n runners on the n distinct n-ths, one each.
  Theorem 4.6: the deviation displaces runner k by exactly e_k*r/d EIGHTHS.

So at t = r/(n*d) runner k sits at  (k*r mod n)/n + (e_k*r/d)/n , i.e. slot (k*r mod n) displaced by
delta_k = e_k*r/d eighths. Consecutive slots are 1/n apart in the ideal, so the gap after the runner in
slot j is  (1 + delta_next - delta_here)/n, and Theorem 4.1 (gap >= 1/n) becomes

    delta_next >= delta_here

-- a pure ORDER condition on the displacement sequence, read around the cycle of slots.

Hence: a runner is lonely at the reference instant exactly when it sits at a NON-DESCENT of the cyclic
displacement sequence (both the step into it and the step out of it are >= 0).

This tests that characterisation against the definition. It also tests the consequence, which is
Corollary 4.4: the count of simultaneously lonely runners is never exactly 7.
"""
import random
from fractions import Fraction as F
from math import gcd

n = 8; INV = F(1, n)
def fract(z): return z - (z.numerator // z.denominator)
def cd(z):    return min(fract(z), 1 - fract(z))

def lonely_set(V, t):
    out = []
    for v in V:
        ds = [F(abs(v - w)) for w in V if w != v]
        if all(cd(F(d) * t) >= INV for d in ds): out.append(v)
    return sorted(out)

def by_descent(V, v0, d, r):
    """slots and displacements at t = r/(n*d); lonely = non-descent of the cyclic delta sequence."""
    slots = {}
    for k, v in enumerate(V):
        e = F(v) - (F(v0) + k * F(d))
        delta = e * r / F(d)                       # Theorem 4.6, in eighths
        s = (k * r) % n
        slots[s] = (delta, v)
    if len(slots) < n: return None                  # slots must be a bijection (Theorem 4.5)
    order = [slots[s] for s in range(n)]
    out = []
    for j in range(n):
        prev = order[(j - 1) % n][0]; here = order[j][0]; nxt = order[(j + 1) % n][0]
        # gap into j is (1 + here - prev)/n >= 1/n  <=>  here >= prev ; similarly out of j
        if here >= prev and nxt >= here: out.append(order[j][1])
    return sorted(out)

random.seed(20260917)
print("the non-descent characterisation at reference instants\n")
agree = 0; tested = 0; mism = []
for _ in range(4000):
    d = random.randint(1, 12); v0 = random.randint(0, 20)
    V = sorted({v0 + k * d + random.randint(-3, 3) for k in range(n)})
    if len(V) < n: continue
    r = random.choice([x for x in range(1, n) if gcd(x, n) == 1])
    t = F(r, n * d)
    got = by_descent(V, v0, d, r)
    if got is None: continue
    tested += 1
    truth = lonely_set(V, t)
    if got == truth: agree += 1
    elif len(mism) < 3: mism.append((V, v0, d, r, truth, got))
print(f"  non-descent vs the definition: agree {agree}/{tested}")
for m in mism: print("     DISAGREE", m)

print("\n  Corollary 4.4: the simultaneous count is never exactly 7")
from collections import Counter
h = Counter()
for _ in range(6000):
    d = random.randint(1, 12); v0 = random.randint(0, 20)
    V = sorted({v0 + k * d + random.randint(-4, 4) for k in range(n)})
    if len(V) < n: continue
    r = random.choice([x for x in range(1, n) if gcd(x, n) == 1])
    got = by_descent(V, v0, d, r)
    if got is not None: h[len(got)] += 1
print(f"     counts observed: {dict(sorted(h.items()))}")
print(f"     count 7 observed: {h.get(7,0)} times  (Corollary 4.4 says never)")
