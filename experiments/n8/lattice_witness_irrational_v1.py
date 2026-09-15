"""The lattice route on irrational readings, exactly. Readings s = a + b·√2 (a, b rational). Lattice L: instants u = p/(nL).
Runner clear at u iff the fractional part of s·u lies in [1/n, 1 − 1/n]; decided exactly by integer square-root comparisons,
no floating point and no periodicity. A lattice is dead when some runner sits on the subject at every lattice instant, i.e.
s/(nL) is an integer (possible only for b = 0). Reports least lattice with a lonely instant (p searched to a stated bound)
and the gap from the first live lattice, for arrangements with irrational readings."""
from fractions import Fraction as F
from math import isqrt, floor, ceil, lcm
import random
from collections import Counter
def sgn_b_sqrt2_minus_c(B, C):          # sign of B·√2 − C, integers
    if B == 0: return (0 > C) - (0 < C)
    if B > 0 and C < 0: return 1
    if B < 0 and C > 0: return -1
    lhs, rhs = 2 * B * B, C * C
    if B > 0: return 1 if lhs > rhs else -1   # C >= 0; equality impossible (√2 irrational) unless B=C=0
    return -1 if lhs > rhs else 1              # B < 0, C <= 0
def sign(a, b):                         # sign of a + b√2, a, b rational
    Q = lcm(a.denominator, b.denominator)
    A, B = int(a * Q), int(b * Q)
    return sgn_b_sqrt2_minus_c(B, -A)
def floor_q2(a, b):                     # floor of a + b√2
    k = floor(a + (isqrt(2 * int(b * b * 10**12 // 1)) / 10**6 if b >= 0 else -isqrt(2 * int(b * b * 10**12 // 1)) / 10**6))
    for kk in (k - 2, k - 1, k, k + 1, k + 2):
        if sign(a - kk, b) >= 0 and sign(a - kk - 1, b) < 0: return kk
    raise RuntimeError
def clear(a, b, n):                     # fract(a + b√2) in [1/n, 1 − 1/n]
    k = floor_q2(a, b)
    return sign(a - k - F(1, n), b) >= 0 and sign(a - k - 1 + F(1, n), b) <= 0
def run(n, trials, seed, Lmax=10):
    rng = random.Random(seed); gaps = Counter(); notfound = 0; worst = None; tot = 0
    for _ in range(trials):
        rd = [(F(1), F(0))]
        for j in range(n - 2):
            a = F(rng.randint(1, 40)); b = F(rng.randint(-300, 300), 1000) if rng.random() < 0.8 else F(0)
            rd.append((a, b))
        if rng.random() < 0.3: rd[-1] = (F(n * rng.randint(1, 4)), F(0))
        vals = {(x, y) for x, y in rd}
        if len(vals) != n - 1 or any(sign(x, y) <= 0 for x, y in rd): continue
        if all(y == 0 for _, y in rd): continue
        tot += 1
        smax = max(x + abs(y) * 2 for x, y in rd)
        dead = lambda L: any(y == 0 and (x / (n * L)).denominator == 1 for x, y in rd)
        Llive = next(L for L in range(1, 1000) if not dead(L))
        found = None
        for L in range(1, Lmax + 1):
            P = int(n * L * (smax + 2) * 3)
            for p in range(1, P + 1):
                u = F(p, n * L)
                if all(clear(x * u, y * u, n) for x, y in rd): found = L; break
            if found: break
        if found is None: notfound += 1; continue
        g = found - Llive; gaps[g] += 1
        if worst is None or g > worst[0]: worst = (g, [f'{x}+{y}√2' for x, y in rd], Llive, found)
    return tot, gaps, notfound, worst
if __name__ == '__main__':
    for n, trials in ((5, 800), (8, 400)):
        tot, gaps, nf, worst = run(n, trials, 100 + n)
        print(f'n={n}: {tot} runners with irrational readings; gap (lonely − first live): {dict(sorted(gaps.items()))}; '
              f'no lonely instant within the search bound up to lattice 10: {nf}')
        print(f'   largest gap {worst[0]} at readings {worst[1]} (first live {worst[2]}, lonely at {worst[3]})')
