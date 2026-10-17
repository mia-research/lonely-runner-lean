#!/usr/bin/env python3
"""Exact cross-check of the abstraction in seven_abstract_v1.py against direct arithmetic: for random units x mod 7^a
(a = 3..9), the band status of x * c (1 + 7^(a-2) s) mod 7^a equals the abstract rule
cell = (c T + floor(c y) + s c rho) mod 49 in [7, 41], with T, Farey cell of y, rho read off x."""
import random
from fractions import Fraction as Fr
exec(open("seven_abstract_v1.py").read().split("units49 =")[0].replace("CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6", "CMAX = 6"))
def farey_index(y):
    for i, (l, r) in enumerate(cells):
        if l < y < r: return i
    raise ValueError("Farey point")
rng = random.Random(11); bad = 0; n = 0
for a in range(3, 10):
    N = 7 ** a
    for _ in range(400):
        x = 0
        while x % 7 == 0: x = rng.randrange(1, N)
        T, y, rho = x // 7 ** (a - 2), Fr(x % 7 ** (a - 2), 7 ** (a - 2)), x % 49
        m = mask(T, FL[farey_index(y)], rho)
        for bit, (c, s) in enumerate(strategies):
            v = x * c * (1 + 7 ** (a - 2) * s) % N
            direct = N // 7 <= v <= 6 * N // 7
            n += 1; bad += direct != bool(m >> bit & 1)
print("checks", n, "mismatches", bad)
