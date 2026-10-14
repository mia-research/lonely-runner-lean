from fractions import Fraction as F
from math import ceil
from scale_jump_r8_v1 import least_L, dist, E
print("r8 near a wrap onto r1's slot: r8 = 1 + 8q + delta.  r1's least lattice, its instant, and the lap-law prediction")
print("lap law (L = 1): t = least odd eighth with every runner clear; for small delta that is the least odd eighth with |delta|*t >= 1/8 (mod 1)")
for q in (1, 2, 3, 4):
    for d in (F(-1,10), F(-1,100), F(0), F(1,100), F(1,10)):
        V = [F(j + 1) for j in range(7)] + [F(1 + 8*q) + d]
        L, m, u = least_L(V, 0, Lmax=12)
        pred = None
        if d != 0:
            a = 1
            while not (dist(abs(d) * F(a, 8)) >= E): a += 2
            pred = F(a, 8)
        dead = [s for s in range(1, 13) if (8*q) % (8*s) == 0] if d == 0 else []
        print(f"  q={q} delta={str(d):>6}: r1 least L={L} at u={str(u):>7}   lap-law prediction {pred}   dead scales {dead}")
