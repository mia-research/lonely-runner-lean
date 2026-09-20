"""T1 re-read: neighbours by AP slot (round(speed) mod 8) instead of fixed label; ties kept as sets."""
from fractions import Fraction as F
from math import floor
from collections import Counter
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from scale_jump_battery_v1 import least_L, sides
def slot(v): return floor(v + F(1, 2)) % 8
c = Counter(); bad = []
for s in [F(8)] + [F(x, 100) for x in (850, 890, 899, 900, 901, 910, 950)] + [F(x, 2) for x in range(20, 34)]:
    V = [F(j + 1) for j in range(7)] + [s]
    for i in range(8):
        L, u, m = least_L(V, i)
        if not (L == 1 and m == 1): c[f"scale {L}, d_min {m} (not checked)"] += 1; continue
        t = u / m; b, a = sides(V, i, t); r = int(8 * u) % 8
        cc = 1 if r in (1, 7) else 3
        want = {(slot(V[i]) - cc) % 8, (slot(V[i]) + cc) % 8}
        got_b = {slot(V[j]) for j in b}; got_a = {slot(V[j]) for j in a}
        ok = got_b | got_a == want and len(got_b) == len(got_a) == 1
        c[("scale 1, d_min 1: neighbours are the AP event's slots", ok)] += 1
        if not ok: bad.append((float(s), f"runner {V[i]}", f"t={t}", sorted(float(V[j]) for j in b), sorted(float(V[j]) for j in a)))
print(dict(c))
for x in bad: print("  not:", x)
