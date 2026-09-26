"""WP3: the longest time a block of six runners can keep the subject's slot occupied.  Exact, Boundary Set Method.
Block F = six positive whole-number readings (the other runners' differences from the subject).  Zones: runner d is in
the way on the open intervals ((m - 1/8)/d, (m + 1/8)/d).  Over one period 1/gcd(F) the union of the zones splits into
components; TOUCHING open zones do not merge (the touching point is clear).  L(F) = the longest component, excluding the
start-up stretch that begins at t = 0 (every runner starts on the subject).
Reported in three scales: L * min(F) (laps of the block's slowest), L * spread (spread = max F - min F), L * delta_min
(delta_min = smallest difference between two block runners).  Shapes: compact trains N + E, evenly spaced blocks
k d + dev, random blocks; N varied to see which scale keeps L bounded."""
import random
from fractions import Fraction as F
from math import gcd, floor
from functools import reduce
def longest_blocked(Fs):
    g = reduce(gcd, Fs); P = F(1, g)
    zones = []
    for d in Fs:
        for m in range(0, d // g + 2):
            a, b = F(8 * m - 1, 8 * d), F(8 * m + 1, 8 * d)
            if b > 0 and a < P: zones.append((a, b))
    zones.sort()
    best = F(0); cur_a, cur_b = zones[0]
    for a, b in zones[1:]:
        if a < cur_b:                      # strictly overlapping open intervals merge; touching ones do not
            cur_b = max(cur_b, b)
        else:
            if cur_a > 0: best = max(best, cur_b - cur_a)
            cur_a, cur_b = a, b
    if cur_a > 0: best = max(best, cur_b - cur_a)
    return best
def scales(Fs):
    L = longest_blocked(Fs); s = sorted(Fs)
    spread = s[-1] - s[0]; dmin = min(b - a for a, b in zip(s, s[1:]))
    return L, L * s[0], L * spread, L * dmin
rnd = random.Random(3)
def report(name, blocks):
    rows = [scales(b) for b in blocks]
    mx = [max(r[i] for r in rows) for i in (1, 2, 3)]
    print(f"  {name:44s} n={len(rows):3d}  max L*min(F) {float(mx[0]):9.3f}   max L*spread {float(mx[1]):8.3f}   max L*delta_min {float(mx[2]):7.3f}")
if __name__ == "__main__":
    print("longest blocked stretch L of a six-runner block, in three scales (max over the family)")
    for N in (100, 1000, 10000):
        report(f"compact train N+{{0..5}}*d, d in 3..20, N={N}", [[N + k * d for k in range(6)] for d in range(3, 21)])
    for N in (100, 1000, 10000):
        report(f"compact train N+random offsets<=60, N={N}", [[N + e for e in sorted(rnd.sample(range(0, 61), 6))] for _ in range(40)])
    for d in (10, 50, 200):
        report(f"evenly spaced k*d+dev (k=1..6), d={d}", [[k * d + rnd.randint(-d // 5, d // 5) for k in range(1, 7)] for _ in range(40)])
    for top in (100, 1000):
        report(f"random 6-sets in [1,{top}]", [sorted(rnd.sample(range(1, top + 1), 6)) for _ in range(60)])
