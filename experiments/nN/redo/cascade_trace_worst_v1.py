"""The cascade's workings in the longest blocked stretches (owner: the cascade is not a black box).
For the worst blocks of room_vs_kappa_v1, find the longest blocked stretch (exact interval merge), start
the cascade at its beginning, and print every move: the instant (in turns of the slowest reading), the
runners in the way, the one setting the move, and every runner's position in eighths.  Also print the
pairwise DIFFERENCES of the block's readings, to see which arithmetic relation hands the blockage on."""
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
def ndist(x): x = x % 1; return min(x, 1 - x)
def longest_run(Fs):
    g = reduce(gcd, Fs)
    z = sorted((F(8 * k - 1, 8 * d), F(8 * k + 1, 8 * d)) for d in Fs for k in range(0, d // g + 2))
    best = (F(0), None); lo, hi = z[0]
    for a, b in z[1:]:
        if a < hi: hi = max(hi, b)
        else:
            if hi - lo > best[0]: best = (hi - lo, lo)
            lo, hi = a, b
    return best
for Fs in [(23, 26, 42), (12, 15, 23, 37), (7, 8, 11, 17, 25), (10, 13, 16, 19, 29, 35)]:
    L, start = longest_run(Fs); m = min(Fs)
    diffs = sorted({b - a for i, a in enumerate(Fs) for b in Fs[i + 1:]})
    print(f"block {Fs}: longest blocked stretch {float(L * m):.3f} turns of {m}, from t = {start}; pairwise differences {diffs}")
    t = start + F(1, 10**9); n = 0      # just inside the stretch (zones are open)
    while True:
        way = [d for d in Fs if ndist(d * t) < F(1, 8)]
        pos = {d: round(float((d * t) % 1) * 8, 2) for d in Fs}
        if not way:
            print(f"   t = {float(t * m):7.3f} turns: CLEAR; positions (eighths) {pos}"); break
        opens = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        setter = max(way, key=lambda d: opens[d])
        print(f"   t = {float(t * m):7.3f} turns: in the way {way}, setter {setter}; positions (eighths) {pos}")
        t = opens[setter]; n += 1
        if n > 60: break
