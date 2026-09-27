"""E136: the 149 band sets to 24 where both AP-scale mirror pairs fail only because edges cross (no capture, interiors
fine).  For each: grid n = round(s), per class the edge readings (A: c n = 1, B: c n = 7) with their lags n/x; the
cascade's landing R*, flank, landing laps, and the landing positions (eighths).  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from ap_pairs_vs_late_v1 import class_status, rnd
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return 8 * T[0] * t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
rows = []
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1] <= 9 * T[0]): continue
    s = [F(d, T[0]) for d in T]
    st = {c: class_status(s, c) for c in (1, 3, 5, 7)}
    if set(st.values()) != {'fails: edges cross'}: continue
    R = cascade(T); n = [rnd(x) for x in s]
    pos = [(x * R) % 8 for x in s]; laps = [int(x * R // 8) for x in s]
    flank = [i for i in range(7) if pos[i] == 1]
    rows.append((T, n, R, flank, laps, pos))
print(len(rows), "sets")
res = Counter(tuple(q % 8 for q in r[1]) for r in rows)
print("grid residues n mod 8 (by rank):"); [print("  %4d  %s" % (v, k)) for k, v in res.most_common(12)]
print("landing R* ranges:", Counter('%.0f-%.0f' % (floor(r[2]), floor(r[2]) + 1) for r in rows))
print("flank rank at landing:", Counter(r[3][0] if r[3] else None for r in rows))
print("landing laps:", Counter(tuple(r[4]) for r in rows).most_common(8))
for T, n, R, fl, laps, pos in rows[:12]:
    print("  ", T, "n", n, "R* = %s = %.4f" % (R, float(R)), "flank", fl, "laps", laps, "pos", [round(float(p), 3) for p in pos])
