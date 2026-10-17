#!/usr/bin/env python3
"""Observation only (n = 7, band [1/7, 6/7]).  For each primitive six-set S = (v1 < ... < v6) <= HI, run the cascade
(as six_cascade_observe_v1 at n = 6, MomentIterationN.move) from 1/(7 v1) with exact Fractions: each move goes to the
latest next opening among the runners in the way; its setter is that runner.  Records per set: moves, setter ranks
with laps, final instant T, final flank (the last setter, v1 if no move), the 7-adic valuation of every speed and of
the final flank, and whether the final opening is a cell opening of a 7-divisible flank (j = u E at e = 7E).
Writes seven_cascade_observe_v1.tsv; prints summary tables."""
import sys, math
from itertools import combinations
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
N = 7
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def v7(x):
    k = 0
    while x % 7 == 0: x //= 7; k += 1
    return k
def cascade(S, cap=2000):
    t = F(1, N * S[0]); moves = []
    for _ in range(cap):
        blk = [d for d in S if cd(d * t) < F(1, N)]
        if not blk: return t, moves
        best = None
        for d in blk:
            x = d * t - F(1, N); c = -((-x.numerator) // x.denominator)
            o = (c + F(1, N)) / d
            if best is None or o > best[0]: best = (o, d, c)
        moves.append((S.index(best[1]) + 1, best[2]))
        t = best[0]
    raise RuntimeError(S)
def work(args):
    v1, HI = args; rows = []
    for rest in combinations(range(v1 + 1, HI + 1), 5):
        S = (v1,) + rest
        if math.gcd(*S) != 1: continue
        T, mv = cascade(S)
        fr = mv[-1][0] if mv else 1; e = S[fr - 1]; lap = mv[-1][1] if mv else 0
        vals = tuple(v7(d) for d in S)
        cell = v7(e) >= 1 and lap % (e // 7) == 0 if v7(e) >= 1 else False
        rows.append((S, len(mv), tuple(m[0] for m in mv), tuple(m[1] for m in mv), T, fr, v7(e), vals, cell))
    return rows
if __name__ == "__main__":
    HI = int(sys.argv[1])
    with Pool(10) as pool: res = [r for rr in pool.map(work, [(v1, HI) for v1 in range(1, HI - 4)], chunksize=1) for r in rr]
    with open(f"seven_cascade_observe_v1_{HI}.tsv", "w") as out:
        out.write("set\tmoves\tsetter_ranks\tlaps\tT\tfinal_flank_rank\tv7_final\tv7_speeds\tcell_opening\n")
        for r in res: out.write("\t".join(map(str, r)) + "\n")
    nm = Counter(r[1] for r in res); fr = Counter(r[5] for r in res); v7f = Counter(r[6] for r in res)
    maxv = Counter((max(r[7]) > 0, r[6] > 0) for r in res)
    top7 = Counter((r[7][5] > 0 and sum(x > 0 for x in r[7]) == 1, r[5] == 6, r[8]) for r in res)
    print(f"HI={HI}: primitive six-sets {len(res)}")
    print("  moves:", dict(sorted(nm.items())))
    print("  final flank rank:", dict(sorted(fr.items())))
    print("  7-adic valuation of the final flank:", dict(sorted(v7f.items())))
    print("  (some speed divisible by 7, final flank divisible by 7):", dict(maxv))
    print("  (only v6 divisible by 7, final flank is v6, final opening a cell opening j = uE):", dict(top7))
