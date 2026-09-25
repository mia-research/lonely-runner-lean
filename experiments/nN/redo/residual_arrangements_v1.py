"""REDO item 4 (supersedes eight_residual_count_v6, ladder_vs_fields_v1, ladder_live_steps_v1, which
enumerated difference sets): the case-list residual and the ladder, per runner of every arrangement.

Every arrangement of 8 distinct speeds in [1,B], gcd of differences 1, EVERY runner.  For each runner's
readings (when there are seven distinct ones -- collisions are handled by order seven, as in the case
list): membership of the session-start residual (v1 fields) and of EightResidual (v5 fields + the
resolution field D <= 64); the ladder's least clearing resolution D* and live steps past L_0; the
cascade tier.  Exact integer band tests.
"""
import sys, time
from itertools import combinations
from math import gcd
from functools import reduce
from collections import Counter
from multiprocessing import Pool
B = int(sys.argv[1]) if len(sys.argv) > 1 else 24
src = open('../eight_residual_count_v5.py').read()
exec(src[:src.index("t0 = time.time()")].replace("N = int(sys.argv[1]) if len(sys.argv) > 1 else 30", ""))
def clears(S, D, a): return all(D <= d * a % (8 * D) <= 7 * D for d in S)
def v1_residual(S):
    if not any(d % 2 for d in S): return False
    if not all(any(d % q == 0 for d in S) for q in (5, 6, 7, 8)): return False
    if not max(S) > 7 * min(S): return False
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: return False
    if any(free_flank8(S, e) for e in S if e % 8 == 0): return False
    if shifted(S): return False
    srt = sorted(S)
    if srt[-1] > 7 * srt[-2]: return False
    return not (first_lap(S) or minus_seven(S))
def v5_plus(S):
    if reduce(gcd, S) > 1: return False
    if has_rational_opening(S) or has_thirds(S) or has_fifths(S): return False
    if has_N(S, 6) or has_N(S, 7) or has_N(S, 9): return False
    return not any(clears(S, D, 8 * j + 1) for D in range(1, 65) for j in range(D))
def ladder(S):
    D = 1; L0 = None; k = 0
    while True:
        if not any(d % (8 * D) == 0 for d in S):
            if L0 is None: L0 = D
            if any(clears(S, D, 8 * j + 1) for j in range(D)): return D, k
            k += 1
        D += 1
def work(first):
    c = Counter(); Ds = Counter(); ks = Counter()
    for rest in combinations(range(first + 1, B + 1), 7):
        V = (first,) + rest
        if reduce(gcd, [v - first for v in rest]) != 1: continue
        for k in range(8):
            S = tuple(sorted({abs(v - V[k]) for v in V if v != V[k]}))
            c['runners'] += 1
            if len(S) < 7: c['collided readings (order seven)'] += 1; continue
            D, st = ladder(S); Ds[D] += 1; ks[st] += 1
            if v1_residual(S):
                c['in session-start residual (v1)'] += 1
                if v5_plus(S): c['in EightResidual incl. resolution field'] += 1
    return c, Ds, ks
if __name__ == "__main__":
    t0 = time.time()
    with Pool(8) as p: parts = p.map(work, range(1, B - 6))
    c = sum((x[0] for x in parts), Counter()); Ds = sum((x[1] for x in parts), Counter()); ks = sum((x[2] for x in parts), Counter())
    print(f"arrangements in [1,{B}], every runner: {dict(c)}  ({time.time() - t0:.0f}s)")
    print(f"   ladder, least clearing resolution D* per runner: max {max(Ds)}, {sorted(Ds.items())}")
    print(f"   ladder, live steps past L_0: max {max(ks)}, {sorted(ks.items())}")
