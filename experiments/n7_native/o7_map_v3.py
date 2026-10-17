#!/usr/bin/env python3
"""Order seven phase-1 map, extended range, parallel over (v1, v2). EXACT integer arithmetic (o7_exact). Same window types as o7_map_v1 (T4, T5, T6,
TIGHT), plus exact fractions for every T6 and TIGHT set (longest lonely length).
  python3 o7_map_v2.py map H     full classification of primitive sets <= H
  python3 o7_map_v2.py tight H   tight / not-lonely search only (full six-runner intersection), primitive <= H
Per class: counts, handled pair for T4, folded runner for T5, longest AP and prefix gcd for T5/T6."""
import math, sys, time
from itertools import combinations
from collections import Counter
from fractions import Fraction as Fr
from multiprocessing import Pool
from o7_exact import classify, block, lcm
def longest_ap(S):
    s = set(S); best = 2
    for a, b in combinations(S, 2):
        d = b - a; n = 2
        while b + (n - 1) * d in s: n += 1
        best = max(best, n)
    return best
def exact_max_len(S):
    def bf(v): return [(Fr(7 * m + 1, 7 * v), Fr(7 * m + 6, 7 * v)) for m in range(v)]
    cur = bf(S[0])
    for v in S[1:]:
        B = bf(v); i = j = 0; out = []
        while i < len(cur) and j < len(B):
            lo, hi = max(cur[i][0], B[j][0]), min(cur[i][1], B[j][1])
            if hi >= lo: out.append((lo, hi))
            if cur[i][1] < B[j][1]: i += 1
            else: j += 1
        cur = out
    return max((hi - lo for lo, hi in cur), default=None)
def sets_for(v1, v2, H):
    for rest in combinations(range(v2 + 1, H + 1), 4):
        S = (v1, v2) + rest
        if math.gcd(*S) == 1: yield S
def work_map(args):
    v1, v2, H = args
    c = Counter(); pat = Counter(); fold = Counter(); ap = Counter(); gp = Counter(); t6 = []; tight = []; bad = []
    for S in sets_for(v1, v2, H):
        k, p = classify(S); c[k] += 1
        if k == "T4": pat[p] += 1
        if k == "T5": fold[p[0]] += 1
        if k in ("T5", "T6", "TIGHT"):
            ap[(k, min(longest_ap(S), 5))] += 1
            gp[(k, "g5>1" if math.gcd(*S[:5]) > 1 else "g4>1" if math.gcd(*S[:4]) > 1 else "coprime")] += 1
        if k == "T6": t6.append(S)
        if k == "TIGHT": tight.append(S)
        if k == "NOT LONELY": bad.append(S)
    return c, pat, fold, ap, gp, t6, tight, bad
def work_tight(args):
    v1, v2, H = args
    n = 0; tight = []; bad = []
    for S in sets_for(v1, v2, H):
        n += 1
        M = lcm(S)
        if not block(S, range(6), M):
            (tight if block(S, range(6), M, strict=False) else bad).append(S)
    return n, tight, bad
if __name__ == "__main__":
    mode, H = sys.argv[1], int(sys.argv[2]); t0 = time.time()
    jobs = sorted(((v1, v2, H) for v1 in range(1, H - 4) for v2 in range(v1 + 1, H - 3)),
                  key=lambda j: -math.comb(H - j[1], 4))
    with Pool(10) as pool:
        res = pool.map(work_map if mode == "map" else work_tight, jobs, chunksize=1)
    if mode == "map":
        c = Counter(); pat = Counter(); fold = Counter(); ap = Counter(); gp = Counter(); t6 = []; tight = []; bad = []
        for r in res:
            c += r[0]; pat += r[1]; fold += r[2]; ap += r[3]; gp += r[4]; t6 += r[5]; tight += r[6]; bad += r[7]
        print(f"== primitive order-seven sets <= {H}: {sum(c.values())} sets: {dict(c)}")
        print("   T4 handled pair:", pat.most_common(8))
        print("   T5 folded runner:", sorted(fold.items()))
        print("   longest AP (capped 5) by class:", sorted(ap.items()))
        print("   prefix gcd by class:", sorted(gp.items()))
        print(f"   NOT LONELY ({len(bad)}):", sorted(bad))
        for S in sorted(tight): print(f"   TIGHT {S}: exact longest length {exact_max_len(S)}")
        for S in sorted(t6): print(f"   T6 {S}: exact longest length {exact_max_len(S)}  longest AP {longest_ap(S)}")
    else:
        n = sum(r[0] for r in res); tight = sorted(s for r in res for s in r[1]); bad = sorted(s for r in res for s in r[2])
        print(f"== tight search, primitive order-seven sets <= {H}: {n} sets")
        print(f"   NOT LONELY ({len(bad)}):", bad)
        for S in tight: print(f"   TIGHT {S}: exact longest length {exact_max_len(S)}")
    print(f"   elapsed {time.time() - t0:.0f} s")
