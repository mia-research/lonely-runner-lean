#!/usr/bin/env python3
"""Order seven read in cascade order (EXACT residue criteria), primitive six-sets <= HI:
  A  first instant 1/(7 v1): lonely iff every d mod 7 v1 in [v1, 6 v1]             (first move, residue form)
  B  t = 1/7: lonely iff no speed divisible by 7
  C  an opening (7j+1)/(7e) or (7j+6)/(7e) of a 7-divisible flank e is lonely      (cells)
  D  remaining sets: which flank carries a lonely opening (cascade final flank), and features
Counts by first closer in the order A, B, C; lists D (the core)."""
import sys, math
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
def lon(S, e, r):
    m = 7 * e
    return all(e <= (d * r) % m <= 6 * e for d in S)
def closer(S):
    v1 = S[0]
    if all(v1 <= d % (7 * v1) <= 6 * v1 for d in S): return "A"
    if all(d % 7 for d in S): return "B"
    for e in S:
        if e % 7 == 0 and any(lon(S, e, 7 * j + 1) or lon(S, e, 7 * j + 6) for j in range(e)): return "C"
    return "D"
def work(args):
    v1, HI = args; c = Counter(); core = []
    for rest in combinations(range(v1 + 1, HI + 1), 5):
        S = (v1,) + rest
        if math.gcd(*S) != 1: continue
        k = closer(S); c[k] += 1
        if k == "D": core.append(S)
    return c, core
if __name__ == "__main__":
    HI = int(sys.argv[1])
    with Pool(10) as pool: res = pool.map(work, [(v1, HI) for v1 in range(1, HI - 4)], chunksize=1)
    c = Counter(); core = []
    for r in res: c += r[0]; core += r[1]
    print(f"HI={HI}: {sum(c.values())} primitive six-sets; first closer A (1/(7v1)) {c['A']}, B (1/7) {c['B']}, "
          f"C (7-divisible flank cell) {c['C']}, D (core) {c['D']}")
    pos = Counter(tuple(i + 1 for i, d in enumerate(S) if d % 7 == 0) for S in core)
    print("  core: ranks of multiples of 7:", sorted(pos.items()))
    print("  core, first 40:", core[:40])
    open(f"seven_core_v1_{HI}.txt", "w").write("\n".join(map(str, core)) + "\n")
