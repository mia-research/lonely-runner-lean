#!/usr/bin/env python3
"""Order seven read through flanks and cells (EXACT integers).  For each primitive six-set S <= HI:
  - U = speeds not divisible by 7, M = speeds divisible by 7.
  - If M is empty: t = 1/7 is lonely (every reading (v mod 7)/7 is in [1/7, 6/7]) -- checked.
  - Else: for each flank e in M (E = e/7) and each opening j in 0..e-1 (instant (7j+1)/(7e)), the residue criterion:
    lonely iff e <= d (7j+1) mod 7e <= 6e for all d in S (`clear_at_int_flank_iff_emod` form).
    Records whether some 7-divisible flank has a lonely opening, whether one is a coarse-cell opening (j = u E),
    and the shape (|U|, |M|, rank of the largest-valuation speed).
Exceptions (M nonempty, no lonely opening at any 7-divisible flank) are listed with their cascade final flank."""
import sys, math
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
def v7(x):
    k = 0
    while x % 7 == 0: x //= 7; k += 1
    return k
def lonely_open(S, e, j):
    m = 7 * e; r = 7 * j + 1
    return all(e <= (d * r) % m <= 6 * e for d in S)
def work(args):
    v1, HI = args; c = Counter(); exc = []
    for rest in combinations(range(v1 + 1, HI + 1), 5):
        S = (v1,) + rest
        if math.gcd(*S) != 1: continue
        M = [d for d in S if d % 7 == 0]; U = [d for d in S if d % 7]
        if not M:
            assert all(1 <= (d % 7) <= 6 for d in S); c[("M empty: t=1/7", True)] += 1; continue
        found = coarse = False
        for e in M:
            E = e // 7
            for j in range(e):
                if lonely_open(S, e, j):
                    found = True
                    if j % E == 0: coarse = True
                    break
            if coarse: break
        shape = (len(U), len(M))
        c[("shape", shape, found, coarse)] += 1
        if not found: exc.append(S)
    return c, exc
if __name__ == "__main__":
    HI = int(sys.argv[1])
    with Pool(10) as pool: res = pool.map(work, [(v1, HI) for v1 in range(1, HI - 4)], chunksize=1)
    c = Counter(); exc = []
    for r in res: c += r[0]; exc += r[1]
    print(f"HI={HI}: primitive six-sets {sum(c.values())}")
    print(f"  no speed divisible by 7: {c[('M empty: t=1/7', True)]} (all lonely at t = 1/7)")
    print("  (|U|, |M|): [lonely opening at a 7-divisible flank (of which a coarse cell opening j = uE), none]")
    shapes = sorted({k[1] for k in c if k[0] == 'shape'})
    for sh in shapes:
        yes = sum(v for k, v in c.items() if k[0] == 'shape' and k[1] == sh and k[2])
        co = sum(v for k, v in c.items() if k[0] == 'shape' and k[1] == sh and k[2] and k[3])
        no = sum(v for k, v in c.items() if k[0] == 'shape' and k[1] == sh and not k[2])
        print(f"    {sh}: [{yes} ({co}), {no}]")
    print(f"  exceptions (no lonely opening at any 7-divisible flank): {len(exc)}; first 30:", exc[:30])
    open(f"seven_cells_v1_{HI}_exceptions.txt", "w").write("\n".join(map(str, exc)) + "\n")
