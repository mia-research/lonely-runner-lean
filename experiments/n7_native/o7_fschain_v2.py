#!/usr/bin/env python3
"""Provable first-stretch chain with the CLUSTER STEP (EXACT Fractions, formula-only, worst-case window positions).
solve(R, l, g, need): runners R (ascending) processed from a window of length l, band [g, 1-g] (g = 1/7 at top level),
ending with a window of length >= need (need = 0: an instant).  Moves on a prefix B of R:
  fold u:     window (1-2g)/u if l >= (2-2g)/u (full stretch), else (l u - 2g)/(2u)        [full_stretch_in, fold]
              last runner, need = 0: success iff l >= 2g/u                                 [hit_in]
  union B:    window w if sum_d (2g L + d L w + 2g w + d w^2 + 4g/d + 2w) < L, L = l - w    [gap_union, band g]
  cluster B:  B = b + e (offsets e > 0, c = max e), window w for B needs offsets in shifted bands shrunk by
              delta = (b + c) w / 2 for a time 1/b: solve(e, l, g + delta, 1/b)               [cluster_window]
Candidate windows w: a geometric grid, each checked exactly.  Coverage on v6 > 100 v1 by family; residue examples."""
import math, random, sys
from fractions import Fraction as Fr
from collections import Counter
from o7_fschain_v1 import step as _unused  # noqa
W_GRID = [Fr(1, 2 ** k) for k in range(1, 40)]
def fold_win(l, u, g):
    if l >= (2 - 2 * g) / u: return (1 - 2 * g) / u
    x = (l * u - 2 * g) / (2 * u)
    return x if x > 0 else None
def union_ok(B, l, g, w):
    L = l - w
    if L <= 0: return False
    s = sum(2 * g * L + d * L * w + 2 * g * w + d * w * w + 4 * g / d + 2 * w for d in B)
    return s < L
def solve(R, l, g, need, depth=0):
    if g >= Fr(1, 2): return False
    if not R: return l >= need
    n = len(R)
    # fold the first runner
    u = R[0]
    if n == 1 and need == 0:
        if l >= 2 * g / u: return True
    else:
        lw = fold_win(l, u, g)
        if lw is not None and solve(R[1:], lw, g, need, depth): return True
    for k in range(2, n + 1):
        B, rest = R[:k], R[k:]
        targets = [need] if not rest else [w * l for w in W_GRID]
        for w in targets:
            if w > l: continue
            if not rest and w < need: continue
            ok_union = k <= 3 and union_ok(B, l, g, w)
            ok_cluster = False
            if not ok_union and depth < 4:
                b = B[0]; e = tuple(x - b for x in B[1:]); c = max(e)
                delta = (b + c) * w / 2
                ok_cluster = solve(e, l, g + delta, Fr(1, b), depth + 1)
            if ok_union or ok_cluster:
                if not rest: return True
                if solve(rest, w, g, need, depth): return True
                break        # larger w already failed downstream? keep trying smaller w only if this w worked
    return False
def fs_chain(P):
    return solve(tuple(P[1:]), Fr(5, 7 * P[0]), Fr(1, 7), Fr(0))
if __name__ == "__main__":
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 4)
    res = Counter(); bad = {}
    def test(name, P):
        if len(set(P)) < 6 or list(P) != sorted(P) or math.gcd(*P) != 1 or P[5] <= 100 * P[0]: return
        ok = fs_chain(P); res[(name, ok)] += 1
        if not ok: bad.setdefault(name, []).append(P)
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    for _ in range(N):
        v1 = rnd.randint(1, 20); top = v1 * rnd.uniform(101, 10**5)
        xs = sorted(math.exp(rnd.uniform(0, math.log(top / v1))) * v1 for _ in range(4))
        test("loguniform", (v1, *[int(x) + 1 + i for i, x in enumerate(xs)], int(top)))
    for _ in range(N):
        v1 = rnd.randint(1, 20); v6 = rnd.randint(101 * v1, 3000 * v1)
        test("uniform", (v1, *sorted(rnd.sample(range(v1 + 1, v6), 4)), v6))
    for v1 in range(1, 15):
        for n in (150, 400, 1000, 5000):
            for d in (1, 2, 5, 13):
                test("runs", (v1, n, n + d, n + 2 * d, n + 3 * d, n + 4 * d))
    print("chain + cluster step, coverage on v6 > 100 v1:", sorted(res.items()))
    for k, l in bad.items(): print(f"   {k} not closed ({len(l)}), e.g.:", l[:6])
