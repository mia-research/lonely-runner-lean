#!/usr/bin/env python3
"""Slow-runner lemma, observation (EXACT integers). For the fast four Q = (v2, v3, v4, v5) let G(Q) be the least length
such that every time interval of length G contains a window of length w = 3/(28 v5) on which all of Q are in band
[1/7, 6/7].  With the good lonely intervals J_i = [L_i, U_i] of Q (length >= w, cyclic over one period [0, 1)):
   G(Q) = max_i (L_{i+1} - U_i) + 2w        (worst start just after J_i stops fitting a window).
Slow lemma: runner 1's band stretches have length 5/(7 v1); if 5/(7 v1) >= G(Q) a stretch contains a full G-interval,
hence a Q-window, with runner 1 in band throughout: kappa(v1, Q) >= 3/28.  So (v1, Q) closes when v1 G(Q) <= 5/7.
Scale-free: h(Q) = v2 G(Q); closes when v1/v2 <= 5/(7 h(Q)).
Time is scaled by N = 28 lcm(Q): edges (7m+e)/(7v) -> (7m+e) 4 lcm/v, w -> 3 lcm/v5.  Reports sup h, maximisers, and
for prefixes P = (v1, Q) <= H the share closed and the smallest v1/v5 and v1/v2 among those not closed."""
import math, sys
from fractions import Fraction as Fr
from itertools import combinations
from multiprocessing import Pool
from o7_exact import lcm, inter
def G_scaled(Q):
    M = lcm(Q); N = 28 * M
    cur = [((7 * m + 1) * 4 * M // Q[0], (7 * m + 6) * 4 * M // Q[0]) for m in range(Q[0])]
    for v in Q[1:]:
        cur = inter(cur, [((7 * m + 1) * 4 * M // v, (7 * m + 6) * 4 * M // v) for m in range(v)])
    w = 3 * M // Q[-1]
    good = [(L, U) for L, U in cur if U - L >= w]
    if not good: return None, N
    gaps = [good[(i + 1) % len(good)][0] + (N if i + 1 == len(good) else 0) - good[i][1] for i in range(len(good))]
    return max(gaps) + 2 * w, N
def work(args):
    v2, H = args; out = []
    for rest in combinations(range(v2 + 1, H + 1), 3):
        Q = (v2,) + rest; G, N = G_scaled(Q)
        out.append((Q, G, N))
    return out
if __name__ == "__main__":
    H = int(sys.argv[1])
    with Pool(10) as pool: res = [x for r in pool.map(work, [(v2, H) for v2 in range(2, H - 2)], chunksize=1) for x in r]
    none = [Q for Q, G, N in res if G is None]
    hs = sorted(((Fr(Q[0] * G, N), Q) for Q, G, N in res if G is not None), reverse=True)
    print(f"exact, fast fours Q <= {H}: {len(res)}; with no 3/28 window: {len(none)} {none[:10]}")
    print(f"   sup h = v2 G(Q) = {hs[0][0]} = {float(hs[0][0]):.4f} at {hs[0][1]}; 15 largest:",
          [(str(h), Q) for h, Q in hs[:15]])
    Gd = {Q: (G, N) for Q, G, N in res}
    closed = notc = 0; minx15 = minx12 = None
    for Q, (G, N) in Gd.items():
        for v1 in range(1, Q[0]):
            if math.gcd(v1, *Q) != 1: continue
            if G is not None and 7 * v1 * G <= 5 * N: closed += 1
            else:
                notc += 1
                r15, r12 = Fr(v1, Q[-1]), Fr(v1, Q[0])
                if minx15 is None or r15 < minx15[0]: minx15 = (r15, (v1,) + Q)
                if minx12 is None or r12 < minx12[0]: minx12 = (r12, (v1,) + Q)
    print(f"   primitive prefixes (v1, Q) <= {H}: closed by the slow lemma {closed}, not closed {notc} "
          f"({closed / (closed + notc):.2%} closed)")
    print(f"   not closed: smallest v1/v5 = {minx15[0]} at {minx15[1]}; smallest v1/v2 = {minx12[0]} at {minx12[1]}")
