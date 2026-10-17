#!/usr/bin/env python3
"""Phase 3a prototype: box tree for kappa >= K over real ratios x = (x1..x4), x_i = v_i/v5, v5 normalised to 1.
Leaf (lap box): a time interval [L, L + K] (time in units 1/v5, L in [0, T]) and laps n_i with, for every x in the box
[a_i, b_i]:  a_i L >= n_i + 1/7  and  b_i (L + K) <= n_i + 6/7  (runner 5: n + 1/7 <= L, L + K <= n + 6/7).
These are the term-wise linear bounds (x_i tau is increasing in x_i and tau, both positive).  The valid L for one runner
form a union of intervals [(n + 1/7)/a_i, (n + 6/7)/b_i - K]; a leaf exists iff the five unions meet in [0, T].
Otherwise split the widest coordinate; boxes with a_i >= b_{i+1} (x not increasing) are dropped; boxes narrower than
WMIN that still fail are recorded as failures.
  python3 o7_kbox_v1.py K_num K_den x1_lo x1_hi T WMIN"""
import sys, time
from fractions import Fraction as Fr
from multiprocessing import Pool
def runner_L(a, b, K, T):
    """valid L in [0, T] for a runner with ratio in [a, b]"""
    out = []; n = int(a * 0)
    n = 0
    while True:
        lo = (n + 1 / 7) / a; hi = (n + 6 / 7) / b - K
        if lo > T: break
        if hi >= lo: out.append((lo, min(hi, T)))
        n += 1
    return out
def inter(A, B):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if hi >= lo: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def leaf(box, K, T):
    cur = runner_L(1.0, 1.0, K, T)
    for a, b in sorted(box, key=lambda z: -z[1]):
        cur = inter(cur, runner_L(a, b, K, T))
        if not cur: return None
    return cur[0][0]
def solve(args):
    box0, K, T, WMIN = args
    stack = [box0]; leaves = 0; fails = []; maxdepth = 0
    while stack:
        box = stack.pop()
        if any(box[i][0] >= box[i + 1][1] for i in range(3)) or box[3][0] >= 1: continue
        if leaf(box, K, T) is not None: leaves += 1; continue
        w = [b - a for a, b in box]; i = max(range(4), key=lambda k: w[k])
        if w[i] < WMIN: fails.append(box); continue
        a, b = box[i]; m = (a + b) / 2
        for half in ((a, m), (m, b)):
            nb = list(box); nb[i] = half; stack.append(nb)
    return leaves, fails
if __name__ == "__main__":
    Kn, Kd, lo, hi, T, WMIN = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6])
    K = Kn / Kd; t0 = time.time(); N = 40
    jobs = [([(lo + (hi - lo) * k / N, lo + (hi - lo) * (k + 1) / N), (lo, 1.0), (lo, 1.0), (lo, 1.0)], K, T, WMIN) for k in range(N)]
    with Pool(10) as pool: res = pool.map(solve, jobs, chunksize=1)
    leaves = sum(r[0] for r in res); fails = [f for r in res for f in r[1]]
    print(f"K = {Kn}/{Kd}, x1 in [{lo}, {hi}], T = {T}, WMIN = {WMIN}: leaves {leaves}, failed boxes {len(fails)}, "
          f"elapsed {time.time() - t0:.0f} s")
    if fails:
        cen = sorted(tuple(round((a + b) / 2, 3) for a, b in f) for f in fails)
        # cluster failure centres to 2 decimals
        from collections import Counter
        cl = Counter(tuple(round(c, 2) for c in x) for x in cen)
        print("   failure clusters (centre rounded to 0.01, count):", cl.most_common(30))
