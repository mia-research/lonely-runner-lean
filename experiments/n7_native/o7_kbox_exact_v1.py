#!/usr/bin/env python3
"""Phase 3a: the o7_kbox_v2 box tree in exact rational arithmetic (Fractions), for the slice that contains both
minimisers: x1 in [1/10, 1/5].  Same leaf condition and sevenths splitting; WMIN = 1/1000."""
import sys, time
from fractions import Fraction as Fr
from multiprocessing import Pool
S7, S67 = Fr(1, 7), Fr(6, 7)
def runner_L(a, b, K, T):
    out = []; n = 0
    while True:
        lo = (n + S7) / a; hi = (n + S67) / b - K
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
    cur = runner_L(Fr(1), Fr(1), K, T)
    for a, b in sorted(box, key=lambda z: -z[1]):
        cur = inter(cur, runner_L(a, b, K, T))
        if not cur: return None
    return cur[0][0]
def solve(args):
    box0, K, T, WMIN = args
    stack = [box0]; leaves = 0; fails = []
    while stack:
        box = stack.pop()
        if any(box[i][0] >= box[i + 1][1] for i in range(3)) or box[3][0] >= 1: continue
        if leaf(box, K, T) is not None: leaves += 1; continue
        w = [b - a for a, b in box]; i = max(range(4), key=lambda k: w[k])
        if w[i] < WMIN: fails.append(box); continue
        a, b = box[i]; m = (a + b) / 2
        ks = [Fr(k, 7) for k in range(1, 7) if a < Fr(k, 7) < b]
        if ks: m = min(ks, key=lambda z: abs(z - m))
        for half in ((a, m), (m, b)):
            nb = list(box); nb[i] = half; stack.append(nb)
    return leaves, fails
if __name__ == "__main__":
    Kn, Kd = int(sys.argv[1]), int(sys.argv[2]); K = Fr(Kn, Kd); T = Fr(40); WMIN = Fr(1, 1000); t0 = time.time()
    lo, hi, N = Fr(1, 10), Fr(1, 5), 40
    jobs = [([(lo + (hi - lo) * k / N, lo + (hi - lo) * (k + 1) / N), (lo, Fr(1)), (lo, Fr(1)), (lo, Fr(1))], K, T, WMIN) for k in range(N)]
    with Pool(10) as pool: res = pool.map(solve, jobs, chunksize=1)
    print(f"exact, K = {K}, x1 in [1/10, 1/5], T = 40, WMIN = 1/1000: leaves {sum(r[0] for r in res)}, "
          f"failed {sum(len(r[1]) for r in res)}, elapsed {time.time() - t0:.0f} s")
    for r in res:
        for f in r[1][:3]: print("   fail", [(float(a), float(b)) for a, b in f])
