# Task 1(a): exhaustive K6 maps over six-sets {1}+five values from a grid. usage: k6map_task1a_v1.py MODE
import sys, itertools, time
from collections import Counter
from k6map_lib_v1 import *
mode = sys.argv[1]
if mode == 'int24': vals = [F(k) for k in range(2, 25)]
elif mode == 'half16': vals = [F(k, 2) for k in range(3, 33)]
elif mode == 'third12': vals = [F(k, 3) for k in range(4, 37)]
elif mode == 'mix8': vals = sorted(set([F(k, 2) for k in range(3, 17)] + [F(k, 3) for k in range(4, 25)]))
else: raise SystemExit
t0 = time.time(); N = 0
ncomp = Counter(); npt = Counter(); minL = None; minR = []; emptyK = 0; finiteK = 0; maxL = None
sig = Counter(); tot_min = None
prog_sig = None
for combo in itertools.combinations(vals, 5):
    rho = [F(1)] + list(combo); N += 1
    W = K6(rho)
    n = len(W); pts = sum(1 for a, b in W if a == b)
    ncomp[n] += 1; npt[(n, pts)] += 1
    if n == 0: emptyK += 1
    elif pts == n: finiteK += 1
    L = max((b - a for a, b in W), default=F(0))
    ratio = L * 7 * rho[5] / 2
    if len(minR) < 12 or ratio <= minR[-1][0]:
        minR.append((ratio, tuple(rho), L, W)); minR.sort(key=lambda x: x[0]); minR = minR[:12]
    tl = sum((b - a for a, b in W), F(0))
    if tot_min is None or tl < tot_min[0]: tot_min = (tl, tuple(rho))
    if maxL is None or L > maxL[0]: maxL = (L, tuple(rho))
print(f"mode {mode}: grid values {len(vals)}, six-sets {N}, time {time.time()-t0:.1f}s")
print("K6 empty:", emptyK, "| K6 nonempty and finite (all components one-point):", finiteK)
print("number of components -> count of six-sets:", sorted(ncomp.items()))
print("(components, one-point windows) -> count:", sorted(npt.items()))
print("least total length of K6:", tot_min[0], float(tot_min[0]), [str(x) for x in tot_min[1]])
print("greatest longest component:", maxL[0], float(maxL[0]), [str(x) for x in maxL[1]])
print("smallest ratio L/(2/(7 rho_6)) (L longest component):")
for r, rho, L, W in minR:
    print("  ratio %s = %.6f  rho=%s  L=%s  comps=%d pts=%d" % (r, float(r), [str(x) for x in rho], L, len(W), sum(1 for a, b in W if a == b)))
print("progression 1..6 for reference:", [(str(a), str(b)) for a, b in K6([F(i) for i in range(1, 7)])])
