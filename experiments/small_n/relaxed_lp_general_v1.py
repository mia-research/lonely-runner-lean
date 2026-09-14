"""Relaxed chains as LPs at general n.  Runners: nearest a (period 1, fixed) and n-2 others with periods
1 >= u_1 >= ... >= u_{n-2} > 0.  Word over all n-1 runners (the nearest may set a move once it is in the way);
t_0 = 1/n; t_j = (Q_j + 1/n) u_{w_j}; handoff: (Q_j - 1/n) u_{w_j} + EPS <= t_{j-1} <= t_j - EPS.
Depth-first over words (no immediate repeats) with laps <= LMAX and length <= DMAX; supremum of n * t_N (nearest
reading).  Usage: n LMAX DMAX [EPS]"""
import sys, time
import numpy as np
from scipy.optimize import linprog
n = int(sys.argv[1]); LMAX = int(sys.argv[2]); DMAX = int(sys.argv[3])
EPS = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-7
h = 1.0 / n; R = n - 2   # other runners 0..R-1 (slowest first); runner R = nearest (period 1)
def solve(word, laps):
    A = []; b = []
    for i in range(R - 1):
        row = [0.0] * R; row[i] = -1; row[i + 1] = 1; A.append(row); b.append(0.0)   # u_{i+1} <= u_i
    row = [0.0] * R; row[0] = 1; A.append(row); b.append(1.0)                        # u_0 <= 1
    def tv(j):
        if j == 0: return [0.0] * R, h
        x = word[j - 1]; Q = laps[j - 1]
        if x == R: return [0.0] * R, Q + h
        v = [0.0] * R; v[x] = Q + h; return v, 0.0
    for j in range(1, len(word) + 1):
        x = word[j - 1]; Q = laps[j - 1]
        pv, pc = tv(j - 1); cv, cc = tv(j)
        # zone start <= t_{j-1} - EPS :  (Q - h) u_x - t_{j-1} <= -EPS
        row = [cv_i * (Q - h) / (Q + h) - pv_i for cv_i, pv_i in zip(cv, pv)]
        A.append(row); b.append(pc - cc * (Q - h) / (Q + h) - EPS)
        # t_{j-1} <= t_j - EPS
        row = [pv_i - cv_i for pv_i, cv_i in zip(pv, cv)]; A.append(row); b.append(cc - pc - EPS)
    if not word: return h
    cv, cc = tv(len(word))
    res = linprog([-c for c in cv], A_ub=np.array(A), b_ub=np.array(b), bounds=[(1e-9, 1)] * R, method='highs')
    if res.status != 0: return None
    return -res.fun + cc
best = (0, None); nodes = 0; t0 = time.time(); near_used = 0
def dfs(word, laps):
    global best, nodes, near_used
    nodes += 1
    v = solve(word, laps)
    if v is None: return
    if v > best[0] + 1e-12: best = (v, (list(word), list(laps)))
    if R in word: near_used = max(near_used, n * v)
    if len(word) >= DMAX: return
    for y in range(R + 1):
        if word and y == word[-1]: continue
        for Q in range(1, LMAX + 1):
            dfs(word + [y], laps + [Q])
dfs([], [])
names = [chr(ord('b') + i) for i in range(R)] + ['a']
w, l = best[1]
print(f'n={n} LMAX={LMAX} DMAX={DMAX} EPS={EPS}: LP nodes {nodes}, {time.time()-t0:.1f}s')
print(f'supremum nearest reading {n*best[0]:.6f} at word {"".join(names[x] for x in w)} laps {l}')
print(f'largest reading among chains in which the nearest runner sets a move: {near_used:.6f}')
