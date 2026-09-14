"""n=5 relaxed chains as linear programs.  Periods u_b >= u_c >= u_d > 0, all <= 1 (nearest period 1).  A relaxed chain
is a word with laps; t_0 = 1/5; t_j = (Q_j + 1/5) u_{w_j}; handoff j: (Q_j - 1/5) u_{w_j} <= t_{j-1} <= t_j; nearest clear
before the last step: t_j <= 4/5.  (Strict inequalities imposed with margin EPS: BSM treats zone boundaries as clear.)  For each word/lap sequence
maximise t_N by LP; depth-first over words with laps <= LMAX and length <= DMAX.  A relaxed chain may take any runner in
the way, not only the latest opening, so its supremum bounds the true chain's."""
import sys, itertools, time
import numpy as np
from scipy.optimize import linprog
h = 0.2
EPS = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-7
IDX = {'b': 0, 'c': 1, 'd': 2}
LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 8
def lp(word, laps, maximise_last=True):
    # variables u_b, u_c, u_d
    A = []; bnd = []
    # ordering and range
    A.append([-1, 1, 0]); bnd.append(0)      # u_c <= u_b
    A.append([0, -1, 1]); bnd.append(0)      # u_d <= u_c
    A.append([1, 0, 0]); bnd.append(1)       # u_b <= 1
    def tvec(j):
        if j == 0: return np.zeros(3), h
        v = np.zeros(3); v[IDX[word[j - 1]]] = laps[j - 1] + h; return v, 0.0
    N = len(word)
    for j in range(1, N + 1):
        x = IDX[word[j - 1]]; Q = laps[j - 1]
        tv, tc = tvec(j - 1)
        # (Q - h) u_x - t_{j-1} <= 0
        row = np.zeros(3); row[x] = Q - h; row -= tv; A.append(list(row)); bnd.append(tc - EPS)
        # t_{j-1} - (Q + h) u_x <= 0
        row = tv.copy(); row[x] -= Q + h; A.append(list(row)); bnd.append(-tc - EPS)
        if j < N:
            row = np.zeros(3); row[x] = Q + h; A.append(list(row)); bnd.append(0.8)
    c = np.zeros(3)
    if N: c[IDX[word[-1]]] = -(laps[-1] + h)
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(bnd), bounds=[(1e-9, 1)] * 3, method='highs')
    if res.status != 0: return None
    return -res.fun if N else h, res.x
best = (0, None); nodes = 0; t0 = time.time()
bylap = {}; bylen = {}
top = []
def dfs(word, laps):
    global best, nodes
    nodes += 1
    r = lp(word, laps)
    if r is None: return
    val, u = r
    if val > best[0] + 1e-12: best = (val, (''.join(word), list(laps), [round(x, 5) for x in u]))
    top.append((val, ''.join(word), tuple(laps)))
    if laps:
        ml = max(laps); bylap[ml] = max(bylap.get(ml, 0), val); bylen[len(laps)] = max(bylen.get(len(laps), 0), val)
    if val > 0.8 - 1e-12 and len(word) > 0:
        pass  # nearest would be at its window edge; the LP already forbids earlier iterates past 4/5
    if len(word) >= DMAX: return
    for y in 'bcd':
        if word and y == word[-1]: continue
        for Q in range(1, LMAX + 1):
            dfs(word + [y], laps + [Q])
dfs([], [])
top.sort(reverse=True)
print('largest reading by the largest lap in the chain:', {k: round(5 * v, 5) for k, v in sorted(bylap.items())})
print('largest reading by chain length:', {k: round(5 * v, 5) for k, v in sorted(bylen.items())})
print(f'LMAX={LMAX} DMAX={DMAX} EPS={EPS}: LP nodes {nodes}, {time.time()-t0:.1f}s')
print(f'supremum of t_N over relaxed chains: {best[0]:.6f}  (nearest reading {5*best[0]:.6f})  at {best[1]}')
seen = set(); k = 0
for v, w, l in top:
    if (w, l) in seen: continue
    seen.add((w, l)); print(f'   reading {5*v:.5f}  word {w}  laps {l}'); k += 1
    if k >= 12: break
