# E831: LP-guided search over zone-chain types (floats steer only).  From a start, take the greedy zone chain of the current readings (breaks allowed), solve the LP over the readings for that chain type (largest margin t of the link inequalities (8j+1) r_q - (8k-1) r_p >= t, ends covered, readings in [1, hi7], r7 in [lo7, hi7], sorted), move to the LP optimum plus a small perturbation, repeat.  A type with t > 1e-9 gives a carve candidate, re-tested exactly (Fractions, strict overlap).  Seeded.  usage: seed lo7 hi7 restarts iters
import sys, random, pickle, collections
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
seed = int(sys.argv[1]); lo7 = float(sys.argv[2]); hi7 = float(sys.argv[3]); random.seed(seed); np.random.seed(seed)
n = 6
hi7 = 80.0; lo7 = 15.0
def chain_of(x):
    zones = []
    for idx, r in enumerate(x):
        j = 1
        while (8 * j - 1) / r < 7:
            zones.append(((8 * j - 1) / r, (8 * j + 1) / r, idx, j)); j += 1
    zones.sort()
    cand = [z for z in zones if z[0] < 1 < z[1]]
    if not cand: return None
    chain = [max(cand, key=lambda z: z[1])]; cur = chain[0][1]
    while cur <= 7:
        opts = [z for z in zones if z[0] <= cur and z[1] > cur]
        if opts: z = max(opts, key=lambda z: z[1])
        else:
            nxt = [z for z in zones if z[0] > cur]
            if not nxt: return None
            z = min(nxt, key=lambda z: z[0])
        chain.append(z); cur = z[1]
    return tuple((z[2], z[3]) for z in chain)
def lp_margin(chain):
    A = []; b = []
    for k in range(len(chain) - 1):
        (p, jp), (q, jq) = chain[k], chain[k + 1]
        if p == q: return None
        row = np.zeros(n + 1); row[q] += -(8 * jp + 1); row[p] += (8 * jq - 1); row[n] = 1.0
        A.append(row); b.append(0.0)
    p, j = chain[0]
    row = np.zeros(n + 1); row[p] = -1; row[n] = 1; A.append(row); b.append(-(8 * j - 1))
    row = np.zeros(n + 1); row[p] = 1; row[n] = 1; A.append(row); b.append(8 * j + 1)
    p, j = chain[-1]
    row = np.zeros(n + 1); row[p] = 7; row[n] = 1; A.append(row); b.append(8 * j + 1)
    for i in range(n - 1):
        row = np.zeros(n + 1); row[i] = 1; row[i + 1] = -1; A.append(row); b.append(0.0)
    c = np.zeros(n + 1); c[n] = -1
    bounds = [(1, hi7)] * (n - 1) + [(lo7, hi7)] + [(None, 10)]
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=bounds, method='highs')
    if res.status != 0: return None
    return -res.fun, res.x[:n]
def carves_exact(x):
    iv = []
    for r in x:
        r = F(r)
        for j in range(1, int(7 * r / 8) + 3):
            a, b = F(8 * j - 1) / r, F(8 * j + 1) / r
            if b > 1 and a < 7: iv.append((a, b))
    if not any(a < 1 < b for a, b in iv): return False
    cur = max(b for a, b in iv if a < 1)
    while cur <= 7:
        nxt = [b for a, b in iv if a < cur and b > cur]
        if not nxt: return False
        cur = max(nxt)
    return True
found = []; types_seen = set(); best_t = -1e9; stuck_types = collections.Counter()
for rest in range(int(sys.argv[4])):
    x = sorted([random.uniform(1, min(9, hi7)) for _ in range(5)] + [random.uniform(lo7, hi7)])
    seen_here = set()
    for it in range(int(sys.argv[5])):
        ch = chain_of(x)
        if ch is None: break
        r = lp_margin(ch)
        if r is None: break
        t, xs = r; types_seen.add(ch)
        best_t = max(best_t, t)
        if t > 1e-9:
            xs = list(map(float, xs))
            if carves_exact(xs): found.append((xs, ch)); break
            break
        if ch in seen_here:
            x = sorted(max(1.0001, v * (1 + random.uniform(-0.03, 0.03))) for v in x); x[-1] = min(max(x[-1], lo7), hi7); x = sorted(x)
        else:
            seen_here.add(ch)
            x = sorted(max(1.0001, float(v) * (1 + random.uniform(-1e-3, 1e-3))) for v in xs); x[-1] = min(max(x[-1], lo7), hi7); x = sorted(x)
pickle.dump(found, open('frontier_type_search_v1_%s_%s_s%d.pkl' % (sys.argv[2], sys.argv[3], seed), 'wb'))
print('r7 in', (lo7, hi7), 'restarts', sys.argv[4], 'iters', sys.argv[5], '| distinct chain types visited:', len(types_seen), '| exact carves found:', len(found), '| rho7 of carves:', sorted(round(f[0][5], 3) for f in found)[:15], '| best margin (float):', best_t)
