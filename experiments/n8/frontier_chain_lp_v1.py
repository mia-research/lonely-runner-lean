# E830: the zone chain of the polished near-carve above 25 (frontier_polish_v1_first.pkl), its link inequalities, and an LP (floats steer only) over the readings for that chain type: the largest margin t with every link (8j+1) r_q - (8k-1) r_p >= t, ends covered, readings in [1, 60] (HiGHS); the dual shows which links bind.
import pickle
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
x = pickle.load(open('frontier_polish_v1_first.pkl', 'rb'))
rs = [F(v) for v in x]
zones = []
for idx, r in enumerate(rs):
    j = 1
    while (8 * j - 1) / r < 7:
        zones.append(((8 * j - 1) / r, (8 * j + 1) / r, idx, j)); j += 1
zones.sort()
start = max([z for z in zones if z[0] < 1 < z[1]], key=lambda z: z[1])
chain = [start]; cur = start[1]; breaks = []
while cur <= 7:
    opts = [z for z in zones if z[0] <= cur and z[1] > cur]
    if opts: z = max(opts, key=lambda z: z[1])
    else:
        z = min([z for z in zones if z[0] > cur], key=lambda z: z[0]); breaks.append((float(cur), float(z[0]), len(chain)))
    chain.append(z); cur = z[1]
print('chain length', len(chain), '| breaks (clear windows) at chain positions:', [(b[2]) for b in breaks])
print('chain (reading rho_{idx+2}, lap):', [('r%d' % (z[2] + 2), z[3]) for z in chain])
# LP: variables r2..r7 (6) and t
n = 6
A = []; bvec = []; names = []
def link(p, jp, q, jq, nm):
    # zone (p, jp) then zone (q, jq): exit (8jp+1)/r_p > entry (8jq-1)/r_q  <=>  (8jp+1) r_q - (8jq-1) r_p >= t
    row = np.zeros(n + 1); row[q] += -(8 * jp + 1); row[p] += (8 * jq - 1); row[n] = 1.0   # -( ... ) + t <= 0
    A.append(row); bvec.append(0.0); names.append(nm)
for k in range(len(chain) - 1):
    p, jp = chain[k][2], chain[k][3]; q, jq = chain[k + 1][2], chain[k + 1][3]
    if p == q: continue
    link(p, jp, q, jq, 'link %d: r%d lap %d -> r%d lap %d' % (k, p + 2, jp, q + 2, jq))
# ends: first zone covers R = 1 strictly: 8j-1 < r < 8j+1
p, j = chain[0][2], chain[0][3]
row = np.zeros(n + 1); row[p] = -1; row[n] = 1; A.append(row); bvec.append(-(8 * j - 1)); names.append('start lower: r%d > %d' % (p + 2, 8 * j - 1))
row = np.zeros(n + 1); row[p] = 1; row[n] = 1; A.append(row); bvec.append(8 * j + 1); names.append('start upper: r%d < %d' % (p + 2, 8 * j + 1))
p, j = chain[-1][2], chain[-1][3]
row = np.zeros(n + 1); row[p] = 7; row[n] = 1; A.append(row); bvec.append(8 * j + 1); names.append('end: 7 r%d < %d' % (p + 2, 8 * j + 1))
for i in range(n - 1):   # sorted: r_i <= r_{i+1}
    row = np.zeros(n + 1); row[i] = 1; row[i + 1] = -1; A.append(row); bvec.append(0.0); names.append('order r%d <= r%d' % (i + 2, i + 3))
c = np.zeros(n + 1); c[n] = -1
res = linprog(c, A_ub=np.array(A), b_ub=np.array(bvec), bounds=[(1, 60)] * n + [(None, 10)], method='highs')
print('LP status', res.status, 'largest margin t (float, steering):', -res.fun)
print('readings at the LP optimum (float):', [round(v, 6) for v in res.x[:n]])
m = res.ineqlin.marginals
print('binding constraints (nonzero dual, float):')
for nm, d in zip(names, m):
    if abs(d) > 1e-9: print('  ', nm, 'dual', round(float(d), 6))
