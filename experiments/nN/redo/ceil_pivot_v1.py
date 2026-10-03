# pivot walk across tight rows maximising rho_IDX over gate-crossing fine cells (exact; floats only choose LP basis / crossing direction)
import sys, time, heapq, math, ast
from ceil_lib_v1 import *
from collections import Counter
from scipy.optimize import linprog
import numpy as np
IDX = int(sys.argv[1]); LIM = float(sys.argv[2]); starts_arg = sys.argv[3:] 
T0 = time.time()
def info_of(x):
    x = norm(x); ok, st, R = crosses(x)
    if not ok: return None, 'gate'
    rows, tags, _ = cell_rows(x)
    r = maxrho(rows, IDX)
    if r is None: return None, 'lpfail'
    X, lam = r
    return dict(x=x, rows=rows, tags=tags, X=X, lam=lam, sup=X[IDX-1], sig=sigkey(tags, st), R=R, n=len(st)), 'ok'
starts = [('X7', X7)]
for a in starts_arg:
    starts.append(('arg', [F(t) for t in ast.literal_eval(a)]))
seen = {}; heap = []; cnt = 0; stalls = Counter(); lpfail = 0; best = None
def push(x, label):
    global cnt, lpfail, best
    info, why = info_of(x)
    if info is None:
        if why == 'lpfail': lpfail += 1
        return why
    if info['sig'] in seen: return 'dup'
    seen[info['sig']] = info; cnt += 1
    heapq.heappush(heap, (-info['sup'], cnt, label, info))
    if best is None or info['sup'] > best[0]: best = (info['sup'], label, info)
    return 'new'
for lab, x in starts: print('start', lab, push(x, lab), flush=True)
def cross(info, S, T):
    rows = info['rows']; X = info['X']
    A_eq = [[float(t) for t in rows[i][1:]] for i in S]; b_eq = [-1.0] * len(S)
    A_ub = [[-float(t) for t in rows[j][1:]] for j in T if j not in S]; b_ub = [-1.0] * len(A_ub)
    r = linprog(np.zeros(6), A_ub=A_ub or None, b_ub=b_ub or None, A_eq=A_eq, b_eq=b_eq, bounds=[(None, None)] * 6, method='highs')
    if r.status != 0: return None
    dv = [F(float(t)).limit_denominator(10**6) for t in r.x]
    for k in range(4, 15):
        e = F(1, 10**k); y = [F(1)] + [X[i+1] + e * dv[i] for i in range(6)]
        if all(row_val(rows[i], y) < 0 for i in S) and all(row_val(rows[j], y) >= 0 for j in T if j not in S): return y
    return None
exp = 0
while heap and time.time() - T0 < LIM:
    negs, _, lab, info = heapq.heappop(heap); exp += 1
    rows = info['rows']; X = info['X']
    T = dedupe_rows(rows, tight(rows, X))
    subs = [(i,) for i in T] + [(i, j) for ii, i in enumerate(T) for j in T[ii+1:]]
    for S in subs:
        if time.time() - T0 > LIM: break
        y = cross(info, S, T)
        if y is None: stalls['nodir'] += 1; continue
        r = push(y, lab + '>')
        if r == 'gate': stalls['gate lost: ' + '; '.join(row_meaning(info['tags'][i]) for i in S)] += 1
print('expanded', exp, 'cells with exact sup', len(seen), 'lpfail', lpfail, 'frontier left', len(heap), 'time', round(time.time() - T0))
vals = sorted(seen.values(), key=lambda d: -d['sup'])
print('top exact cell sups of rho%d:' % IDX, [(str(v['sup']), round(float(v['sup']), 6)) for v in vals[:8]])
b = vals[0]; print('best vertex', [str(t) for t in b['X']], 'rows tight:')
Tb = dedupe_rows(b['rows'], tight(b['rows'], b['X']))
for i in Tb: print('  ', b['rows'][i], row_meaning(b['tags'][i]))
print('best dual', {i: str(l) for i, l in b['lam'].items()})
print('best cell member', [str(t) for t in b['x']], 'landing', b['R'], 'moves', b['n'])
print('top stalls:')
for k, v in stalls.most_common(15): print('  ', v, k)
