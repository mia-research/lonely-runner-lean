"""E949: can every non-closer reading escape?  A search for a gate-crossing arrangement with min_k B_k > 8 end(landing)
(2026-11-25).  Exact Fractions; the search itself is a seeded hill-climb (seed = start index), which steers only.
Starts: the 24 crossers of crosser_equality_v1 whose attaining set is one reading (reading 5, class X, in all 24).
State: readings r_1 = 1 < r_2 < ... < r_7.  Step: one reading k in 2..7 multiplied by (1 + s u), u in {-1, -1/2, 1/2, 1},
s in {2^-8 .. 2^-20}, order kept.  Objective (lexicographic, smaller is better): (not a gate crosser, number of
attaining readings, total relative gap between the pass set P of W_k and the set A of positions of k that pass every
earlier six-window, over the attaining readings).  Classes as crosser_equality_v1 (C, L, P, X, N); for L and P the gap is
taken as 1.  A found arrangement (no attaining reading) is confirmed with bmove: min_k B_k > 8 end."""
import pickle, glob, sys, random
from fractions import Fraction as Fr
from math import floor, ceil
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load(open('/Users")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
rows = []
for f in sorted(glob.glob('crosser_equality_v1_part*.pkl')): rows += pickle.load(open(f, 'rb'))
rows.sort(); starts = [r for r in rows if len(r[4]) == 1]
def score(rs):
    T, path = cascade(rs, E)
    if 8 * T < 9: return (1, 9, Fr(9)), None
    ents = [(floor(x * T + E) + 1 - E) / x for x in rs]; end = min(ents)
    natt = 0; gap = Fr(0); cls = {}
    for k in range(1, 7):
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1)
        n = next(i for i, (a, b, o) in enumerate(ws) if a <= T <= b); a, b, o = ws[n]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1 if b > a else Fr(10) ** 4
        if b > end: cls[k + 1] = 'C'; continue
        if b - a >= Fr(1, 4) / lo: cls[k + 1] = 'L'; natt += 1; gap += 1; continue
        P = [(l, h) for l, h, m in passes(a, b, lo, hi)]
        if not P: cls[k + 1] = 'P'; natt += 1; gap += 1; continue
        A = [(lo, hi)]
        for jj in range(n):
            if not A: break
            A = passes_in(ws[jj][0], ws[jj][1], A)
        if not A: cls[k + 1] = 'X'; natt += 1; gap += 1; continue
        d = min(max(Fr(0), max(l1, l2) - min(h1, h2)) for l1, h1 in P for l2, h2 in A)
        if d == 0: cls[k + 1] = 'N'
        else: cls[k + 1] = 'X'; natt += 1; gap += d / rs[k]
    return (0, natt, gap), cls
si = int(sys.argv[1]); iters = int(sys.argv[2])
idx0 = starts[si][0]; rs = sorted(Fr(x) for x in rec[idx0][1]); rng = random.Random(si)
cur, cls = score(rs); best = cur
print('start', si, 'E340 index', idx0, 'score', (cur[0], cur[1], float(cur[2])), cls, flush=True)
for it in range(iters):
    k = rng.randrange(1, 7); s = Fr(1, 2 ** rng.randrange(8, 21)); u = rng.choice([Fr(-1), Fr(-1, 2), Fr(1, 2), Fr(1)])
    new = list(rs); new[k] = rs[k] * (1 + s * u)
    if not all(new[i] < new[i + 1] for i in range(6)): continue
    sc, cl = score(new)
    if sc <= cur:
        rs, cur, cls = new, sc, cl
        if cur[1] == 0:
            T, _ = cascade(rs, E); end = min((floor(x * T + E) + 1 - E) / x for x in rs)
            Bs = {}
            for kk in range(1, 7):
                six = rs[:kk] + rs[kk + 1:]
                Bs[kk + 1] = bmove(six, rs[kk - 1], rs[kk + 1] if kk < 6 else None)[0]
            print('FOUND', si, 'iteration', it, 'readings', [str(x) for x in rs], 'R*', 8 * T, '8 end', 8 * end, 'B_k', {q: str(v) for q, v in Bs.items()}, 'min B > 8 end', min(v for v in Bs.values() if isinstance(v, Fr)) > 8 * end, flush=True)
            break
    if it % 100 == 0: print('  it', it, 'score', (cur[0], cur[1], float(cur[2])), cls, flush=True)
print('end', si, 'score', (cur[0], cur[1], float(cur[2])), cls, 'readings (floats, steer only)', [round(float(x), 8) for x in rs])
