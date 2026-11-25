"""Wall-window index, test v6 (2026-11-25).  Exact Fractions.  Closed form for a one-move pass, checked against v5.

[P] A zone of reading f at lap k is the open interval ((8k-1)/(8f), (8k+1)/(8f)); it contains a window [a, b] iff
f lies in I_k(a, b) = ((8k-1)/(8a), (8k+1)/(8b)).  I_k is non-empty iff b/a < (8k+1)/(8k-1) (at most 9/7, k = 1).
F passes [a, b] in ONE move iff some F reading lies in some I_k(a, b)  (the max-exit blocker at a then exits past b).
For W_1 = [1/(8d), 7/(8 max S)]: I_k = ((8k-1) d, (8k+1) max S / 7), non-empty iff max S > (8k-1)/(8k+1) * 7d (>= 49/9 d).
Checked here: the predicate against v5's one-move passes, for every window up to the one holding T; and the window
ratio b/a of passed windows against the bound (9/7)^moves (each move multiplies the state by at most 9/7, E340).
"""
import sys
src = open('wall_window_index_v5.py').read().split("tab = Counter(); ex = {}")[0]
exec(src)
from math import floor, ceil
c = Counter(); exs = {}
def onemove_pred(Fs, a, b):
    hits = []
    for f in Fs:
        for k in range(max(1, floor(8 * a * f / 8) - 1), floor(f * b) + 2):
            if Fr(8 * k - 1, 8) / a < f < Fr(8 * k + 1, 8) / b: hits.append((Fs.index(f) + 1, k))
    return hits
def case(pop, rs, label):
    rs = sorted(rs); d = rs[0]; t0 = E / d
    S = [r for r in rs if r <= 7 * d]; Fs = [r for r in rs if r > 7 * d]
    if not Fs: return
    T, _ = cascade(rs, t0)
    ws = windows(S, t0, T + 1)
    i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    for j in range(i + 1):
        a, b, o = ws[j]
        moves, passed, setters, st = f_run(Fs, a, b)
        hits = onemove_pred(Fs, a, b)
        one = passed and moves == 1
        key = (pop, 'W%d' % min(j + 1, 3), 'one-move pass' if one else ('chain pass' if passed else 'lands'),
               'pred %s' % ('yes' if hits else 'no'))
        c[key] += 1
        if hits and one: c[(pop, 'W%d' % min(j + 1, 3), 'one-move pass', 'lap k of hit %s' % min(min(h[1] for h in hits), 4))] += 1
        rho = b / a
        if passed:
            bound = Fr(9, 7) ** moves
            c[(pop, 'passed windows', 'ratio < (9/7)^moves' if rho < bound else 'RATIO >= (9/7)^moves')] += 1
        c[(pop, 'W%d' % min(j + 1, 3), 'passed' if passed else 'lands', 'ratio b/a %s 9/7' % ('<' if rho < Fr(9, 7) else '>='))] += 1
        if j == 0:
            c[(pop, 'W1', 'passed' if passed else 'lands', 'max S %s 49d/9' % ('>' if S[-1] > Fr(49, 9) * d else '<='))] += 1
        if (hits and not one) or (one and not hits):
            exs.setdefault(key, (label, [str(x) for x in rs], j, str(a), str(b), hits, setters))
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
import itertools, random
for v in itertools.combinations(range(1, 17), 8):
    for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)], (v, k))
rng = random.Random(1)
for _ in range(3000):
    gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
    v = [Fr(1)]
    for g in gaps: v.append(v[-1] + g)
    for k in range(8): case('Q', readings(v, k), ([str(g) for g in gaps], k))
rng = random.Random(6); seen = 0
while seen < 2900:
    others = sorted(set(Fr(rng.randint(13, 480), 12) for _ in range(6)))
    if len(others) < 6: continue
    seen += 1; case('W40', [Fr(1)] + others, seen)
for k, v in sorted(c.items(), key=lambda x: str(x[0])):
    print(v, k)
    if k in exs: print('      e.g.', exs[k])
