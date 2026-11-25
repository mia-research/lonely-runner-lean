"""R* against the d_max side, test v1 (2026-11-25).  Exact Fractions for every reported value; floats steer only.

Question (G2, after outcome_split_v1): is the landing R* = 8 d_min T bounded independently of the fast readings?
(a) M071's d_max shift on E340's members with R* >= 11: replace each F reading f (f > 7 d_min) by f + j/T,
    j = 1..J (its position at T is unchanged); record the new R* and whether it equals the old.
(b) climb: from the 40 highest-R* members, repeatedly replace one reading by a random value (S readings within
    [1, 7] on the 1/1024 grid; F readings in (7, 400] on the 1/64 grid), keep the change when R* does not drop;
    1,500 steps per start.  Report the largest R* found, exact, with its readings.
"""
import pickle, random
from fractions import Fraction as Fr
from math import floor
exec(open('wall_window_index_v5.py').read().split('def windows')[0])
def Rstar(rs):
    rs = sorted(rs); d = rs[0]
    if len(set(rs)) < len(rs): return None
    T, _ = cascade(rs, E / d); return 8 * d * T, T
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
mem = []
for r in rec:
    rs = sorted(Fr(x) for x in r[1]); R, T = Rstar(rs); mem.append((R, rs, T))
mem.sort(key=lambda x: -x[0])
hi = [m for m in mem if m[0] >= 11]
print('(a) members with R* >= 11:', len(hi))
same = up = down = 0; best = Fr(0)
for R, rs, T in hi:
    for j in range(1, 6):
        for idx, f in enumerate(rs):
            if f <= 7 * rs[0]: continue
            new = list(rs); new[idx] = f + Fr(j) / T
            x = Rstar(new)
            if x is None: continue
            R2 = x[0]; best = max(best, R2)
            if R2 == R: same += 1
            elif R2 > R: up += 1
            else: down += 1
print('    shifted cases: R* unchanged', same, '| larger', up, '| smaller', down, '| largest R* after a shift', best, '=', round(float(best), 4))
rng = random.Random(925); top = Fr(0); topr = None
for R, rs, T in mem[:40]:
    cur, curR = list(rs), R
    for step in range(1500):
        new = list(cur); i = rng.randrange(1, 7)
        if rng.random() < 0.5: new[i] = Fr(rng.randint(1025, 7 * 1024), 1024)
        else: new[i] = Fr(rng.randint(7 * 64 + 1, 400 * 64), 64)
        x = Rstar(new)
        if x is None: continue
        if x[0] >= curR: cur, curR = sorted(new), x[0]
    if curR > top: top, topr = curR, cur
    print('    climb from R* =', round(float(R), 4), '-> R* =', curR, '=', round(float(curR), 4), '| max reading', round(float(max(cur)), 2))
print('(b) largest R* found:', top, '=', round(float(top), 6), '| readings', [str(x) for x in topr])
