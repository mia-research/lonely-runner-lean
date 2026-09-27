"""E118: Case C residual members?  Spread d_max > 24 d_min, all 22 EightResidual fields.  Exact integers.
Construction: one collider L*u (L = 8 lcm(1..64): dead lattices D <= 64) placed as the least reading (mode A) or
inside the fast cluster (mode B); the other six hill-climbed, objective = fields passed (v4's order, then fast pair,
block split, one free), spread > 24 enforced."""
exec(open('residual_fields_v1.py').read())
import itertools
def scoreC(S):
    if len(set(S)) < 7 or max(S) <= 24 * min(S): return -1
    for i, (_, f) in enumerate(FIELDS):
        if not f(S): return i
    return len(FIELDS)
rnd = random.Random(118); found = {'A': [], 'B': []}; best = {'A': (-1, None), 'B': (-1, None)}
fails = {'A': Counter(), 'B': Counter()} if 'Counter' in dir() else None
from collections import Counter
fails = {'A': Counter(), 'B': Counter()}
for mode in 'AB':
    for r in range(300):
        u = rnd.randrange(1, 20)
        if mode == 'A':
            dmin = L * u; lo, hi = 25 * dmin, 25 * dmin * rnd.choice((2, 5, 7))
            others = [rnd.randrange(lo, hi) for _ in range(6)]
            build = lambda o: tuple(sorted([dmin] + o))
            rng = lambda: (lo, hi)
        else:
            col = L * u; dmin = rnd.randrange(1, max(2, col // 25))
            lo, hi = col // 7 + 1, col * 7
            others = [dmin] + [rnd.randrange(lo, hi) for _ in range(5)]
            build = lambda o: tuple(sorted([col] + o))
            rng = lambda: (lo, hi)
        S = build(others); sc = scoreC(S)
        for step in range(400):
            o = list(others); i = rnd.randrange(6)
            if mode == 'B' and i == 0: 
                o[0] = rnd.randrange(1, max(2, min(o[1:] + [col]) // 25))
            else:
                a, b = rng(); base = rnd.randrange(a, b); mod = rnd.choice((8, 24, 40, 120))
                o[i] = base - base % mod + rnd.randrange(mod)
            T = build(o); s2 = scoreC(T)
            if s2 >= sc: others, S, sc = o, T, s2
            if sc == len(FIELDS): break
        fails[mode][FIELDS[sc][0] if 0 <= sc < len(FIELDS) else ('spread<=24' if sc < 0 else 'ALL')] += 1
        if sc == len(FIELDS): found[mode].append(S)
for mode in 'AB':
    print("mode", mode, "(collider = least reading)" if mode == 'A' else "(collider inside the fast cluster)",
          ": members", len(found[mode]), "; first failing field after climbing:", dict(fails[mode]))

# through the cascade, exact
from fractions import Fraction as F
from math import floor
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * min(T)); n = 0
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t, n
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way); n += 1
for mode in 'AB':
    summ = Counter(); Rs = []
    for S in found[mode]:
        Ss = sorted(S); t, n = cascade(Ss)
        i, K = next((i, e * t - E8) for i, e in enumerate(Ss) if (e * t - E8).denominator == 1)
        core = [d for d in Ss if d * 24 < Ss[-1]]; clus = [d for d in Ss if d * 24 >= Ss[-1]]
        R = 8 * Ss[0] * t; Rs.append(float(R))
        summ[('core %d / cluster %d' % (len(core), len(clus)), 'flank in cluster' if Ss[i] in clus else 'flank in core',
              'R* <= 7 (slow runner on its first lap)' if R <= 7 else 'R* > 7')] += 1
        summ['cluster spread <= 7'] += clus[-1] <= 7 * clus[0]
    print("mode", mode, "cascade on", len(found[mode]), "members; R* range %.3f..%.3f" % (min(Rs), max(Rs)))
    for k, v in sorted(summ.items(), key=str): print("   ", v, k)
