"""E136: at the AP scale (reference = nearest runner, grid n_i = round(s_i)), decide each phi(8) class exactly (lap
k_i = floor(c n_i / 8), a captured reading on the lap before or at; relocation free; 1-D Helly), and name why a class
fails.  Compare with the cascade: does a late landing (R* > 7) occur only when both mirror pairs (1,7) and (3,5) fail?
Populations: every band set to 24 (all land in [1,7]); late fine shapes (d1 = 27720, perturbation walks, as in
grid_class_v2._study).  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set, least_clear
def rnd(q): return int((q + F(1, 2)) // 1)
def class_status(s, c):
    n = [rnd(x) for x in s]
    if min(n) < 1: return 'n<1'
    opts = []
    for x, q in zip(s, n):
        r = (c * q) % 8; k = (c * q) // 8
        opts.append([kk for kk in ((k - 1, k) if r == 0 else (k,)) if kk >= 0])
    cands = sorted({F(8 * k + 1) / x for x, o in zip(s, opts) for k in o})
    for R in cands:
        if all(any(F(8 * k + 1) / x <= R <= F(8 * k + 7) / x for k in o) for x, o in zip(s, opts)): return 'works'
    res = [(c * q) % 8 for q in n]
    A = [i for i in range(7) if res[i] == 1]; B = [i for i in range(7) if res[i] == 7]
    if 0 in res: return 'fails: capture'
    lag = [F(q) / x for q, x in zip(n, s)]
    if A and B and max(lag[i] for i in A) > min(lag[i] for i in B): return 'fails: edges cross'
    return 'fails: interior deviation'
def pairs(s):
    st = {c: class_status(s, c) for c in (1, 3, 5, 7)}
    p17 = st[1] == 'works' or st[7] == 'works'; p35 = st[3] == 'works' or st[5] == 'works'
    return p17, p35, st
out = Counter(); why = Counter()
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1] <= 9 * T[0]): continue
    s = [F(d, T[0]) for d in T]; p17, p35, st = pairs(s)
    out[('band to 24 (R* <= 7)', 'pair (1,7) ' + ('holds' if p17 else 'fails'), 'pair (3,5) ' + ('holds' if p35 else 'fails'))] += 1
    if not p17 and not p35: why[('band to 24', tuple(sorted(set(st.values()))))] += 1
# late fine shapes
D1 = 27720; rng = random.Random(41); late = set()
for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
    T = [int(round(x * D1)) for x in sd]
    for step in range(3000):
        L = list(T); i = rng.randrange(1, 7); L[i] += rng.randrange(-500, 501)
        U = sorted(set(L))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        s = [F(d, D1) for d in U]
        if clear_set(s, F(1), F(7)): continue
        T = U; late.add(tuple(U))
for U in sorted(late):
    s = [F(d, D1) for d in U]; p17, p35, st = pairs(s)
    out[('late fine shapes (R* > 7)', 'pair (1,7) ' + ('holds' if p17 else 'fails'), 'pair (3,5) ' + ('holds' if p35 else 'fails'))] += 1
    if not p17 and not p35: why[('late', tuple(sorted(set(st.values()))))] += 1
for k, v in sorted(out.items()): print("  %6d  %s" % (v, k))
print("\nwhere both pairs fail, the reasons present:")
for k, v in sorted(why.items(), key=lambda kv: -kv[1])[:20]: print("  %6d  %s" % (v, k))
