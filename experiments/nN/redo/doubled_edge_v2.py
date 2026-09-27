"""E135: doubled edges, fast exact form.  For a reference (j, m) and class c (phi(8)), reading i may take grid point
n in {floor, ceil}(x_i), x_i = s_i m / s_j, n >= 1, and lap k = floor(c n / 8) (a captured reading, c n = 0 mod 8, also
k - 1).  Its clear R-interval is [(8k+1)/s_i, (8k+7)/s_i].  The class works iff some R lies in one option of every
reading; R may be taken at an option's left end (1-D Helly).  For each working R record the edge structure of the
options used, choosing per reading to minimise edge doubling: |A| = readings with c n = 1 (mod 8), |B| = c n = 7,
Z = captured.  Per band set to 24: is there a working option with single edges and no capture ('single')?  Exact."""
import itertools
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return 8 * T[0] * t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def working(s, M=2):
    """yield (m, j, c, R, per-reading list of usable (n, k, residue)) for every working reference/class/instant"""
    for m in range(1, M + 1):
        for j in range(7):
            lam = s[j] / m
            for c in (1, 3, 5, 7):
                R0 = c / lam
                if R0 < 1 or 7 < R0 < 9 or R0 > 15: continue
                opts = []
                for x in s:
                    o = []
                    for n in sorted({floor(x / lam), ceil(x / lam)}):
                        if n < 1: continue
                        r = (c * n) % 8; k = (c * n) // 8
                        for kk in ((k - 1, k) if r == 0 else (k,)):
                            if kk >= 0: o.append((n, kk, r))
                    opts.append(o)
                if any(not o for o in opts): continue
                cands = sorted({F(8 * k + 1) / x for x, o in zip(s, opts) for (_, k, _) in o})
                for R in cands:
                    use = [[(n, k, r) for (n, k, r) in o if F(8 * k + 1) / x <= R <= F(8 * k + 7) / x] for x, o in zip(s, opts)]
                    if all(use): yield (m, j, c, R, use)
def best_structure(use):
    """choose one option per reading minimising (captures, max edge multiplicity)"""
    best = None
    for pick in itertools.product(*use):
        res = [r for (_, _, r) in pick]
        key = (res.count(0), max(res.count(1), res.count(7)))
        if best is None or key < best[0]: best = (key, pick)
    return best
def study(first):
    cnt = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1] <= 9 * T[0]): continue
        s = [F(d, T[0]) for d in T]
        bestkey = None; bestw = None
        for (m, j, c, R, use) in working(s):
            key, pick = best_structure(use)
            if bestkey is None or key < bestkey: bestkey, bestw = key, (m, j, c, R, pick)
            if key == (0, 1): break
        cnt[bestkey] += 1
        if bestkey != (0, 1) and len(ex) < 40: ex.append((T, bestkey, bestw, cascade(T)))
    return cnt, ex
if __name__ == '__main__':
    tot = Counter(); EX = []
    with Pool(8) as p:
        for c, e in p.imap_unordered(study, range(1, 19)): tot.update(c); EX += e
    print("band sets to 24; best working grid-class option, key = (captured readings, max readings on one edge):")
    for k, v in sorted(tot.items(), key=lambda kv: (kv[0] is None, kv[0])): print("  %6d  %s" % (v, k))
    print("\nsets whose every working option has a doubled edge or a capture:")
    for T, key, w, R in sorted(EX)[:40]:
        m, j, c, Rw, pick = w
        print("  ", T, "key", key, "  best: m=%d j=%d c=%d R=%.4f" % (m, j, c, float(Rw)), "n,k,res:", [(p[0], p[1], p[2]) for p in pick], " cascade R* = %.4f" % float(R))
