"""E132: doubled edges.  For every band set to 24 (spread in (7, 9]), every working grid-class option (reference j,
m <= 2, class c in {1,3,5,7}, grid n_i in {floor, ceil}(x_i), captured readings on the lap before or at), record the edge
structure of the class: |A| = readings with c n = 1 (mod 8) (leaving edge), |B| = c n = 7 (entering edge), captured
c n = 0.  A set is 'single' if some working option has |A| <= 1, |B| <= 1 and no capture; else record what the working
options look like and the cascade's landing.  Exact."""
import itertools, sys
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
def compat(s, k):
    return all((8 * k[i] + 1) * s[j] <= (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
def options(s, M=2, CMAX=7):
    out = []
    for m in range(1, M + 1):
        for j in range(7):
            lam = s[j] / m
            opts = [sorted({floor(x / lam), ceil(x / lam)}) for x in s]
            for c in range(1, CMAX + 1, 2):
                R = c / lam
                if R < 1 or 7 < R < 9 or R > 15: continue
                for n in itertools.product(*opts):
                    if min(n) < 1: continue
                    base = [(c * q) // 8 for q in n]; amb = [i for i, q in enumerate(n) if (c * q) % 8 == 0]
                    for adj in itertools.product(*[(-1, 0) if i in amb else (0,) for i in range(7)]):
                        k = [b + a for b, a in zip(base, adj)]
                        if min(k) >= 0 and compat(s, k):
                            res = [(c * q) % 8 for q in n]
                            A = tuple(i for i in range(7) if res[i] == 1); B = tuple(i for i in range(7) if res[i] == 7)
                            Z = tuple(i for i in range(7) if res[i] == 0)
                            out.append((m, j, c, n, tuple(k), A, B, Z)); break
    return out
def study(first):
    cnt = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1] <= 9 * T[0]): continue
        s = [F(d, T[0]) for d in T]
        op = options(s)
        single = [o for o in op if len(o[5]) <= 1 and len(o[6]) <= 1 and not o[7]]
        if single:
            o = single[0]; cnt[('single', 'edges |A|,|B| = %d,%d' % (len(o[5]), len(o[6])))] += 1
        else:
            kinds = Counter(('doubled A' if len(o[5]) > 1 else '') + ('doubled B' if len(o[6]) > 1 else '') + ('captured' if o[7] else '') for o in op)
            cnt[('no single-edge option', tuple(sorted(kinds)))] += 1
            if len(ex) < 60: ex.append((T, op[:3], cascade(T)))
    return cnt, ex
if __name__ == '__main__':
    tot = Counter(); EX = []
    with Pool(6) as p:
        for c, e in p.imap_unordered(study, range(1, 19)): tot.update(c); EX += e
    print("band sets to 24: the best working grid-class option's edge structure (m <= 2, c <= 7):")
    for k, v in sorted(tot.items(), key=lambda kv: -kv[1]): print("  %6d  %s" % (v, k))
    print("\nsets with no single-edge option (first 40): T, R*, working options (m, j, c, n, laps, A, B, captured):")
    for T, op, R in sorted(EX)[:40]:
        print("  ", T, "R* = %.4f" % float(R))
        for o in op: print("        ", o)
