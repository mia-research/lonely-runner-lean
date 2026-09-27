"""E129 control: is the grid-class coverage (E128) content or near-tautology?  With c unrestricted, any flank opening
(8k+1)/s_j is the class c = 8k+1 of the grid through s_j (m = 1).  Restrict c <= CMAX (the phi(8) classes when CMAX = 7)
and compare coverage; also record the least c that works."""
import itertools, sys
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
from multiprocessing import Pool
def compat(s, k):
    return all((8 * k[i] + 1) * s[j] <= (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
def least_c(s, M=2):
    best = None
    for m in range(1, M + 1):
        for j in range(7):
            lam = s[j] / m
            options = [sorted({floor(x / lam), ceil(x / lam)}) for x in s]
            for c in range(1, 200, 2):
                if best is not None and c >= best: break
                R = c / lam
                if R > 15: break
                if R < 1 or 7 < R < 9: continue
                hit = False
                for n in itertools.product(*options):
                    if min(n) < 1: continue
                    base = [(c * q) // 8 for q in n]
                    amb = [i for i, q in enumerate(n) if (c * q) % 8 == 0]
                    for adj in itertools.product(*[(-1, 0) if i in amb else (0,) for i in range(7)]):
                        k = [b + a for b, a in zip(base, adj)]
                        if min(k) >= 0 and compat(s, k): hit = True; break
                    if hit: break
                if hit: best = c; break
    return best
def chunk(first):
    c = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1] <= 9 * T[0]): continue
        lc = least_c([F(d, T[0]) for d in T])
        c['<= 7' if lc is not None and lc <= 7 else ('9..15' if lc is not None and lc <= 15 else ('>15' if lc else 'none'))] += 1
    return c
if __name__ == '__main__':
    tot = Counter()
    with Pool(10) as p:
        for c in p.imap_unordered(chunk, range(1, 19)): tot.update(c)
    print("band sets to 24 (m <= 2): least class c that works:", dict(tot))
