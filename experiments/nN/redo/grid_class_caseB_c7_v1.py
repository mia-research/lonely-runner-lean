"""E131: the owed re-check (handover v8 section 4; compile-diff item 10).  Case B to readings <= 24 (spread in (7, 24]):
least m (<= 4) with a grid reference s_j/m and a class c restricted to the phi(8) classes c in {1, 3, 5, 7}; same lap
rule, relocation and exact pairwise decision as grid_class_v2 (which allowed c odd up to 199).  Reports the least m and
every set left uncovered."""
import itertools, sys
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
from multiprocessing import Pool
def compat(s, k):
    return all((8 * k[i] + 1) * s[j] <= (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
def least_m(s, M, CMAX=7):
    for m in range(1, M + 1):
        for j in range(7):
            lam = s[j] / m
            options = [sorted({floor(x / lam), ceil(x / lam)}) for x in s]
            for c in range(1, CMAX + 1, 2):
                R = c / lam
                if R > 15: break
                if R < 1 or 7 < R < 9: continue
                for n in itertools.product(*options):
                    if min(n) < 1: continue
                    base = [(c * q) // 8 for q in n]
                    amb = [i for i, q in enumerate(n) if (c * q) % 8 == 0]
                    for adj in itertools.product(*[(-1, 0) if i in amb else (0,) for i in range(7)]):
                        k = [b + a for b, a in zip(base, adj)]
                        if min(k) >= 0 and compat(s, k): return m
    return None
N = int(sys.argv[1]); SMAX = int(sys.argv[2]); M = int(sys.argv[3])
def chunk(first):
    c = Counter(); left = []
    for rest in itertools.combinations(range(first + 1, N + 1), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1] <= SMAX * T[0]): continue
        m = least_m([F(d, T[0]) for d in T], M)
        c[m] += 1
        if m is None: left.append(T)
    return c, left
if __name__ == '__main__':
    tot = Counter(); L = []
    with Pool(8) as p:
        for c, left in p.imap_unordered(chunk, range(1, N - 5)): tot.update(c); L += left
    print("readings <= %d, spread in (7, %d], classes c <= 7, m <= %d: least m:" % (N, SMAX, M),
          sorted(tot.items(), key=lambda kv: (kv[0] is None, kv[0] or 0)))
    print("  uncovered: %d" % len(L))
    for T in sorted(L)[:60]: print("   ", T)
