"""E129: the single-class small-deviation criterion (provable like clear_at_class): reference grid lam = s_j/m (m <= M),
x_i = s_i/lam, n_i = round(x_i) >= 1; class c odd; rescaling nu in {n_i/x_i}; condition: no reading captured
(c n = 0 mod 8); interior (c n = 2..6): |x nu - n| <= 1/c; leaving edge (c n = 1): 0 <= x nu - n <= 6/c; entering edge
(c n = 7): -6/c <= x nu - n <= 0.  Any number of readings per edge.  Exact.  Coverage and, for the unsettled, whether the
blocking candidate had a doubled edge or a captured reading."""
import itertools, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
M = int(sys.argv[3]) if len(sys.argv) > 3 else 4; CMAX = 63
def rnd(q): return int((q + F(1, 2)) // 1)
def ok_class(x, n, c, nu):
    for xi, ni in zip(x, n):
        r = (c * ni) % 8; d = xi * nu - ni
        if r == 0: return False
        if 2 <= r <= 6:
            if abs(d) > F(1, c): return False
        elif r == 1:
            if not (0 <= d <= F(6, c)): return False
        else:
            if not (-F(6, c) <= d <= 0): return False
    return True
def settles(s):
    for m in range(1, M + 1):
        for j in range(7):
            lam = s[j] / m; x = [v / lam for v in s]; n = [rnd(v) for v in x]
            if min(n) < 1: continue
            nus = sorted({F(ni) / xi for xi, ni in zip(x, n)})
            for c in range(1, CMAX + 1, 2):
                for nu in nus:
                    if ok_class(x, n, c, nu): return True
    return False
N = int(sys.argv[1]); SMAX = int(sys.argv[2])
def chunk(first):
    cov = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, N + 1), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1] <= SMAX * T[0]): continue
        r = settles([F(d, T[0]) for d in T]); cov[r] += 1
        if not r and len(ex) < 4: ex.append(T)
    return cov, ex
if __name__ == '__main__':
    cov = Counter(); EX = []
    with Pool(10) as p:
        for c, e in p.imap_unordered(chunk, range(1, N - 5)): cov.update(c); EX += e
    print("readings <= %d, spread (7, %d], m <= %d: settled by the single-class criterion: %d of %d" % (N, SMAX, M, cov[True], cov[True] + cov[False]))
    print("  unsettled e.g.", EX[:8])
