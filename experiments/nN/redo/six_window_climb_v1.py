"""E153: the six-reading window ratio rho on fine shapes (denominator 2520), hill-climbed from the integer extremes and
from random starts.  rho(G) = sup over A >= 1 of (next lonely R >= A)/A, R in own-bound units, computed exactly on
[1, 400].  Reports the largest rho found and its shape."""
import random, sys
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
D = 2520; RMAX = 400
def rho(g):
    s = sorted(F(x, g[0]) for x in g)
    L = clear_set(s, F(1), F(RMAX))
    if not L: return F(10 ** 6)
    w = L[0][0]
    for (a, b), (c, d) in zip(L, L[1:]): w = max(w, c / b)
    return w
def climb(seed):
    rng = random.Random(seed)
    starts = [(6, 8, 10, 11, 13, 14), (7, 11, 14, 16, 18, 20), (8, 10, 11, 12, 13, 14), (4, 6, 8, 10, 11, 14)]
    g = [x * D for x in starts[seed % 4]] if seed < 8 else sorted(rng.sample(range(D, 8 * D), 6))
    best = rho(g)
    for step in range(1500):
        h = list(g); i = rng.randrange(6); h[i] += rng.choice((-1, 1)) * rng.randrange(1, max(2, D // (10 + step // 50)))
        h = sorted(h)
        if len(set(h)) < 6 or h[0] <= 0: continue
        r = rho(h)
        if r >= best: g, best = h, r
    return best, [x / g[0] for x in g]
if __name__ == '__main__':
    with Pool(8) as p: res = sorted(p.imap_unordered(climb, range(24)), key=lambda x: -x[0])
    for r, g in res[:8]: print("rho = %.4f  shape (least = 1): %s" % (float(r), [round(float(x), 4) for x in g]))
