"""E153: the lemma form suggested by rho = 9: six readings G (least = 1), from a start A >= 1, lonely inside
A.([1,7] u [9,15] u ... u [8m+1, 8m+7]) -- the first m+1 blocks of a slow runner whose bound is at A.  For each G the
worst start A needs how many blocks?  Exact: candidate starts are the breakpoints e/(8j+1), e/(8j+7) (e an endpoint of
G's lonely set on [1, RMAX]) and midpoints between consecutive candidates.  Populations: all 6-sets of readings <= 16,
the fine extremal shapes of six_window_climb_v1, and a climb maximising the blocks needed."""
import itertools, random, sys
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
RMAX = 2000; MB = 6
def lonely_set(G):
    s = sorted(F(x) / min(G) for x in G)
    return clear_set(s, F(1), F(RMAX))
def blocks_needed(L, A):
    for m in range(MB):
        lo, hi = A * (8 * m + 1), A * (8 * m + 7)
        if hi > RMAX: return None
        if any(a <= hi and b >= lo for a, b in L): return m + 1
    return MB + 1
def worst(G, Amax=F(40)):
    L = lonely_set(G)
    cands = set()
    for a, b in L:
        for e in (a, b):
            for j in range(MB):
                for q in (8 * j + 1, 8 * j + 7):
                    A = e / q
                    if 1 <= A <= Amax: cands.add(A)
    cands = sorted(cands | {F(1)})
    pts = cands + [(x + y) / 2 for x, y in zip(cands, cands[1:])]
    w = (0, None)
    for A in pts:
        n = blocks_needed(L, A)
        if n is not None and n > w[0]: w = (n, A)
    return w
def ints(first):
    best = (0, None, None)
    for rest in itertools.combinations(range(first + 1, 17), 5):
        G = (first,) + rest; n, A = worst(G)
        if n > best[0]: best = (n, G, A)
    return best
def climb(seed):
    rng = random.Random(seed); D = 2520
    g = sorted(rng.sample(range(D, 4 * D), 6)); g[0] = D; g = sorted(set(g))
    while len(g) < 6: g = sorted(set(g + [rng.randrange(D + 1, 4 * D)]))
    best = worst(g)[0]
    for step in range(300):
        h = list(g); i = rng.randrange(1, 6); h[i] += rng.choice((-1, 1)) * rng.randrange(1, D // 8)
        h = sorted(h)
        if len(set(h)) < 6 or h[0] != D or h[1] <= D: continue
        n = worst(h)[0]
        if n >= best: g, best = h, n
    return best, [round(x / D, 4) for x in g]
if __name__ == '__main__':
    with Pool(8) as p:
        R = sorted(p.imap_unordered(ints, range(1, 12)), key=lambda x: -x[0])
        print("all 6-sets of readings <= 16: most blocks needed = %d at G = %s, A = %s" % (R[0][0], R[0][1], R[0][2]))
        ext = [(1.0, 1.3746, 1.7628, 2.2539, 2.5123, 3.23), (1.0, 1.3637, 1.7229, 2.2072, 2.4565, 3.1583),
               (1.0, 1.2781, 1.5849, 1.7644, 2.2574, 2.8117), (1.0, 1.2653, 1.4334, 1.5874, 1.7831, 2.2627)]
        for e in ext:
            G = [int(round(x * 10000)) for x in e]; print("extremal rho shape", e, "-> blocks needed", worst(G)[0])
        C = sorted(p.imap_unordered(climb, range(16)), key=lambda x: -x[0])
        for n, g in C[:5]: print("climb: blocks needed %d at %s" % (n, g))
