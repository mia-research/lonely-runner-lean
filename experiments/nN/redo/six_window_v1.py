"""E153: the window lemma the dominant Case C shape needs.  For m readings G (normalised so the least is 1; R = 8 g1 t),
from any start A >= 1 the next instant where every reading is clear at 1/8 is at most rho(G)·A.  rho(G) = sup over A of
(next lonely R >= A)/A, attained at A just after a lonely component ends (or A = 1).  Computed exactly on R in [1, Rmax]
from the lonely set (intersection of clear intervals); beyond Rmax the ratio only matters if a gap is longer, which is
reported.  All 6-sets of readings <= N (and 5-, 4-sets), exact.  Reports the worst rho and its sets."""
import itertools, sys
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
def rho(G, Rmax):
    s = [F(g, G[0]) for g in G]
    L = clear_set(s, F(1), F(Rmax))
    if not L: return None, None
    worst = (L[0][0], F(1))           # from A = 1: first lonely point / 1
    for (a, b), (c, d) in zip(L, L[1:]):
        r = c / b
        if r > worst[0] / worst[1]: worst = (c, b)
    return worst[0] / worst[1], worst
N = int(sys.argv[1]); m = int(sys.argv[2]); RMAX = 200
def chunk(first):
    best = (F(0), None, None)
    for rest in itertools.combinations(range(first + 1, N + 1), m - 1):
        G = (first,) + rest
        r, w = rho(G, RMAX)
        if r is None: return (F(10**9), G, 'no lonely point in [1, Rmax]')
        if r > best[0]: best = (r, G, w)
    return best
if __name__ == '__main__':
    with Pool(8) as p: res = sorted(p.imap_unordered(chunk, range(1, N - m + 2)), key=lambda x: -x[0])
    print("m = %d readings <= %d: worst rho = %s = %.4f at G = %s, component %s" % (m, N, res[0][0], float(res[0][0]), res[0][1], res[0][2]))
    for r in res[1:6]: print("   next: %.4f at %s" % (float(r[0]), r[1]))
