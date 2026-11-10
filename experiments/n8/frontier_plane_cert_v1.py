# E833: window-type certificates on a box split by tie planes (exact Fractions).  The planes are the zero sets of the exact cycle identities of E830/E832:  h1 = rho7 - 7 rho5  (links rho7 lap 6 -> rho5 lap 1 and rho5 lap 3 -> rho7 lap 22: 25(49 rho5 - 7 rho7) + 7(25 rho7 - 175 rho5) = 0)  and  h2 = 3 rho6 - 5 rho4  (links rho4 lap 1 -> rho6 lap 2 and rho6 lap 3 -> rho4 lap 2: (5/3)(9 rho6 - 15 rho4) + (25 rho4 - 15 rho6) = 0).
# A polytope P (a set of points whose hull is P) is certified when some window type found at a point of P holds at all points; otherwise P is split by a plane that takes both signs on it, and both sides must be certified (each side's points: the points of one sign plus the intersections of segments between points of opposite sign).  A box not certified is halved.  usage: infile Dmax
import sys, itertools
from fractions import Fraction as F
exec(open('frontier_window_cert_v1.py').read().split("def sorted_feasible")[0])
PLANES = [(0, 0, 0, -7, 0, 1), (0, 0, -5, 0, 3, 0)]
def hval(h, u): return sum(F(c) * x for c, x in zip(h, u))
def sides(P, h):
    pos = [u for u in P if hval(h, u) >= 0]; neg = [u for u in P if hval(h, u) <= 0]
    cross = []
    pp = [u for u in P if hval(h, u) > 0]; nn = [u for u in P if hval(h, u) < 0]
    for a in pp:
        for b in nn:
            ha, hb = hval(h, a), hval(h, b); t = ha / (ha - hb)
            cross.append(tuple(x + t * (y - x) for x, y in zip(a, b)))
    return pos + cross, neg + cross
def cert_poly(P, planes, depth=0):
    cands = [tuple(sum(u[i] for u in P) / len(P) for i in range(6))] + P[:: max(1, len(P) // 6)]
    tried = set()
    for u in cands:
        for X, Y, xv, yv in windows(u):
            ineqs = wtype(u, X, Y, xv); k = tuple(ineqs)
            if k in tried: continue
            tried.add(k)
            if holds(ineqs, P): return True
    if depth >= 2: return False
    for idx, h in enumerate(planes):
        vals = [hval(h, u) for u in P]
        if min(vals) < 0 < max(vals):
            A, B = sides(P, h); rest = planes[:idx] + planes[idx + 1:]
            if cert_poly(A, rest, depth + 1) and cert_poly(B, rest, depth + 1): return True
    return False
def sorted_feasible(n):
    x = n[0]
    for i in range(6):
        if n[i] > x: x = n[i]
        if x > n[i] + 1: return False
    return True
def refine(D, n, Dmax, stats):
    stats['nodes'] += 1
    V = corners(D, n)
    if cert_poly(V, PLANES): stats['cert'][D] = stats['cert'].get(D, 0) + 1; return
    if D >= Dmax: stats['leaves'].append((D, n)); return
    for m in range(64):
        c = tuple(2 * n[i] + ((m >> i) & 1) for i in range(6))
        if sorted_feasible(c): refine(2 * D, c, Dmax, stats)
def work(item):
    D, n, Dmax = item
    stats = {'nodes': 0, 'cert': {}, 'leaves': []}
    refine(D, n, Dmax, stats); return stats
if __name__ == '__main__':
    from multiprocessing import Pool
    infile = sys.argv[1]; Dmax = int(sys.argv[2])
    L = []
    for l in open(infile):
        v = [int(x) for x in l.split()]
        if v: L.append((v[0], tuple(v[1:])))
    with Pool(10) as p: res = p.map(work, [(D, n, Dmax) for D, n in L], chunksize=2)
    nodes = sum(r['nodes'] for r in res); cert = {}; leaves = []
    for r in res:
        for k, v in r['cert'].items(): cert[k] = cert.get(k, 0) + v
        leaves += r['leaves']
    print(infile, '| input leaves', len(L), '| depth cap', Dmax, '| boxes tested', nodes, '| certified by depth D:', sorted(cert.items()), '| uncertified leaves at the cap', len(leaves))
    open(infile.replace('.txt', '') + '_pleaves_%d.txt' % Dmax, 'w').write(''.join('%d %s\n' % (D, ' '.join(map(str, n))) for D, n in leaves))
