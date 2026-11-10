# E833: window-type certificates (exact Fractions).  For a box rho_i in [n_i/D, (n_i+1)/D] (i = 2..7), a WINDOW TYPE is: the zone (p, jp) whose exit is the left end X of a lonely window (or X = 1), the zone (q, jq) whose entry is the right end Y (or Y = 7), and for every reading i the lap j_i with (8 j_i + 1)/rho_i <= X and Y <= (8 j_i + 7)/rho_i (the window lies in one clear gap of every reading).  All of these are inequalities  A rho_t <= B rho_s  (linear in the readings); if they hold at all 64 corners of the box they hold on the box, and then for every arrangement in the box [X, Y] is a nonempty clear window inside [1, 7]: a lonely instant of W_0, so [1,7] is not carved.  A box is certified when some window type found at some corner holds at all 64 corners.  Uncertified boxes are halved (axis-aligned).  usage: infile(D n0..n5 per line) Dmax [sample]
import sys, itertools
from fractions import Fraction as F
def zones(v):
    z = []
    for i, r in enumerate(v):
        j = 1
        while (8 * j - 1) / r < 7:
            z.append(((8 * j - 1) / r, (8 * j + 1) / r, i, j)); j += 1
    return z
def windows(v):
    """closed clear components of [1,7]: list of (X-desc, Y-desc) with X-desc = (num, idx) meaning num / rho_idx, or (1, None)."""
    z = sorted(zones(v)); out = []
    cur = F(1); curd = (1, None)
    if any(a < 1 < b for a, b, i, j in z):
        a0, b0, i0, j0 = max([t for t in z if t[0] < 1 < t[1]], key=lambda t: t[1]); cur = b0; curd = (8 * j0 + 1, i0)
    for a, b, i, j in z:
        if b <= cur: continue
        if a >= cur and a <= 7:
            out.append((curd, (8 * j - 1, i), cur, a))
        if b > cur: cur = b; curd = (8 * j + 1, i)
    if cur < 7: out.append((curd, (7, None), cur, F(7)))
    return out
def wtype(v, X, Y, xv):
    """the inequality list for the window with left end X-desc, right end Y-desc at the vector v"""
    ineqs = [((1, None), X), (Y, (7, None)), (X, Y)]
    for i, r in enumerate(v):
        j = 0
        while (8 * (j + 1) + 1) / r <= xv: j += 1        # largest j with exit (8j+1)/r <= X
        ineqs.append(((8 * j + 1, i), X)); ineqs.append((Y, (8 * j + 7, i)))
    return ineqs
def holds(ineqs, vertices):
    for (A, s), (B, t) in ineqs:
        for u in vertices:
            rs = u[s] if s is not None else 1; rt = u[t] if t is not None else 1
            if A * rt > B * rs: return False
    return True
def corners(D, n):
    return [tuple(F(n[i] + ((m >> i) & 1), D) for i in range(6)) for m in range(64)]
def certify(D, n):
    V = corners(D, n); tried = set()
    for u in [tuple(F(2 * n[i] + 1, 2 * D) for i in range(6)), V[0], V[63], V[21], V[42]]:
        for X, Y, xv, yv in windows(u):
            ineqs = wtype(u, X, Y, xv)
            k = tuple(ineqs)
            if k in tried: continue
            tried.add(k)
            if holds(ineqs, V): return True
    return False
def sorted_feasible(n):
    x = n[0]
    for i in range(6):
        if n[i] > x: x = n[i]
        if x > n[i] + 1: return False
    return True
def refine(D, n, Dmax, stats):
    stats['nodes'] += 1
    if certify(D, n): stats['cert'][D] = stats['cert'].get(D, 0) + 1; return
    if D >= Dmax: stats['leaves'].append((D, n)); return
    for m in range(64):
        c = tuple(2 * n[i] + ((m >> i) & 1) for i in range(6))
        if sorted_feasible(c): refine(2 * D, c, Dmax, stats)
def work(item):
    D, n, Dmax = item
    stats = {'nodes': 0, 'cert': {}, 'leaves': []}
    refine(D, n, Dmax, stats)
    return stats
if __name__ == '__main__':
    from multiprocessing import Pool
    infile = sys.argv[1]; Dmax = int(sys.argv[2]); sample = int(sys.argv[3]) if len(sys.argv) > 3 else None
    L = []
    for l in open(infile):
        v = [int(x) for x in l.split()]
        if v: L.append((v[0], tuple(v[1:])))
    if sample:
        import random; random.seed(1); L = random.sample(L, min(sample, len(L)))
    with Pool(10) as p: res = p.map(work, [(D, n, Dmax) for D, n in L], chunksize=4)
    nodes = sum(r['nodes'] for r in res); cert = {}; leaves = []
    for r in res:
        for k, v in r['cert'].items(): cert[k] = cert.get(k, 0) + v
        leaves += r['leaves']
    print(infile, '| input leaves', len(L), '| depth cap', Dmax, '| boxes tested', nodes, '| certified by depth D:', sorted(cert.items()), '| uncertified leaves at the cap', len(leaves))
    open(infile.replace('.txt', '') + '_wleaves_%d.txt' % Dmax, 'w').write(''.join('%d %s\n' % (D, ' '.join(map(str, n))) for D, n in leaves))
