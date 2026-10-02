"""E285/E286 (2026-10-02): the named instants of GridNeighbourhoodN beyond the proved radius.  Design: log E285.
Complete grids (residues of the other seven = a permutation of 1..7, D = r + 8N), subject = the slowest (D > 0), deviations eps in
[-rho, rho] grid steps (exact).  gridT = t_A if t_A <= t_B else 7 t_B, t_A = D_A/(8 delta_A), t_B = D_B/(8 delta_B)."""
import sys, os, random
from fractions import Fraction as F
from collections import Counter, defaultdict
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import many_arrangements_v1 as MA
E8 = F(1, 8)
S = 10 ** 6
def nd(x):
    x = x % 1; return min(x, 1 - x)
def one(args):
    Nmax, rho, seed = args; rnd = random.Random(seed); rows = []
    for _ in range(400):
        r = list(range(1, 8)); rnd.shuffle(r)
        D = [r[i] + 8 * rnd.randint(0, Nmax) for i in range(7)]
        if len(set(D)) < 7: continue
        e = [rnd.randint(-int(rho * S), int(rho * S)) for _ in range(7)] if rho else [0] * 7
        T = [D[i] * S + e[i] for i in range(7)]
        if len(set(T)) < 7 or min(T) <= 0: continue
        dl = [F(x, S) for x in T]   # delta_j in grid steps
        iA = next(i for i in range(7) if D[i] % 8 == 1); iB = next(i for i in range(7) if D[i] % 8 == 7)
        tA = F(D[iA]) / (8 * dl[iA]); tB = F(D[iB]) / (8 * dl[iB])
        tg = tA if tA <= tB else 7 * tB
        lonely_g = all(nd(d * tg) >= E8 for d in dl)
        tc, mv, last = MA.cascade(T); tstar = tc * S      # landing in grid units
        lonely_c = all(nd(d * tstar) >= E8 for d in dl)
        W = max(D); eta = max(abs(dl[i] - D[i]) for i in range(7))
        q = float(eta * (14 * W + 21))
        named = tstar in (tA, tB, 7 * tA, 7 * tB)
        rows.append(dict(q=q, lonely_g=lonely_g, lonely_c=lonely_c, eq=(tstar == tg), named=named, earlier=(tstar < tg), later=(tstar > tg), mv=mv, T=tuple(sorted(T)), W=W))
    return Nmax, rho, rows
def qbin(q):
    if q <= 0.5: return '0: q <= 0.5 (inside the proved radius)'
    for i, hi in enumerate((1, 10, 100, 1e3, 1e4, 1e5, 1e6, 1e8)):
        if q <= hi: return '%d: q in (%g, %g]' % (i + 1, (0.5 if i == 0 else (1, 10, 100, 1e3, 1e4, 1e5, 1e6)[i - 1]), hi)
    return '9: q > 1e8'
if __name__ == '__main__':
    out = open('named_instant_v1.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    cells = [(N, rho) for N in (10, 100, 1000, 10000, 10 ** 6) for rho in (0, 0.001, 0.01, 0.1, 0.3, 0.49)]
    with Pool(10) as pool: res = pool.map(one, [(N, rho, 9100 + i) for i, (N, rho) in enumerate(cells)])
    allrows = [(N, rho, r) for N, rho, rows in res for r in rows]
    w("arrangements: %d" % len(allrows))
    w("CHECKS: landing not lonely: %d; landing later than gridT: %d; inside the radius (q <= 0.5) gridT not lonely: %d of %d" % (
        sum(1 for N, p, r in allrows if not r['lonely_c']), sum(1 for N, p, r in allrows if r['later'] and r['lonely_g']),
        sum(1 for N, p, r in allrows if r['q'] <= 0.5 and not r['lonely_g']), sum(1 for N, p, r in allrows if r['q'] <= 0.5)))
    bins = defaultdict(list)
    for N, p, r in allrows: bins[qbin(r['q'])].append(r)
    w("\nby q = eta (14 W + 21):  n | gridT lonely | landing == gridT | landing is a named instant | landing earlier than gridT | max moves")
    for b in sorted(bins):
        rs = bins[b]
        w("  %-42s n %5d | %5d | %5d | %5d | %5d | %d" % (b, len(rs), sum(r['lonely_g'] for r in rs), sum(r['eq'] for r in rs), sum(r['named'] for r in rs), sum(r['earlier'] for r in rs), max(r['mv'] for r in rs)))
    w("\nwhere gridT is not lonely (beyond the radius): first by (Nmax, rho) cell")
    cc = Counter((N, p) for N, p, r in allrows if not r['lonely_g'])
    for k, v in sorted(cc.items()): w("  Nmax %7d rho %-6s: %d of 400" % (k[0], k[1], v))
    w("\nsmallest q with gridT not lonely: %s" % (min((r['q'] for N, p, r in allrows if not r['lonely_g']), default=None),))
    w("largest q with gridT lonely: %s" % (max((r['q'] for N, p, r in allrows if r['lonely_g']), default=None),))
    ex = sorted([(r['q'], N, p, r) for N, p, r in allrows if not r['lonely_g']], key=lambda x: x[0])[:6]
    w("\nthe six arrangements with the least q where gridT is not lonely (landing equal gridT? named? moves):")
    for q, N, p, r in ex: w("  q %.3f Nmax %d rho %s W %d: landing==gridT %s named %s moves %d  T %s" % (q, N, p, r['W'], r['eq'], r['named'], r['mv'], r['T']))
    out.close(); print(open('named_instant_v1.out').read()[len(__doc__):])
