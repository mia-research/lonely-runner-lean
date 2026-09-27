"""E124: exact covering of the band polytope by lap-assignment cones, cut only along walls.
Band: s0 = 1 <= s1 <= ... <= s6, 7 <= s6 <= 9 (variables x_i = s_{i+1} - 1 >= 0).
Cone of laps k = (k0..k6): (8 k_i + 1) s_j <= (8 k_j + 7) s_i for all i != j  (TwoBlockN.lonely_eight_of_pairwise_laps:
every shape in it is lonely at R = max_i (8k_i+1)/s_i, in the slowest runner's block k0).
Recursion: piece P -> interior point (max slack) -> a cone containing it (witness: add the point's categories) ->
P inside the cone? leaf.  Else split P \\ cone along the cone's violated walls.  Exact LP (exact_lp.py)."""
import sys, json, time, re
from fractions import Fraction as F
from multiprocessing import Pool
from exact_lp import lp_max
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
NV = 6
BASE = [([1 if j == i else (-1 if j == i + 1 else 0) for j in range(NV)], F(0)) for i in range(NV - 1)]
BASE += [([0] * 5 + [1], F(8)), ([0] * 5 + [-1], F(-6))]
def cone_rows(k):
    rows = []
    for i in range(7):
        for j in range(7):
            if i == j: continue
            a = [0] * NV; rhs = F((8 * k[j] + 7) - (8 * k[i] + 1))
            if j >= 1: a[j - 1] += 8 * k[i] + 1
            if i >= 1: a[i - 1] -= 8 * k[j] + 7
            if all(v == 0 for v in a):
                if rhs < 0: rows.append((a, rhs))
                continue
            rows.append((a, rhs))
    return rows
def load_cones():
    C = []
    for line in open('band_category_cover_v1.out'):
        m = re.search(r'laps (\S+|\([^)]*\))\s+newly', line)
        if m:
            t = m.group(1); C.append(tuple(int(x) for x in (t.strip('()').split(', ') if t.startswith('(') else t)))
    return C
def interior(P):
    A = [a + [1] for a, b in P]; b = [r for a, r in P]
    res = lp_max(A, b, [0] * NV + [1])
    if res[0] != 'opt': return None, None
    return res[2][:NV], res[1]
def inside(s, k):
    return all((8 * k[i] + 1) * s[j] <= (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
def cats(s):
    out = []
    for lo, hi in [(F(1), F(7)), (F(9), F(15))]:
        for a, b in clear_set(s, lo, hi):
            m = (a + b) / 2; out.append(tuple(int(x * m // 8) for x in s))
    return out
def process(args):
    P, cones = args
    feas = lp_max([a for a, b in P], [b for a, b in P], [0] * NV)
    if feas[0] == 'infeasible': return ('empty', None, [], [])
    x, tau = interior(P)
    if x is None: x = feas[2]
    s = [F(1)] + [F(1) + v for v in x]
    k = next((c for c in cones if inside(s, c)), None); new = []
    if k is None:
        new = [c for c in cats(s) if inside(s, c)]
        if not new: return ('HOLE', [str(v) for v in s], [], [])
        k = new[0]
    viol = []
    for a, rhs in cone_rows(k):
        r = lp_max([aa for aa, bb in P], [bb for aa, bb in P], a)
        if r[0] == 'opt' and r[1] > rhs: viol.append((a, rhs))
    if not viol: return ('in', k, [], new)
    children = []; acc = []
    for a, rhs in viol:
        children.append(P + acc + [([-v for v in a], -rhs)])
        acc = acc + [(a, rhs)]
    return ('split', k, children, new)
if __name__ == '__main__':
    cones = load_cones(); frontier = [BASE]; stats = {'in': 0, 'empty': 0, 'split': 0, 'HOLE': 0}; used = set()
    t0 = time.time(); wave = 0
    with Pool(10) as pool:
        while frontier:
            wave += 1
            res = pool.map(process, [(P, cones) for P in frontier], chunksize=1)
            nxt = []
            for kind, k, ch, new in res:
                stats[kind] += 1
                for c in new:
                    if c not in cones: cones.append(c)
                if kind == 'HOLE': print("HOLE (no category at this point):", k); sys.stdout.flush()
                if kind in ('in', 'split'): used.add(tuple(k))
                nxt += ch
            frontier = nxt
            print("wave %d: frontier %d  stats %s  cones %d  used %d  %.0fs" % (wave, len(frontier), stats, len(cones), len(used), time.time() - t0)); sys.stdout.flush()
    print("DONE", stats, "cones used", len(used))
    json.dump(sorted(used), open('band_cones_used_v1.json', 'w'))
