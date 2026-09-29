"""E171 control 2: is the grid-class LAP PATTERN (GridClass8's grid clause, mm <= 4, c unit) a constraint at all at these
R, or would any instant's laps fit?  Random rational instants (NOT required to be lonely), R = 8 m t uniform in each bin;
same membership test as wave_incident_v1.grid_descriptions.  If random instants are covered at the rates the incidents
were, the grid clause carries nothing there and all the content is the pairwise (lonely) test."""
import sys, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from wave_incident_v1 import grid_descriptions, BINS

def work(args):
    sets, seed = args; rng = random.Random(seed); c = Counter()
    for S in sets:
        S = sorted(S); m = S[0]; rank = {d: i for i, d in enumerate(S)}
        for a, b in BINS[:4]:
            R = F(a) + F(rng.randrange(10**6), 10**6) * (b - a)
            t = R / (8 * m)
            c[(a, b, 'n')] += 1; c[(a, b, 'cov')] += bool(grid_descriptions(S, t, rank))
    return c

if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    pops = [('Case B to 24, every 10th', [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::10]),
            ('late band shapes', late_shapes())]
    with Pool(8) as pool:
        for name, sets in pops:
            tot = Counter()
            for c in pool.map(work, [(sets[i::16], i) for i in range(16)]): tot.update(c)
            print(name, ' '.join('R[%d,%d): %d/%d' % (a, b, tot[(a, b, 'cov')], tot[(a, b, 'n')]) for a, b in BINS[:4]))
