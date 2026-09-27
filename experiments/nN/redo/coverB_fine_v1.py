"""E159: is CoverB8 (bound or grid class with mm <= 4, c in {1,3,5,7}) true on FINE shapes, or only on readings <= 24?
CoverB8 quantifies over all whole-number sets, all scales.  Populations (denominator 2520 = whole numbers at that scale):
the late band shapes (verified: not lonely anywhere in [1,7]); 5,000 random fine band shapes; 5,000 random fine shapes
with spread in (9, 24].  Least mm (up to 8) per set; the bound regime counted separately.  Protections: progress file,
caffeinate by the caller, control = the Case B integer sample must give mm <= 4 throughout."""
import itertools, random, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set, is_clear
from casec_gridclass_v1 import least_m
PROG = 'coverB_fine_v1.progress'
def classify(T):
    if is_clear(T, F(1, T[0])): return 'bound'
    return least_m(T, 8)
def late_shapes():
    D1 = 27720; rng = random.Random(41); late = set()
    for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
        T = [int(round(x * D1)) for x in sd]
        for step in range(3000):
            U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-500, 501); U = sorted(set(U))
            if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
            if clear_set([F(d, D1) for d in U], F(1), F(7)): continue
            T = U; late.add(tuple(U))
    return sorted(late)
def rand_shapes(seed, lo, hi, n=1250, D=2520):
    rng = random.Random(seed); out = []
    while len(out) < n:
        top = rng.uniform(lo, hi); xs = sorted({D} | {rng.randrange(D + 1, int(top * D)) for _ in range(5)} | {int(top * D)})
        if len(xs) == 7 and 7 * xs[0] < xs[-1]: out.append(tuple(xs))
    return out
def job(args):
    name, sets = args; C = Counter(); U = []
    for T in sets:
        r = classify(T); C[r] += 1
        if r is None or (r != 'bound' and r > 4): U.append(T)
    open(PROG, 'a').write("%s: %s\n" % (name, dict(C)))
    return name, C, U
if __name__ == '__main__':
    open(PROG, 'w').write("start\n")
    samp = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1] <= 24 * T[0]][::400]
    cc = Counter(classify(T) for T in samp)
    open(PROG, 'a').write("control (Case B integer sample): %s\n" % dict(cc))
    if any(k is None or (k != 'bound' and k > 4) for k in cc): sys.exit("CONTROL FAILED")
    L = late_shapes()
    jobs = [('late band shapes part %d' % i, L[i::4]) for i in range(4)]
    jobs += [('random fine band seed %d' % s, rand_shapes(s, 7.0001, 9)) for s in range(4)]
    jobs += [('random fine spread 9-24 seed %d' % s, rand_shapes(100 + s, 9, 24)) for s in range(4)]
    tot = {}
    with Pool(8) as p:
        for name, C, U in p.imap_unordered(job, jobs):
            key = name.rsplit(' ', 2)[0] if 'part' in name or 'seed' in name else name
            key = name.split(' part')[0].split(' seed')[0]
            a = tot.setdefault(key, [Counter(), []]); a[0].update(C); a[1] += U
    for k, (C, U) in tot.items():
        print("%s: %s ; needing mm > 4 or uncovered: %d %s" % (k, sorted(C.items(), key=lambda kv: str(kv[0])), len(U), [tuple(round(x / U0[0], 4) for x in U0) for U0 in U[:5]]))
    open(PROG, 'a').write("ALLDONE\n")
