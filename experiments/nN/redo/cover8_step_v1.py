"""E165: the spread-free covering.  Cover8(M): every set of readings is lonely at the bound or at a relocated grid-class
instant of a grid through one of its own readings j with step s_j/mm >= d_min/M (i.e. mm <= M s_j / d_min), class c in
{1,3,5,7} (exact Helly).  M = 4.  Populations: Case B to 24 (all); Case C d_min = 1 readings <= 32 (every 10th set);
the 547 constructed residual C members; random wide 7 < spread <= 2000 (24,000); fine shapes (late band, random fine
band, random fine 9-24).  Least mm is searched upward per (j) and stops at the first success.  Protections: progress
file, caffeinate by the caller, control = Case B sample."""
import itertools, random, sys, io, contextlib, os
from fractions import Fraction as F
from math import exp, log, floor
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import is_clear
from casec_gridclass_v1 import works
from coverB_fine_v1 import late_shapes, rand_shapes
PROG = 'cover8_step_v1.progress'; M = 4
def covered(T):
    s = [F(d) for d in T]
    if is_clear(T, F(1, T[0])): return 'bound'
    best = None
    for j in range(7):
        top = floor(M * F(T[j], T[0]))
        for mm in range(1, top + 1):
            if best is not None and F(T[j], mm) <= best[0]: break      # only need one success; keep the coarsest step found
            if any(works(s, j, mm, c) for c in (1, 3, 5, 7)):
                step = F(T[j], mm)
                if best is None or step > best[0]: best = (step, j, mm)
                break
    return None if best is None else ('grid step/d_min >= %s' % ('1' if best[0] >= T[0] else '1/2' if 2 * best[0] >= T[0] else '1/4'))
def job(args):
    name, sets = args; C = Counter(); U = []
    for T in sets:
        r = covered(tuple(T)); C[r] += 1
        if r is None: U.append(tuple(T))
    open(PROG, 'a').write("%s: %s\n" % (name, dict(C)))
    return name, C, U
def wide(seed, n=1500):
    rng = random.Random(1000 + seed); out = []
    while len(out) < n:
        dmin = rng.randrange(1, 60); S = rng.uniform(7.01, 2000)
        xs = sorted({max(dmin + 1, int(round(dmin * exp(rng.uniform(0, log(S)))))) for _ in range(5)} | {dmin, int(dmin * S)})
        if len(xs) == 7 and xs[-1] > 7 * xs[0]: out.append(tuple(xs))
    return out
if __name__ == '__main__':
    open(PROG, 'w').write("start\n")
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1] <= 24 * T[0]]
    here = os.getcwd(); os.chdir('..')
    with contextlib.redirect_stdout(io.StringIO()):
        g = {}; exec(open('residual_members_C_v1.py').read(), g)
    os.chdir(here)
    P1 = [(1, a) + r for a in range(2, 28) for r in itertools.combinations(range(a + 1, 33), 5) if r[-1] > 24][::10]
    L = late_shapes()
    jobs = [('Case B to 24 part %d' % i, caseB[i::8]) for i in range(8)]
    jobs += [('Case C P1 (every 10th) part %d' % i, P1[i::8]) for i in range(8)]
    jobs += [('Case C constructed members', [tuple(S) for m_ in 'AB' for S in g['found'][m_]])]
    jobs += [('random wide seed %d' % s, wide(s)) for s in range(16)]
    jobs += [('late band shapes', L), ('random fine band', sum((rand_shapes(s, 7.0001, 9) for s in range(4)), [])),
             ('random fine 9-24', sum((rand_shapes(100 + s, 9, 24) for s in range(4)), []))]
    tot = {}
    with Pool(8) as p:
        for name, C, U in p.imap_unordered(job, jobs):
            key = name.split(' part')[0].split(' seed')[0]
            a = tot.setdefault(key, [Counter(), []]); a[0].update(C); a[1] += U
    for k, (C, U) in tot.items():
        print("%s: %d sets; %s; uncovered %d %s" % (k, sum(C.values()), sorted(((str(a), b) for a, b in C.items())), len(U), U[:5]))
    open(PROG, 'a').write("ALLDONE\n")
