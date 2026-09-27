"""E157: the grid-class regime (grid through reading j at scale s_j/m, class c in {1,3,5,7}, grid points n_i in
{floor, ceil}(m s_i / s_j) with n_i >= 1, lap floor(c n_i / 8) (or one less when c n_i = 0 mod 8), decided exactly by
1-D Helly) on Case C: does the same small m work as the gaps grow?  Least m (<= 8) per set.  Populations: every set with
d_min = 1, readings <= 32, spread > 24; 20,000 random wide; the 547 constructed residual C members.  Protections:
progress file; run under caffeinate; control: Case B to 24's known least-m distribution on a sample must reproduce."""
import itertools, random, sys, io, contextlib, os
from fractions import Fraction as F
from math import floor, ceil, exp, log
from collections import Counter
from multiprocessing import Pool
PROG = 'casec_gridclass_v1.progress'
def works(s, j, m, c):
    lam = F(s[j], m); opts = []
    for x in s:
        o = []
        for n in {floor(x / lam), ceil(x / lam)}:
            if n < 1: continue
            k = (c * n) // 8
            for kk in ((k - 1, k) if (c * n) % 8 == 0 else (k,)):
                if kk >= 0: o.append(kk)
        if not o: return False
        opts.append((x, o))
    cands = sorted({F(8 * k + 1) / x for x, o in opts for k in o})
    return any(all(any(F(8 * k + 1) / x <= R <= F(8 * k + 7) / x for k in o) for x, o in opts) for R in cands)
def least_m(T, M=8):
    s = [F(d) for d in T]
    for m in range(1, M + 1):
        for j in range(7):
            for c in (1, 3, 5, 7):
                if works(s, j, m, c): return m
    return None
def p1(second):
    C = Counter(); U = []
    for rest in itertools.combinations(range(second + 1, 33), 5):
        T = (1, second) + rest
        if T[-1] <= 24: continue
        r = least_m(T); C[r] += 1
        if r is None: U.append(T)
    open(PROG, 'a').write("P1 chunk %d: %s\n" % (second, dict(C)))
    return C, U
def p2(seed):
    rng = random.Random(seed); C = Counter(); U = []
    for _ in range(2500):
        dmin = rng.randrange(1, 60); S = rng.uniform(25, 2000)
        xs = sorted({max(dmin + 1, int(round(dmin * exp(rng.uniform(0, log(S)))))) for _ in range(5)} | {dmin, int(dmin * S)})
        if len(xs) != 7: continue
        T = tuple(xs); r = least_m(T); C[r] += 1
        if r is None: U.append(T)
    open(PROG, 'a').write("P2 seed %d: %s\n" % (seed, dict(C)))
    return C, U
if __name__ == '__main__':
    open(PROG, 'w').write("start\n")
    # control: Case B to 24 sample must give least m in 1..4 for every set (E132: 201,698/8,422/210/5)
    samp = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1] <= 24 * T[0]][::200]
    cc = Counter(least_m(T, 4) for T in samp)
    open(PROG, 'a').write("control Case B sample (%d sets): %s\n" % (len(samp), dict(cc)))
    if None in cc: sys.exit("CONTROL FAILED")
    here = os.getcwd(); os.chdir('..')
    with contextlib.redirect_stdout(io.StringIO()):
        g = {}; exec(open('residual_members_C_v1.py').read(), g)
    os.chdir(here)
    C3 = Counter(least_m(tuple(S)) for m_ in 'AB' for S in g['found'][m_])
    print("P3 constructed members: least m", dict(C3)); sys.stdout.flush()
    with Pool(8) as p:
        for name, fn, rg in (('P2 random wide', p2, range(8)), ('P1 d_min=1 readings<=32', p1, range(2, 28))):
            C = Counter(); U = []
            for c, u in p.imap_unordered(fn, rg): C.update(c); U += u
            print(name, ": least m", sorted(C.items(), key=lambda kv: (kv[0] is None, kv[0] or 0)), "; uncovered (m<=8):", len(U), U[:15]); sys.stdout.flush()
    open(PROG, 'a').write("ALLDONE\n")
