"""E152: Case C (spread > 24) through the cascade, with the regime of E151: split at the largest consecutive gap into
S (slow) and G (fast); at the landing, is S on one lap k, and is the landing G's own first point from the start of S's
common block on lap k, R_start = (8k+1)/s_min(S)?  The room: where in that block G arrives, as a fraction of the block
(R* - start)/(end - start), end = (8k+7)/s_top(S).  Populations: (P1) every set with d_min = 1, readings <= 32, spread
> 24; (P2) 20,000 random wide sets (spread 25..2000, log-uniform readings); (P3) the constructed Case C residual members
(E118).  Exact."""
import itertools, random, sys, io, contextlib
from fractions import Fraction as F
from math import floor, exp, log
from collections import Counter
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def casc(T, t):
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def analyse(T):
    T = tuple(sorted(T)); t0 = F(1, 8 * T[0]); ts = casc(T, t0)
    if ts == t0: return ('at the bound',)
    gi = max(range(1, 7), key=lambda i: F(T[i], T[i - 1])); S = T[:gi]; G = T[gi:]
    laps = {floor(s * ts) for s in S}
    if len(laps) > 1: return ('S split over laps at the landing', '|S| = %d' % len(S))
    k = laps.pop(); start = F(8 * k + 1, 8) / S[0]; end = F(8 * k + 7, 8) / S[-1]
    own = casc(G, start) == ts
    frac = (ts - start) / (end - start) if end > start else None
    fb = 'room used: n/a' if frac is None else 'room used %s' % ('<1/4' if frac < F(1, 4) else '<1/2' if frac < F(1, 2) else '<3/4' if frac < F(3, 4) else '>=3/4')
    return ('S on one lap (k=%s)' % (k if k < 3 else '>=3'), "G's own first point from the block start" if own else 'G delayed inside the block', '|S| = %d' % len(S), fb)
def chunk1(second):
    C = Counter(); mx = F(0)
    for rest in itertools.combinations(range(second + 1, 33), 5):
        T = (1, second) + rest
        if T[-1] <= 24: continue
        C[analyse(T)] += 1
    return C
def p2(seed):
    rng = random.Random(seed); C = Counter()
    for _ in range(2500):
        dmin = rng.randrange(1, 60); S = rng.uniform(25, 2000)
        xs = sorted({max(dmin + 1, int(round(dmin * exp(rng.uniform(0, log(S)))))) for _ in range(5)} | {dmin, int(dmin * S)})
        if len(xs) != 7: continue
        C[analyse(tuple(xs))] += 1
    return C
if __name__ == '__main__':
    import os
    here = os.getcwd(); os.chdir('..')
    with contextlib.redirect_stdout(io.StringIO()):
        g = {}; exec(open('residual_members_C_v1.py').read(), g)
    os.chdir(here)
    with Pool(8) as p:
        C1 = Counter()
        for c in p.imap_unordered(chunk1, range(2, 28)): C1.update(c)
        C2 = Counter()
        for c in p.imap_unordered(p2, range(8)): C2.update(c)
    C3 = Counter(analyse(S) for m in 'AB' for S in g['found'][m])
    for name, C in (('P1 d_min=1, readings <= 32, spread > 24', C1), ('P2 random wide', C2), ('P3 constructed residual C members', C3)):
        print("==", name, "(%d sets)" % sum(C.values()))
        for k, v in sorted(C.items(), key=lambda kv: -kv[1]): print("  %7d  %s" % (v, k))
