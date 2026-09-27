"""E156: the regime covering to be stated in Lean, checked exactly before it is stated.  Readings S (whole numbers),
m = least.  Regimes (each proved sufficient in Lean; each instant or window fixed by S, so the covering is not the
conjecture renamed):
  bound:   lonely at R = 1/m                                  (R = 8t)
  first:   for some e in S, lonely at e's first opening after the bound, R = (8K+1)/e, K = least with 8K+1 >= e/m
  block:   for some e in S and K in {1,2,3}, lonely at R = (8K+1)/e
  slow:    split at the largest consecutive gap (slow = readings up to top); for k in {0,1} the window
           R in [(8k+1)/m, (8k+7)/top] contains an R where every fast reading is clear
Populations: Case B (spread in (7,24]) all sets with readings <= 24; Case C: every set with m = 1, readings <= 32,
spread > 24; 20,000 random wide sets; the 547 constructed residual C members.  Protections: progress file, run under
caffeinate by the caller; control: a set known lonely only late must still be covered by a named regime or reported."""
import itertools, random, sys, io, contextlib, os
from fractions import Fraction as F
from math import ceil, exp, log
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set, is_clear
PROG = 'regime_cover_v1.progress'
def regimes(T):
    m = T[0]; hit = []
    if is_clear(T, F(1, m)): hit.append('bound')
    for e in T:
        K = max(0, ceil((F(e, m) - 1) / 8))
        if is_clear(T, F(8 * K + 1, e)): hit.append('first'); break
    if any(is_clear(T, F(8 * K + 1, e)) for e in T for K in (1, 2, 3)): hit.append('block')
    gi = max(range(1, len(T)), key=lambda i: F(T[i], T[i - 1])); top = T[gi - 1]; G = [F(g) for g in T[gi:]]
    for k in (0, 1):
        lo, hi = F(8 * k + 1, m), F(8 * k + 7, top)
        if lo <= hi and clear_set(G, lo, hi): hit.append('slow'); break
    return hit
def caseB(first):
    C = Counter(); U = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1] <= 24 * T[0]): continue
        h = regimes(T); C[tuple(h) if h else ('UNCOVERED',)] += 1
        if not h: U.append(T)
    open(PROG, 'a').write("caseB chunk %d: uncovered %d\n" % (first, len(U)))
    return C, U
def caseC1(second):
    C = Counter(); U = []
    for rest in itertools.combinations(range(second + 1, 33), 5):
        T = (1, second) + rest
        if T[-1] <= 24: continue
        h = regimes(T); C[tuple(h) if h else ('UNCOVERED',)] += 1
        if not h: U.append(T)
    open(PROG, 'a').write("caseC P1 chunk %d: uncovered %d\n" % (second, len(U)))
    return C, U
def caseC2(seed):
    rng = random.Random(seed); C = Counter(); U = []
    for _ in range(2500):
        dmin = rng.randrange(1, 60); S = rng.uniform(25, 2000)
        xs = sorted({max(dmin + 1, int(round(dmin * exp(rng.uniform(0, log(S)))))) for _ in range(5)} | {dmin, int(dmin * S)})
        if len(xs) != 7: continue
        T = tuple(xs); h = regimes(T); C[tuple(h) if h else ('UNCOVERED',)] += 1
        if not h: U.append(T)
    open(PROG, 'a').write("caseC P2 seed %d: uncovered %d\n" % (seed, len(U)))
    return C, U
def summ(name, res):
    C = Counter(); U = []
    for c, u in res: C.update(c); U += u
    cov = sum(v for k, v in C.items() if k != ('UNCOVERED',))
    print("== %s: %d sets, covered %d, uncovered %d" % (name, sum(C.values()), cov, C[('UNCOVERED',)]))
    only = Counter()
    for k, v in C.items():
        if len(k) == 1 and k != ('UNCOVERED',): only[k[0]] += v
    print("   covered by one regime only:", dict(only))
    for T in U[:25]: print("   uncovered:", T)
    return U
if __name__ == '__main__':
    open(PROG, 'w').write("start\n")
    here = os.getcwd(); os.chdir('..')
    with contextlib.redirect_stdout(io.StringIO()):
        g = {}; exec(open('residual_members_C_v1.py').read(), g)
    os.chdir(here)
    with Pool(8) as p:
        UB = summ('Case B, readings <= 24', list(p.imap_unordered(caseB, range(1, 19))))
        UC1 = summ('Case C P1 (m = 1, readings <= 32)', list(p.imap_unordered(caseC1, range(2, 28))))
        UC2 = summ('Case C P2 random wide', list(p.imap_unordered(caseC2, range(8))))
    C3 = Counter(); U3 = []
    for mode in 'AB':
        for S in g['found'][mode]:
            h = regimes(tuple(S)); C3[tuple(h) if h else ('UNCOVERED',)] += 1
            if not h: U3.append(S)
    print("== Case C P3 constructed members: %d, uncovered %d" % (sum(C3.values()), len(U3)))
    open(PROG, 'a').write("ALLDONE\n")
