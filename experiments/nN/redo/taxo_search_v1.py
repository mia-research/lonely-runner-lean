# taxo_search_v1.py -- targeted exact searches for the empty classes K2a and K2s1 (cascade label only).
import sys, random, time
from multiprocessing import Pool
from fractions import Fraction as F
from collections import Counter
from taxo_lib_v1 import *
def qq(x, d=200): return F(round(x * d), d)
def gen(rnd, mode):
    if mode == 0:   # general: one strip blocker + one reading in (5,7.5) + fillers over mixed scales
        xs = [F(1), qq(rnd.uniform(5, 7.5)), F(8 * rnd.randint(1, 4)) + qq(rnd.uniform(-1.02, 1.02))]
        xs += [qq(rnd.uniform(1.05, rnd.choice((3, 6, 12, 40)))) for _ in range(4)]
    elif mode == 1: # two or more strip blockers, any laps, plus low fillers
        k = rnd.choice((2, 3, 4)); xs = [F(1)] + [F(8 * rnd.randint(1, 5)) + qq(rnd.uniform(-1.02, 1.02)) for _ in range(k)]
        xs += [qq(rnd.uniform(1.05, rnd.choice((3, 7, 9)))) for _ in range(6 - k)]
    else:           # fully mixed: every reading drawn from a random scale
        xs = [F(1)] + [qq(rnd.uniform(1.05, rnd.choice((2, 4, 8, 9, 17, 25, 33)))) for _ in range(6)]
    xs = sorted(xs)
    return xs if len(set(xs)) == 7 and xs[0] == 1 else gen(rnd, mode)
def work(a):
    seed, mode, n = a; rnd = random.Random(seed); c = Counter(); hits = []
    for _ in range(n):
        xs = gen(rnd, mode); lab, o = label_cascade(xs); c[lab] += 1
        if lab in ('K2a', 'K2s1') and len(hits) < 5: hits.append((lab, [str(x) for x in xs]))
    return mode, c, hits
if __name__ == '__main__':
    jobs = [(900 + 10 * m + i, m, 8000) for m in range(3) for i in range(5)]
    tot = Counter(); bym = {0: Counter(), 1: Counter(), 2: Counter()}; hits = []; t = time.time()
    with Pool(2) as p:
        for m, c, h in p.imap_unordered(work, jobs): tot += c; bym[m] += c; hits += h
    print("searched", sum(tot.values()), "seconds", round(time.time() - t))
    for m in bym: print("mode", m, "n", sum(bym[m].values()), dict(sorted(bym[m].items())))
    print("K2a hits", tot['K2a'], "K2s1 hits", tot['K2s1']); print(hits[:5])
