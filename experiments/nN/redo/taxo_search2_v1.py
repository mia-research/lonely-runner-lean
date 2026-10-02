# taxo_search2_v1.py -- K2s1 target: s in (5.4,7] (lap-1 opener needs 7/rho_s < R2 < 9/7), 1-3 strip blockers of laps 1-3, fillers in (1,3).
import random, time
from multiprocessing import Pool
from fractions import Fraction as F
from collections import Counter
from taxo_lib_v1 import *
def qq(x, d=1000): return F(round(x * d), d)
def work(a):
    seed, n = a; rnd = random.Random(seed); c = Counter(); hits = []; nm2 = 0
    for _ in range(n):
        k = rnd.choice((1, 2, 3))
        xs = [F(1), qq(rnd.uniform(5.4, 7.0))] + [F(8 * rnd.randint(1, 3)) + qq(rnd.uniform(-1.0, 1.0)) for _ in range(k)]
        xs += [qq(rnd.uniform(1.05, 3.0)) for _ in range(5 - k)]
        xs = sorted(xs)
        if len(set(xs)) != 7: continue
        lab, o = label_cascade(xs); c[lab] += 1; nm2 += o['nmoves'] >= 2
        if lab in ('K2s1', 'K2a') and len(hits) < 5: hits.append((lab, [str(x) for x in xs]))
    return c, hits, nm2
if __name__ == '__main__':
    t = time.time(); tot = Counter(); hits = []; nm2 = 0
    with Pool(2) as p:
        for c, h, m in p.imap_unordered(work, [(5000 + i, 10000) for i in range(10)]): tot += c; hits += h; nm2 += m
    print("searched", sum(tot.values()), "with nm>=2:", nm2, "seconds", round(time.time() - t)); print(dict(sorted(tot.items()))); print("hits", hits)
