# taxo_sample_v1.py -- fresh exact sample, cascade label vs independent condition label; 2 processes.
import sys, pickle, random, time
from multiprocessing import Pool
from fractions import Fraction as F
from taxo_lib_v1 import *
def work(args):
    fi, seed, n = args; NS['rnd'].seed(seed); name, f = FAMS[fi]; out = []
    for _ in range(n):
        xs = f(); m = xs[0]; rho = [x / m for x in xs]
        lab, o = label_cascade(rho); lab2, Rs = label_conditions(rho)
        out.append((name, rho, lab, lab2, o['R'] == Rs, o['nmoves'], o['opener'], o['closer'], o['width'], o['R']))
    return out
if __name__ == '__main__':
    N = [(0, 8000), (1, 8000), (2, 6000), (3, 6000), (4, 6000), (5, 6000), (6, 6000), (7, 6000)]
    jobs = []
    for fi, n in N:
        for c in range(n // 1000): jobs.append((fi, 777000 + fi * 100 + c, 1000))
    t = time.time(); rows = []
    with Pool(2) as p:
        for r in p.imap_unordered(work, jobs): rows += r
    print("sample size", len(rows), "seconds", round(time.time() - t))
    pickle.dump(rows, open('taxo_sample_v1.pkl', 'wb'))
