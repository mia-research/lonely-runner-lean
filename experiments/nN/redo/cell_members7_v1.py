# Exact members of tree cells: jitter the LP point at several scales; accept a point only if the exact cascade reproduces the cell's path.
import sys, pickle, random
from fractions import Fraction as F
from multiprocessing import Pool
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
J = int(sys.argv[1]); T = pickle.load(open('terminals7_J%d.pkl' % J, 'rb'))
SC = [0, 1e-12, 1e-10, 1e-9, 1e-8, 1e-7, 1e-6, 1e-5, 1e-4]
def work(i):
    p, lo, hi, rng, w, kind = T[i]; rnd = random.Random(i)
    if w is None: return (i, None, 0)
    tries = 0
    for sc in SC:
        for k in range(1 if sc == 0 else 25):
            tries += 1
            v = [F(x) if sc == 0 else F(x) + F(rnd.uniform(-1, 1) * sc) for x in w]
            rho = [F(1)] + v
            if sorted(rho) != rho or len(set(rho)) < 7: continue
            if outcome(rho)['path'] == tuple(p): return (i, rho, tries)
    return (i, None, tries)
if __name__ == "__main__":
    with Pool(2) as pool: res = pool.map(work, range(len(T)), chunksize=20)
    got = [(i, r) for i, r, t in res if r is not None]
    print("J", J, "cells", len(T), "exact members found", len(got), "missed", len(T) - len(got))
    pickle.dump(got, open('cell_members7_J%d.pkl' % J, 'wb'))
