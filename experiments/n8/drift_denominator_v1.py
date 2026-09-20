"""Every runner moved from the AP by k/q (|k/q| <= 0.45), for a range of q.  For each runner (own AP frame, exact):
does it have a lonely own-AP instant within one period?  Split: exact slot-sharer present / absent.
Also the reading denominator of each subject's readings (the drift-line period is 8 x that)."""
import sys, random
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from collections import Counter
from multiprocessing import Pool
from drift_sharer_dichotomy_v1 import analyse
if __name__ == "__main__":
    rng = random.Random(30); AP = [F(k) for k in range(1, 9)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    with Pool(8) as pool:
        for q in (2, 3, 4, 5, 6, 8, 10, 12, 16, 25, 50, 97, 211, 1000):
            L = []
            while len(L) < 300:
                V = ok([AP[j] + F(rng.randint(-(45 * q) // 100, (45 * q) // 100), q) for j in range(8)])
                if V: L.append(V)
            R = [x for r in pool.map(analyse, L, chunksize=8) for x in r]
            c = Counter((x["sharer"], x["has"]) for x in R)
            print(f"q = {q:>4}: runners {len(R)} | sharer&no-instant {c[(True,False)]:>4} | sharer&instant {c[(True,True)]} | "
                  f"NO sharer & NO instant {c[(False,False)]:>4} | no sharer & instant {c[(False,True)]:>5}", flush=True)
