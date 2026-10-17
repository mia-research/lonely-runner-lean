#!/usr/bin/env python3
"""Phase 3a: the 3/28 failures of o7_kbox_v1 near R1 = (1,3,4,5)/7 and R2 = (1,4,5,6)/7. Box tree (o7_kbox_v1.solve) on
the cube of half-width r around R, for growing T and shrinking WMIN: does the failure set shrink to R as T grows, and
how does the failure radius scale with T?"""
import sys
from multiprocessing import Pool
exec(open("o7_kbox_v1.py").read().split('if __name__')[0])
K = 3 / 28
def job(args):
    R, r, T, WMIN, k = args
    box = [(R[i] - r, R[i] + r) for i in range(4)]
    a, b = box[0]; box[0] = (a + 2 * r * k / 10, a + 2 * r * (k + 1) / 10)
    return solve((box, K, T, WMIN))
if __name__ == "__main__":
    for name, R in (("R1", (1/7, 3/7, 4/7, 5/7)), ("R2", (1/7, 4/7, 5/7, 6/7))):
        for T, WMIN in ((40, 1e-3), (400, 1e-4), (4000, 1e-5)):
            r = 0.01
            with Pool(10) as pool: res = pool.map(job, [(R, r, T, WMIN, k) for k in range(10)])
            leaves = sum(x[0] for x in res); fails = [f for x in res for f in x[1]]
            rad = max((max(max(abs(a - R[i]), abs(b - R[i])) for i, (a, b) in enumerate(f)) for f in fails), default=0)
            print(f"{name} half-width {r}: T = {T}, WMIN = {WMIN}: leaves {leaves}, failed {len(fails)}, "
                  f"max failure distance from R {rad:.2e}", flush=True)
