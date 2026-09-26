"""offgrid_trace_v1, counted against the bound instant R = 1 (the nearest neighbour's first edge)."""
import random
from multiprocessing import Pool
from offgrid_trace_v1 import run
if __name__ == '__main__':
    rnd = random.Random(41)
    Vs = [sorted(rnd.sample(range(1, 200), 8)) for _ in range(60)]
    with Pool() as pool: res = [x for part in pool.map(run, Vs) for x in part]
    fw = [r for r in res if r['kind'] == 'fwd']; bk = [r for r in res if r['kind'] == 'back']
    print(f"forward {len(fw)}: starting at the bound R = 1: {sum(1 for r in fw if abs(r['Rb'] - 1) < 1e-12)}")
    print(f"back {len(bk)}: returning to the bound R = 1: {sum(1 for r in bk if abs(r['Ra'] - 1) < 1e-12)}")
    print(f"forward not from the bound: {[(round(r['Rb'],3), round(r['Ra'],3), r['arriving'], r['relay']) for r in fw if abs(r['Rb']-1) >= 1e-12][:12]}")
    print(f"back not to the bound: {[(round(r['Rb'],3), round(r['Ra'],3), r['opener'], r['closer']) for r in bk if abs(r['Ra']-1) >= 1e-12][:12]}")
