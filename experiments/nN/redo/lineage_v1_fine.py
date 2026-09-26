"""Resolution check for lineage_v1: the first 12 paths (random [1,300]) at grid 300 and grid 3000."""
from multiprocessing import Pool
from lineage_v1 import track
from pinchoff_v1 import targets
if __name__ == '__main__':
    T = [t for t in targets() if t[0].startswith('random')][:12]
    with Pool() as pool:
        for N in (300, 3000):
            res = pool.map(track, [(n, V, N) for n, V in T])
            b = sum(r[2] for r in res); p = sum(r[3] for r in res); h = sum(r[4] for r in res); a = sum(r[5] for r in res)
            print(f"grid {N}: births {b} pinch-offs {p} hand-offs {h} ambiguous {a}; fewest {min(r[6] for r in res)}; "
                  f"event descends from a root on {sum(r[7] for r in res)} of {len(res)}; per path (births, pinches, fewest, descends): "
                  f"{[(r[2], r[3], r[6], r[7]) for r in res]}", flush=True)
