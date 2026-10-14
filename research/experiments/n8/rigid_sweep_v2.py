#!/usr/bin/env python3
"""RIGID sweep, part 2: the prereg's SAMPLED arms (n=9..12), plus a stratum-exhaustive
enumeration of the rigid class.

STAGE `sampled`  -- executes PREREG_RIGID_CLASS_v1.md sec 3 arms 0/1/2 exactly as written.
STAGE `stratum`  -- NOT in the prereg.  Tagged EXPLORATORY in the write-up.  Enumerates
                    every frame tuple satisfying C0&C1&C2&C3 and tests rigidity, which
                    determines the rigid class EXHAUSTIVELY in-frame because those four
                    conditions are proved necessary (RIGID_CLASS_v2.md secs 1-3).
                    Strictly stronger than the sampled arm; reported as a deviation.
"""
import sys, os, json, random
from math import gcd
from functools import reduce
from itertools import combinations
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rigid_sweep_v1 import C1, C2, analyse, want_pts, units, SEED   # SHA pin asserted on import

def C0(T, n): return all(v % n != 0 for v in T)
def C3(T, n): return reduce(gcd, T) == 1
def C0123(T, n): return C0(T, n) and C1(T, n) and C2(T, n) and C3(T, n)

# ------------------------------------------------------------------ stratum
def _strat_chunk(args):
    n, first = args
    hi, out, seen = 4 * n, [], 0
    for rest in combinations(range(first + 1, hi + 1), n - 2):
        T = (first,) + rest
        if not C0123(T, n):
            continue
        seen += 1
        r, pts, ivs = analyse(T, n)
        if r:
            out.append(list(T))
    return seen, out

def stratum(n, pool):
    hi = 4 * n
    jobs = [(n, f) for f in range(1, hi - (n - 3))]
    seen, rig = 0, []
    for s, o in pool.imap_unordered(_strat_chunk, jobs):
        seen += s; rig += o
    return seen, sorted(rig)

# ------------------------------------------------------------------ sampled arms
def _draw_uniform(rng, n):
    return tuple(sorted(rng.sample(range(1, 4 * n + 1), n - 1)))

def _draw_constructive(rng, n):
    hi = 4 * n
    while True:
        S = set()
        ok = True
        for q in range(2, n):
            if any(v % q == 0 for v in S): continue
            c = [m for m in range(q, hi + 1, q) if m not in S]
            if not c: ok = False; break
            S.add(rng.choice(c))
        if not ok or len(S) > n - 1: continue
        for u in sorted(units(n)):
            if any(v % n == u for v in S): continue
            c = [x for x in range(1, hi + 1) if x % n == u and x not in S]
            if not c: ok = False; break
            S.add(rng.choice(c))
        if not ok or len(S) > n - 1: continue
        rest = [x for x in range(1, hi + 1) if x not in S]
        S |= set(rng.sample(rest, n - 1 - len(S)))
        T = tuple(sorted(S))
        if C1(T, n) and C2(T, n): return T

def _rig(T_n):
    T, n = T_n
    r, pts, ivs = analyse(T, n)
    return list(T), r, len(pts), len(ivs)

def sampled(n, arm, pool, target=20000):
    rng = random.Random(SEED + 1000 * n + arm)
    draws, batch = 0, []
    while len(batch) < target:
        if arm == 1:
            batch.append(_draw_constructive(rng, n)); draws += 1
        else:
            T = _draw_uniform(rng, n); draws += 1
            if arm == 0 and C1(T, n) and C2(T, n): batch.append(T)
            elif arm == 2 and (C1(T, n) ^ C2(T, n)): batch.append(T)
    res = list(pool.imap_unordered(_rig, [(T, n) for T in batch], chunksize=200))
    K = sum(1 for T, r, p, i in res if not r)
    R = [T for T, r, p, i in res if r]
    return draws, len(batch), K, R

if __name__ == "__main__":
    stage = sys.argv[1]
    ns = [int(x) for x in sys.argv[2:]]
    with Pool(10) as pool:
        if stage == "stratum":
            out = {}
            for n in ns:
                seen, rig = stratum(n, pool)
                print(f"n={n:>2}  C0&C1&C2&C3 stratum size {seen}  RIGID {len(rig)}", flush=True)
                for T in rig:
                    g = sorted({T[i+1]-T[i] for i in range(len(T)-1)})
                    print(f"      {T}  mod {n}: {sorted({v%n for v in T})}  "
                          f"AP={len(g)==1 and T[0]==g[0]}")
                out[n] = {"stratum": seen, "rigid": rig}
            json.dump(out, open(os.path.join(HERE, f"rigid_stratum_v2_{'_'.join(map(str,ns))}.json"), "w"), indent=1)
        else:
            out = {}
            for n in ns:
                row = {}
                arms = [0, 2] if n in (9, 10) else [1, 2]
                for arm in arms:
                    draws, size, K, R = sampled(n, arm, pool)
                    label = {0: "Arm0 uniform-stratum", 1: "Arm1 constructive",
                             2: "Arm2 near-miss control"}[arm]
                    rate = f"{size/draws:.5f}" if arm == 0 else ("n/a (biased stratum)" if arm == 1 else f"{size/draws:.5f}")
                    print(f"n={n:>2} {label:24} draws={draws:>9} arm={size} "
                          f"K={K} rigid={len(R)} accept-rate={rate}", flush=True)
                    if R: print(f"      RIGID found: {R}")
                    row[label] = {"draws": draws, "arm": size, "K": K, "rigid": R}
                out[n] = row
            json.dump(out, open(os.path.join(HERE, f"rigid_sampled_v2_{'_'.join(map(str,ns))}.json"), "w"), indent=1)
