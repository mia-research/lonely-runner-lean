"""ok_three_mover_complete_v1 -- the d_min rule over EVERY triple of runners.

n = 8, individual isolation, threshold 1/8, base AP (1,...,8).

Claim under test:

    For a runner disturbed by NONE of the movers, the first isolation is exactly
        t* = 1 / (8 * d_min)
    where d_min is that runner's smallest speed difference.

Previously checked on 5 triples (5,380 of 5,380).  This checks ALL C(8,3) = 56
triples, every runner varied across its own neighbour interval, ordering kept
strict (a runner never reaches or passes another -- at equality the configuration
is really n = 7).

"Disturbed by mover m at speed v" means: in the SINGLE-mover configuration (m at v,
the other seven at AP positions) that runner's first isolation differs from 1/8.

Every failure is recorded in full, not merely counted.
"""
import sys, os, csv, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from ok_full_transit_sweep_v1 import runner_row

AP = [F(x) for x in range(1, 9)]
E  = F(1, 8)

def moments(V):
    out = []
    for i in range(8):
        r = runner_row(V, i)
        out.append(r["windows"][0][0] if r["windows"] else None)
    return out

def dmin(V, i):
    return min(abs(V[i] - V[j]) for j in range(8) if j != i)

_cache = {}
def disturbed(m, v):
    if (m, v) not in _cache:
        V = list(AP); V[m-1] = v
        mm = moments(V)
        _cache[(m, v)] = {i+1 for i in range(8) if mm[i] != E}
    return _cache[(m, v)]

def interval(m, step):
    lo = F(m-1) if m > 1 else F(0)
    hi = F(m+1) if m < 8 else F(9)
    v, out = lo + step, []
    while v < hi:
        if v > 0: out.append(v)
        v += step
    return out

if __name__ == "__main__":
    step = F(1, 4) if len(sys.argv) < 2 else F(sys.argv[1])
    t0 = time.time()
    und = [0, 0]; dis = [0, 0]; fails = []
    for ti, trip in enumerate(itertools.combinations(range(1, 9), 3), 1):
        grids = [interval(m, step) for m in trip]
        n = 0
        for combo in itertools.product(*grids):
            V = list(AP)
            for m, v in zip(trip, combo): V[m-1] = v
            if len(set(V)) < 8 or any(V[k] >= V[k+1] for k in range(7)): continue
            n += 1
            D = set()
            for m, v in zip(trip, combo): D |= disturbed(m, v)
            for i in range(8):
                r = runner_row(V, i)
                if not r["windows"]: continue
                t = r["windows"][0][0]
                pred = E / dmin(V, i)
                tgt = dis if (i+1) in D else und
                tgt[0] += 1
                if t == pred: tgt[1] += 1
                elif (i+1) not in D:
                    fails.append({"triple": str(trip), "speeds": str([str(x) for x in V]),
                                  "runner": i+1, "actual": str(t), "predicted": str(pred),
                                  "d_min": str(dmin(V, i))})
        print(f"  [{ti:>2}/56] {trip}: {n} configurations  "
              f"[undisturbed {und[1]}/{und[0]}]  {time.time()-t0:.0f}s", flush=True)
    print(f"\nstep {step}")
    print(f"  disturbed by NO mover  : {und[1]} of {und[0]}   rate {und[1]/und[0]:.6f}")
    print(f"  disturbed by >= 1      : {dis[1]} of {dis[0]}   rate {dis[1]/dis[0]:.6f}")
    print(f"  failures among undisturbed: {len(fails)}")
    if fails:
        with open("experiments/n8/out_three_mover_failures_v1.csv","w",newline="") as f:
            w=csv.DictWriter(f,fieldnames=list(fails[0].keys())); w.writeheader(); w.writerows(fails)
        for x in fails[:10]: print("   ", x)
