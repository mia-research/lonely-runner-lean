"""
AP deformation series.  Reference AP (1,...,8); runner labels = AP indices 1..8.
Every runner's isolation time is the framework's own (isolation_sets_v1.isolation_set, unchanged):
d_min from speed-neighbours, lap-by-lap window, BSM.  Nothing else searches for times.

Per runner we record
  t        start of the framework's first isolation set
  phase    if 8t is an odd integer, 8t mod 8 (an AP global instant), else None
  sides    labels of the runners behind | ahead at t (ties kept as sets)
  ap_sig   whether sides equal the AP's neighbours for that phase: +-1 at phase 1,7; +-3 at 3,5
  pred     for unmoved runners: the least odd-eighth instant at which every moved runner is >= 1/8 away
Roles: 'moved', 'beside' (AP index +-1 of a moved runner, cyclic), 'away'.
"""
import sys, random
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
from fractions import Fraction as F
from math import floor
from collections import Counter, defaultdict
from multiprocessing import Pool
import isolation_sets_v1 as iso

E8 = F(1, 8)
def fr(x): return x - floor(x)
def dist(x): x = fr(x); return min(x, 1 - x)

def sides(V, i, t):
    rel = {j: fr((V[j] - V[i]) * t) for j in range(8) if j != i}
    a, b = min(rel.values()), max(rel.values())
    return frozenset(j for j in rel if rel[j] == b), frozenset(j for j in rel if rel[j] == a)

def ap_neighbours(i, phase):
    c = 1 if phase in (1, 7) else 3
    return {(i - c) % 8, (i + c) % 8}

def predicted(V, i, moved):
    """least odd-eighth t (any lap) with every other runner clear; unmoved runners are always clear there
    unless they share the subject's AP slot, so in effect: every moved runner clear."""
    for a in range(1, 8 * 400, 2):
        t = F(a, 8)
        if all(dist((V[j] - V[i]) * t) >= E8 for j in range(8) if j != i):
            return t
    return None

def runner_record(V, i, moved):
    m, k, pts, ivs = iso.isolation_set(V, i)
    ev = sorted([(p, p) for p in pts] + list(ivs))
    t = ev[0][0]
    ph = int(8 * t) % 8 if (8 * t).denominator == 1 and int(8 * t) % 2 == 1 else None
    b, a = sides(V, i, t)
    ap_sig = ph is not None and {min(b), min(a)} == ap_neighbours(i, ph) and len(b) == 1 and len(a) == 1
    if i in moved: role = "moved"
    elif any((i - j) % 8 in (1, 7) for j in moved): role = "beside"
    else: role = "away"
    pred = predicted(V, i, moved) if i not in moved else None
    return dict(i=i, t=t, phase=ph, behind=b, ahead=a, ap_sig=ap_sig, role=role, pred=pred,
                pred_ok=(pred == t) if pred is not None else None)

def arrangement(args):
    offsets, = args
    V = [F(j + 1) + offsets.get(j, F(0)) for j in range(8)]
    if not all(V[j] < V[j + 1] for j in range(7)) or V[0] <= 0:
        return None
    moved = {j for j, e in offsets.items() if e != 0}
    return V, [runner_record(V, i, moved) for i in range(8)]

def summarise(title, results):
    c = defaultdict(Counter); ex = defaultdict(list)
    for r in results:
        if r is None: continue
        V, recs = r
        for x in recs:
            role = x["role"]; c[role]["runners"] += 1
            c[role]["at an AP instant"] += x["phase"] is not None
            c[role]["AP instant with that event's AP neighbours"] += x["ap_sig"]
            if x["pred"] is not None:
                c[role]["time = predicted odd-eighth instant"] += x["pred_ok"]
            if role != "moved" and not x["ap_sig"] and len(ex[role]) < 4:
                ex[role].append(([str(v) for v in V], f"r{x['i']+1}", str(x["t"]), x["phase"],
                                 "/".join(f"r{j+1}" for j in sorted(x["behind"])) + "|" +
                                 "/".join(f"r{j+1}" for j in sorted(x["ahead"]))))
    print(f"\n=== {title}")
    for role in ("away", "beside", "moved"):
        if c[role]: print(f"  {role:>6}: {dict(c[role])}")
    for role in ("away", "beside"):
        for e in ex[role]: print(f"     {role} exception: speeds {e[0]} {e[1]} t={e[2]} phase={e[3]} sides {e[4]}")

OFFS = [F(s) * F(x, 100) for x in (1, 10, 30, 50, 90) for s in (-1, 1)]

if __name__ == "__main__":
    with Pool(8) as pool:
        # E1: one runner moved
        jobs = [({k: e},) for k in range(8) for e in OFFS]
        res = pool.map(arrangement, jobs)
        summarise("E1 one runner moved (each of r1..r8, offsets +-0.01 +-0.1 +-0.3 +-0.5 +-0.9)", res)
        print("\n  E1 detail, per moved runner: runners NOT at an AP instant with that event's AP neighbours")
        for (off,), r in zip(jobs, res):
            if r is None: continue
            V, recs = r
            k, e = next(iter(off.items()))
            bad = [f"r{x['i']+1}" + ("" if x["role"] == "moved" else f"({x['role']})") for x in recs if not x["ap_sig"]]
            ph = {f"r{x['i']+1}": x["phase"] for x in recs if x["role"] == "beside"}
            print(f"    move r{k+1} by {str(e):>7}: not AP-event: {bad}   beside-runner phases {ph}")
        # E2: two runners moved
        jobs = [({k1: e1, k2: e2},) for k1 in range(8) for k2 in range(k1 + 1, 8)
                for e1 in (F(-3, 10), F(3, 10)) for e2 in (F(-3, 10), F(3, 10))]
        summarise("E2 two runners moved (every pair, offsets +-0.3 each)", pool.map(arrangement, jobs))
        # E3: every runner moved, random
        rng = random.Random(14)
        for scale in (F(1, 100), F(1, 10), F(3, 10)):
            jobs = []
            while len(jobs) < 120:
                off = {j: F(rng.randint(-1000, 1000), 1000) * scale for j in range(8)}
                jobs.append((off,))
            summarise(f"E3 every runner moved, |dev| <= {scale} (120 arrangements; roles all 'moved')",
                      pool.map(arrangement, jobs))
