"""
Own-AP battery.  For each runner i: m = d_min(i) (speed-neighbours); its own ideal AP of gap m based at v_i;
idx_j = round((v_j - v_i)/m), dev_j = (v_j - v_i) - idx_j*m.  Own AP instants: u = m t = k + r/8, r odd.
At such an instant runner j's ideal part sits at idx_j*r/8, so the ideal neighbours are idx*r = +-1 (mod 8).

Framework time = isolation_sets_v1.isolation_set (unchanged): start of the first isolation set.
Recorded per runner:
  on_own     framework time is an own-AP instant
  sig        (if on_own) the runners behind|ahead have idx*r = -1|+1 (mod 8)  [sets, ties kept]
  persists   some own-AP instant within the lap cap is lonely; first_own = the earliest
  fw_eq      framework time == first_own
  setters    (if not on_own) runners exactly at distance 1/8 at the framework time: (idx, deviates?)
"""
import sys, random
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter, defaultdict
from multiprocessing import Pool
import isolation_sets_v1 as iso

E8 = F(1, 8)
LAPCAP = 400
def fr(x): return x - floor(x)
def dist(x): x = fr(x); return min(x, 1 - x)
def rnd(x): return floor(x + F(1, 2))

def runner(V, i, moved=frozenset()):
    n = len(V); m = min(abs(V[j] - V[i]) for j in range(n) if j != i)
    idx = {j: rnd((V[j] - V[i]) / m) for j in range(n) if j != i}
    dev = {j: (V[j] - V[i]) - idx[j] * m for j in idx}
    lonely = lambda t: all(dist((V[j] - V[i]) * t) >= E8 for j in idx)
    _, k, pts, ivs = iso.isolation_set(V, i, lap_cap=LAPCAP)
    if k is None:
        return dict(fw=None)
    t = sorted([p for p in pts] + [a for a, b in ivs])[0]
    u = m * t
    on_own = (8 * u).denominator == 1 and int(8 * u) % 2 == 1
    rel = {j: fr((V[j] - V[i]) * t) for j in idx}
    lo, hi = min(rel.values()), max(rel.values())
    ahead = {j for j in rel if rel[j] == lo}; behind = {j for j in rel if rel[j] == hi}
    sig = None
    if on_own:
        r = int(8 * u) % 8
        sig = all((idx[j] * r) % 8 == 1 for j in ahead) and all((idx[j] * r) % 8 == 7 for j in behind)
    first_own = None
    for a in range(1, 8 * LAPCAP, 2):
        tt = F(a, 8) / m
        if lonely(tt): first_own = tt; break
    setters = [] if on_own else [(idx[j], dev[j] != 0) for j in idx if dist((V[j] - V[i]) * t) == E8]
    role = "moved" if i in moved else ("beside" if any(abs(j - i) == 1 or {i, j} == {0, n - 1} for j in moved) else "away")
    if not moved: role = "all"
    return dict(fw=t, on_own=on_own, sig=sig, persists=first_own is not None, first_own=first_own,
                fw_eq=(first_own == t), setters=setters, role=role, m=m, dm_is_1=(m == 1))

def job(args):
    V, moved = args
    return V, [runner(V, i, moved) for i in range(len(V))]

def report(title, results, show_ex=3):
    c = defaultdict(Counter); ex = defaultdict(list); setc = Counter()
    for V, recs in results:
        for i, x in enumerate(recs):
            if x["fw"] is None:
                c["-"]["framework: no set within lap cap"] += 1; continue
            R = x["role"]; C = c[R]
            C["runners"] += 1
            C["fw time is an own-AP instant"] += x["on_own"]
            C["  ... with the instant's ideal neighbours"] += bool(x["sig"])
            C["lonely at some own-AP instant (persists)"] += x["persists"]
            C["fw time == first lonely own-AP instant"] += x["fw_eq"]
            if not x["on_own"]:
                for s in x["setters"]: setc[("threshold runner deviates", s[1])] += 1
                setc[("number of threshold runners", len(x["setters"]))] += 1
            if x["on_own"] and not x["sig"] and len(ex["neighbours"]) < show_ex:
                ex["neighbours"].append(([str(v) for v in V], i + 1, str(x["fw"])))
            if not x["persists"] and len(ex["no own-AP instant"]) < show_ex:
                ex["no own-AP instant"].append(([str(v) for v in V], i + 1, str(x["fw"])))
    print(f"\n=== {title}")
    for R, C in c.items():
        print(f"  [{R}]")
        for k, v in C.items(): print(f"      {k}: {v}")
    if setc: print("  off-own-AP framework times, runners exactly on the threshold:", dict(setc))
    for k, v in ex.items():
        for e in v: print(f"    e.g. {k}: speeds {e[0]} runner r{e[1]} t={e[2]}")

if __name__ == "__main__":
    rng = random.Random(15)
    offs = [F(s) * F(x, 100) for x in (1, 10, 30, 50, 90) for s in (-1, 1)]
    AP = [F(j + 1) for j in range(8)]
    def build(off):
        V = [AP[j] + off.get(j, 0) for j in range(8)]
        return V if all(V[j] < V[j + 1] for j in range(7)) and V[0] > 0 else None
    fams = []
    fams.append(("B1 one runner moved from the AP (r1..r8, 10 offsets)",
                 [(build({k: e}), frozenset({k})) for k in range(8) for e in offs]))
    fams.append(("B2 two runners moved (every pair, +-0.3)",
                 [(build({a: e1, b: e2}), frozenset({a, b})) for a in range(8) for b in range(a + 1, 8)
                  for e1 in (F(-3, 10), F(3, 10)) for e2 in (F(-3, 10), F(3, 10))]))
    for sc in (F(1, 100), F(1, 10), F(3, 10), F(9, 10)):
        L = []
        while len(L) < 150:
            V = build({j: F(rng.randint(-1000, 1000), 1000) * sc for j in range(8)})
            if V: L.append((V, frozenset()))
        fams.append((f"B3 every runner moved, |dev| <= {sc}", L))
    fams.append(("B4 random integer speeds in [1,100]",
                 [([F(v) for v in sorted(rng.sample(range(1, 101), 8))], frozenset()) for _ in range(300)]))
    fams.append(("B5 all 8-subsets of [1,14], gcd 1",
                 [([F(v) for v in c], frozenset()) for c in combinations(range(1, 15), 8) if reduce(gcd, c) == 1]))
    named = [(1,31,75,97,128,160,176,225), (1,2,3,4,5,6,7,9), (3,7,12,20,29,31,44,50),
             (27,45,308,678,679,799,806,979), (4,12,29,37,101,121,176,196), (1,3,5,9,12,14,16,18)]
    fams.append(("B6 named arrangements", [([F(v) for v in V], frozenset()) for V in named]))
    with Pool(8) as pool:
        for title, L in fams:
            L = [x for x in L if x[0] is not None]
            res = pool.map(job, L, chunksize=8)
            report(title, res)
            sys.stdout.flush()
        print("\nB6 detail:")
        for V, recs in pool.map(job, fams[-1][1]):
            print(" ", [int(v) for v in V])
            for i, x in enumerate(recs):
                print(f"    r{i+1} d_min {x['m']}: fw t={x['fw']} own-AP instant {x['on_own']} ideal-neighbours {x['sig']} | first lonely own-AP instant {x['first_own']} | threshold runners {x['setters']}")
