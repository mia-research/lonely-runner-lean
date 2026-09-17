"""Who sets each move of the COMPLETE_PREDICTOR iteration (unchanged rule)?  Per displaced runner:
  setters  the runner(s) whose next opening is the latest at each move (ties kept)
  same     one runner sets every move
  final    runner(s) at exactly 1/8 at the final time;  final_is_last_setter
  kinds    for the setter at move 1 and the last: slot-sharer (difference = 8q*d_min), speed-neighbour, AP index distance
Families as in complete_predictor_replication_v1 (smaller where large)."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor, ceil, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
def fr(x): return x - floor(x)
def cd(x): x = fr(x); return min(x, 1 - x)
def nxt(d, t):
    k = ceil((8 * d * t - 1) / 8); return F(8 * max(k, 0) + 1, 8 * d)
def trace(V, i):
    D = {j: abs(V[j] - V[i]) for j in range(8) if j != i}; m = min(D.values())
    t = F(1, 8) / m; setters = []
    while True:
        inway = [j for j in D if cd(D[j] * t) < F(1, 8)]
        if not inway: break
        nt = max(nxt(D[j], t) for j in inway)
        setters.append(frozenset(j for j in inway if nxt(D[j], t) == nt)); t = nt
        if len(setters) > 500: return None
    final = frozenset(j for j in D if cd(D[j] * t) == F(1, 8))
    return m, D, setters, final
def kind(i, j, D, m):
    s = D[j] / m
    if s.denominator == 1 and s.numerator % 8 == 0: return "slot-sharer"
    if abs(i - j) == 1: return "speed-neighbour"
    return f"index distance {min(abs(i-j), 8-abs(i-j))}"
def job(V):
    out = []
    for i in range(8):
        r = trace(V, i)
        if r is None or not r[2]: continue
        m, D, S, final = r
        same = len(set(S)) == 1 or bool(frozenset.intersection(*S))
        out.append(dict(moves=len(S), same=same, final_last=bool(final & S[-1]),
                        first=kind(i, min(S[0]), D, m), last=kind(i, min(S[-1]), D, m),
                        changes=sum(1 for a, b in zip(S, S[1:]) if not (a & b))))
    return out
def run(name, arrs, pool):
    R = [x for r in pool.map(job, arrs, chunksize=8) for x in r]
    one = [x for x in R if x["moves"] == 1]; many = [x for x in R if x["moves"] > 1]
    print(f"\n{name}: displaced {len(R)} (one move {len(one)}, several {len(many)})")
    print(f"   final runner at exactly 1/8 is the last move's runner: {sum(x['final_last'] for x in R)}")
    print(f"   several moves, same runner sets every move: {sum(x['same'] for x in many)} of {len(many)}")
    print(f"   several moves, number of setter changes: {dict(sorted(Counter(x['changes'] for x in many).items()))}")
    print(f"   first setter kind: {dict(Counter(x['first'] for x in R).most_common())}")
    print(f"   last setter kind:  {dict(Counter(x['last'] for x in R).most_common())}")
if __name__ == "__main__":
    rng = random.Random(25); AP = [F(k) for k in range(1, 9)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    fams = [("one runner moved, step 0.01", [V for V in (ok([AP[j] + (F(x, 100) - AP[k] if j == k else 0) for j in range(8)]) for k in range(8) for x in range(100 * k + 1, 100 * (k + 2))) if V])]
    L = []
    while len(L) < 600:
        V = ok([AP[j] + F(rng.randint(-900, 900), 1000) for j in range(8)])
        if V: L.append(V)
    fams.append(("every runner moved, |dev| <= 0.9", L))
    fams.append(("all 8-subsets of [1,16], gcd 1", [[F(v) for v in c] for c in combinations(range(1, 17), 8) if reduce(gcd, c) == 1]))
    fams.append(("random integers [1,1000]", [[F(v) for v in sorted(rng.sample(range(1, 1001), 8))] for _ in range(500)]))
    with Pool(8) as pool:
        for n, a in fams: run(n, a, pool); sys.stdout.flush()
