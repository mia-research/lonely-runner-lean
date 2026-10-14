"""Off-own-AP framework times: is u_fw = u0 + (largest requirement at u0), u0 = the latest own-AP instant
k + r/8 (r odd) at or before u_fw, with requirement/room as in BufferRoom_v1.lean?  Also: does that move fit
(largest requirement <= smallest room)?"""
import sys, random
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
import isolation_sets_v1 as iso
E = F(1, 8)
def fr(x): return x - floor(x)
def move(s_list, u0):
    req = F(0); room = None
    for s in s_list:
        ph = fr(s * u0)
        if ph < E: q, R = (E - ph) / s, (7 * E - ph) / s
        elif ph > 1 - E: q, R = (1 + E - ph) / s, (15 * E - ph) / s
        else: q, R = F(0), (7 * E - ph) / s
        req = max(req, q); room = R if room is None else min(room, R)
    return req, room
def job(V):
    out = []
    for i in range(8):
        ds = [abs(V[j] - V[i]) for j in range(8) if j != i]; m = min(ds); s = [d / m for d in ds]
        _, k, pts, ivs = iso.isolation_set(V, i, lap_cap=400)
        if k is None: out.append("no set"); continue
        u = m * sorted(list(pts) + [a for a, b in ivs])[0]
        if (8 * u).denominator == 1 and int(8 * u) % 2: out.append("on own AP"); continue
        a = floor(8 * u); a = a if a % 2 else a - 1
        if a < 1: out.append("before first AP instant"); continue
        u0 = F(a, 8); req, room = move(s, u0)
        if u0 + req == u: out.append("= previous own-AP instant + move" + (" (fits)" if req <= room else " (does not fit?)"))
        else:
            # latest own-AP instant whose move lands exactly on u
            hit = None
            for b in range(a - 2, max(-1, a - 8 * 400), -2):
                q, R = move(s, F(b, 8))
                if F(b, 8) + q == u and q <= R: hit = (a - b) // 2; break
            out.append(f"= an earlier own-AP instant + move ({hit} instants back)" if hit else "not a move from an own-AP instant")
    return V, out
if __name__ == "__main__":
    rng = random.Random(15)
    def dev(sc):
        while True:
            V = [F(j + 1) + F(rng.randint(-1000, 1000), 1000) * sc for j in range(8)]
            if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0: return V
    fams = [(f"every runner moved |dev|<={sc}", [dev(sc) for _ in range(150)]) for sc in (F(1,10), F(3,10), F(9,10))]
    fams.append(("random integers [1,100]", [[F(v) for v in sorted(rng.sample(range(1, 101), 8))] for _ in range(300)]))
    fams.append(("all 8-subsets of [1,14]", [[F(v) for v in c] for c in combinations(range(1, 15), 8) if reduce(gcd, c) == 1]))
    fams.append(("named", [[F(v) for v in V] for V in [(1,31,75,97,128,160,176,225),(1,2,3,4,5,6,7,9),(3,7,12,20,29,31,44,50),(27,45,308,678,679,799,806,979),(4,12,29,37,101,121,176,196),(1,3,5,9,12,14,16,18)]]))
    with Pool(8) as p:
        for name, L in fams:
            c = Counter(x for _, o in p.map(job, L, chunksize=8) for x in o)
            print(f"{name}: {dict(c)}")
