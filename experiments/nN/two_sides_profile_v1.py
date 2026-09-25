"""Are the sets the length induction misses genuinely near-AP?  And length against arrival.

On the [1,40] residual: for the 193 sets LEN misses (two_sides_v1) against all the others --
  gap       delta(S) = max_t min_d ||d t||  (1/8 at the AP; the cell length is >= 2(delta - 1/8)/d_max)
  AP fit    least over steps D of max_k |d_k - k D| / D (sorted disparities against D, 2D, ..., 7D)
  first     the first lonely cell (cascade, Theorem 11): its length in units of 1/d_max, the time T
            of first isolation in units of 1/d_min, and the number of cascade moves.
"""
import itertools, os, time, math
from fractions import Fraction as F
from statistics import mean, median
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(HERE, 'two_sides_v1.py')).read().split("if __name__ == '__main__':")[0])
def gap(S):
    bn, bq = 0, 1
    for d, e in itertools.combinations(S, 2):
        for Q in (d + e, e - d):
            for m in range(Q):
                v = min(min(x * m % Q, Q - x * m % Q) for x in S)
                if v * bq > bn * Q: bn, bq = v, Q
    return bn / bq
def apfit(S):
    s = sorted(S)
    return min(max(abs(d - (k + 1) * D) for k, d in enumerate(s)) / D for D in range(1, s[-1] + 1))
def first(S):
    E = F(1, 8)
    def nd(x): x = x % 1; return min(x, 1 - x)
    t = E / min(S); m = 0
    while True:
        way = [d for d in S if nd(d * t) < E]
        if not way: break
        nx = []
        for d in way:
            N = math.floor(d * t - E); o = (N + E) / d
            if o < t: o = (N + 1 + E) / d
            nx.append(o)
        t = max(nx); m += 1
    R = min(((math.ceil(d * t + E) - E) / d if (math.ceil(d * t + E) - E) / d >= t else (math.ceil(d * t + E) + 1 - E) / d) for d in S)
    return float((R - t) * max(S)), float(t * min(S)), m
def job(S):
    return S, LEN(S), gap(S), apfit(S), first(S)
if __name__ == '__main__':
    t0 = time.time()
    R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
    with Pool(4) as pool:
        rows = list(pool.imap_unordered(job, R, chunksize=200))
    for label, sel in (("LEN misses", [r for r in rows if not r[1]]), ("LEN covers", [r for r in rows if r[1]])):
        g = [r[2] for r in sel]; a = [r[3] for r in sel]; ln = [r[4][0] for r in sel]; T = [r[4][1] for r in sel]; mv = [r[4][2] for r in sel]
        print(f"{label} ({len(sel)}): gap median {median(g):.3f} (min {min(g):.3f}, share at exactly 1/8 {sum(abs(x-0.125)<1e-12 for x in g)/len(g):.2f}); "
              f"AP-fit median {median(a):.2f}; first cell length x d_max median {median(ln):.3f} (share one-point {sum(x==0 for x in ln)/len(ln):.2f}); "
              f"first T x d_min median {median(T):.3f}; cascade moves mean {mean(mv):.2f}")
    # length against arrival, over everything
    import collections
    b = collections.defaultdict(list)
    for r in rows: b[min(r[4][2], 6)].append(r[4][0])
    print("cascade moves -> median first-cell length x d_max:", {k: round(median(v), 3) for k, v in sorted(b.items())})
    print(f"({time.time()-t0:.0f}s)")
