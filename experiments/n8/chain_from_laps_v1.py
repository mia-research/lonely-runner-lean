"""(1) The chain as the run of overlapping lap-completion zones.  Runner l completes relative lap N at N/d_l and is in the way on
    the open zone (N/d_l - 1/(8 d_l), N/d_l + 1/(8 d_l)).  Sort every zone by its left end; starting at the bound
    b = 1/(8 d_min), take zones in order; while a zone's left end is < the current time and its right end > current time,
    advance to its right end ... equivalently the first time >= b outside the union.  Computed by one pass over the
    sorted list (no re-evaluation).  Compared with the BSM first isolation time.  Also: are the chain's setters in
    increasing order of their lap-completion time N/d?
(2) Drift lines in the AP-deviation frame.  d_l = (a_l + e_l) m, a_l = round(d_l/m).  At the subject's AP instant
    u = K + r/8 (t = (8K+r)/(8m)), runner l sits at  r a_l + (8K+r) e_l  eighths (mod 8); in the way iff within 1 of 8Z.
    For each odd r and each runner the blocked K form explicit intervals; the first lonely AP instant is the least
    (8K+r) outside every runner's intervals.  Compared with direct evaluation of AP instants in order."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor, ceil, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from full_transit_positions_v2 import first_time
def fr(x): return x - floor(x)
def cd(x): x = fr(x); return min(x, 1 - x)
def rnd(x): return floor(x + F(1, 2))
def union_walk(ds, b, horizon):
    zones = []
    for d in ds:
        for N in range(1, int(d * horizon) + 2):
            zones.append((F(N, 1) / d - F(1, 8) / d, F(N, 1) / d + F(1, 8) / d, d, N))
    zones.sort()
    t = b; used = []
    for lo, hi, d, N in zones:
        if lo >= t: break                     # sorted by left end: nothing later can cover t
        if hi > t: t = hi; used.append((d, N))
    return t, used
def setters_chain(ds, m):
    scale = m; seq = []
    while True:
        best = None
        for d in ds:
            s = d / scale; N = rnd(s / 8)
            if abs(s - 8 * N) < 1:
                r = s / (8 * N + 1)
                if best is None or r < best[0]: best = (r, d, N)
        if best is None: return seq
        seq.append((best[1], best[2])); scale *= best[0]
def first_ap_instant_direct(ds, m, cap=600):
    for n in range(1, 8 * cap, 2):
        t = F(n, 8) / m
        if all(cd(d * t) >= F(1, 8) for d in ds): return n
    return None
def first_ap_instant_drift(ds, m, cap=4000):
    """Least odd n = 8K + r outside every runner's blocked set.  Runner l (reading s = a + e) blocks exactly the n in the
    open intervals ((8M - 1)/s, (8M + 1)/s): its drift line n*s passes within 1 of 8M.  One pass over the merged,
    sorted interval list per residue r -- the intervals are listed from (a, e), no instant is evaluated."""
    best = None
    for r in (1, 3, 5, 7):
        iv = []
        for d in ds:
            s = d / m
            for M in range(0, floor(cap * s) + 2):
                iv.append((F(8 * M - 1) / s, F(8 * M + 1) / s))
        iv.sort()
        n = r
        for lo, hi in iv:
            if lo >= n: break
            if hi > n:                                  # n is covered: move to the next n = r mod 8 at or after hi
                k = ceil((hi - r) / 8)
                n = 8 * k + r
                if F(n) == hi: pass                     # zone is open: its right end is clear
        if n < 8 * cap: best = n if best is None or n < best else best
    return best
def job(V):
    out = []
    for i in range(8):
        ds = [abs(V[j] - V[i]) for j in range(8) if j != i]; m = min(ds)
        b = F(1, 8) / m; t_bsm = first_time(V, i)
        t_walk, used = union_walk(ds, b, t_bsm + 1)
        seq = setters_chain(ds, m)
        centres = [F(N) / d for d, N in seq]
        mono = all(centres[k] < centres[k + 1] for k in range(len(centres) - 1))
        nd = first_ap_instant_direct(ds, m); nf = first_ap_instant_drift(ds, m, cap=(nd // 8 + 2) if nd else 60)
        out.append((t_walk == t_bsm, mono, len(seq), nd == nf))
    return out
def run(name, arrs, pool):
    R = [x for r in pool.map(job, arrs, chunksize=8) for x in r]
    print(f"{name}: {len(R)} runners | union walk over sorted lap zones = BSM: {sum(a for a,_,_,_ in R)} | "
          f"chain setters in increasing lap-completion time (chains >= 2): {sum(b for a,b,n,_ in R if n >= 2)} of {sum(1 for a,b,n,_ in R if n >= 2)} | "
          f"drift-line first AP instant = direct: {sum(d for *_, d in R)}")
if __name__ == "__main__":
    rng = random.Random(28); AP = [F(k) for k in range(1, 9)]
    def ok(V): return V if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0 else None
    fams = [("one runner moved, step 0.05", [V for V in (ok([AP[j] + (F(x, 20) - AP[k] if j == k else 0) for j in range(8)]) for k in range(8) for x in range(20 * k + 1, 20 * (k + 2))) if V])]
    L = []
    while len(L) < 200:
        V = ok([AP[j] + F(rng.randint(-90, 90), 100) for j in range(8)])
        if V: L.append(V)
    fams.append(("every runner moved, |dev| <= 0.9 (hundredths)", L))
    fams.append(("all 8-subsets of [1,14], gcd 1", [[F(v) for v in c] for c in combinations(range(1, 15), 8) if reduce(gcd, c) == 1]))
    fams.append(("random integers [1,300]", [[F(v) for v in sorted(rng.sample(range(1, 301), 8))] for _ in range(150)]))
    with Pool(8) as pool:
        for n, a in fams: run(n, a, pool); sys.stdout.flush()
