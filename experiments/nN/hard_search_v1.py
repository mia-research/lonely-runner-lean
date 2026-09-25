"""Targeted search for the hard sets of the order-eight residual beyond [1,40], and the two
dichotomies on them.

A hard set is in the v1 residual (eight_residual) and fails the rung-selection rule at every q <= 8
(rung_selection_v1).  pair_moduli_v1/v2 found, on [1,40]:
  D1: q <= 8, or the largest flank has a lonely opening (Theorem 10 at the largest disparity);
  D2: q <= 8, or some instant k/(a+b) is lonely, a < b the two largest (the mirror of the top pair);
with no exception, but random sampling beyond 40 almost never reaches a hard set.  Here:
  Part 1: EVERY 7-set with largest element 41..SEARCH_TOP (exhaustive, split by the largest element).
  Part 2: structured families reaching further, in the shape of the 28 hard sets of [1,40]:
          five from [1,16] with two from [17,150]; four from [1,12] with three from [13,100].
Reported: hard sets found, and every hard set failing D1 or D2 (a counterexample to the pattern).
"""
import itertools, sys, time
from multiprocessing import Pool
from collections import Counter
SEARCH_TOP = int(sys.argv[1]) if len(sys.argv) > 1 else 60   # read first: the exec'd sources reset sys.argv
_rs = __file__.replace('hard_search_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])


def largest_flank_ok(S):
    D = max(S)
    return any(all(D <= d * (8 * j + 1) % (8 * D) <= 7 * D for d in S) for j in range(D))
def mirror_top_ok(S):
    b, a = sorted(S, reverse=True)[:2]; q = a + b
    return any(all(q <= 8 * (d * k % q) <= 7 * q for d in S) for k in range(1, q))
def hard(S): return eight_residual(S) and not any(rule(S, q, free_exact) for q in range(2, 9))

def by_largest(D):
    n = h = 0; out = []
    for c in itertools.combinations(range(1, D), 6):
        S = c + (D,)
        if eight_residual(S):
            n += 1
            if not any(rule(S, q, free_exact) for q in range(2, 9)): out.append(S)
    return D, n, out

def family(args):
    small, lo, hi, k = args
    out = []; n = 0
    for big in itertools.combinations(range(lo, hi + 1), k):
        S = small + big
        if eight_residual(S):
            n += 1
            if not any(rule(S, q, free_exact) for q in range(2, 9)): out.append(S)
    return n, out

def judge(H, label):
    d1 = [S for S in H if not largest_flank_ok(S)]
    d2 = [S for S in H if not mirror_top_ok(S)]
    both = [S for S in H if S in d1 and S in d2]
    print(f"{label}: hard sets {len(H)}; D1 fails {len(d1)} {d1[:6]}; D2 fails {len(d2)} {d2[:6]}; both fail {len(both)} {both[:6]}", flush=True)
    return d1, d2

if __name__ == '__main__':
    t0 = time.time()
    with Pool(4) as pool:
        H1 = []; tot = 0
        for D, n, out in pool.imap_unordered(by_largest, range(SEARCH_TOP, 40, -1)):
            tot += n; H1 += out
            print(f"  largest {D}: residual {n}, hard {len(out)}  ({time.time()-t0:.0f}s)", flush=True)
        print(f"Part 1, every 7-set with largest 41..{SEARCH_TOP}: residual {tot}", flush=True)
        judge(H1, "Part 1")
        print("  hard sets:", sorted(H1), flush=True)
        H2 = set(); tot = 0
        jobs = [(s, 17, 150, 2) for s in itertools.combinations(range(1, 17), 5)] + \
               [(s, 13, 100, 3) for s in itertools.combinations(range(1, 13), 4)]
        for n, out in pool.imap_unordered(family, jobs, chunksize=8):
            tot += n; H2.update(out)
        H2 = sorted(S for S in H2 if max(S) > SEARCH_TOP)
        print(f"Part 2, families (5 of [1,16] + 2 of [17,150]; 4 of [1,12] + 3 of [13,100]): residual {tot}; "
              f"hard with largest > {SEARCH_TOP}: {len(H2)}  ({time.time()-t0:.0f}s)", flush=True)
        judge(H2, "Part 2")
        print("  hard sets (first 40):", H2[:40], flush=True)
        print("  largest elements of the Part 2 hard sets:", sorted(Counter(max(S) for S in H2).items()), flush=True)
    print(f"total {time.time()-t0:.0f}s")
