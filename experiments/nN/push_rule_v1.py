"""The extended rule: q <= 8, e ANY multiple of q in S, push lap r <= R (instants i/q + (r + 1/8)/e,
i in Z/q), i.e. an opening j of e with j mod (e/q) <= R.  push_depth_v1: R = 2 certifies every hard
set with largest 41..60.  Here: the 28 hard sets of [1,40], and the hard sets of the structured
families of hard_search_v1 (largest up to 150), with the least R each needs.
"""
import itertools, json, os, time
from multiprocessing import Pool
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
_rs = os.path.join(HERE, 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def lonely(S, e, j): return all(e <= d * (8 * j + 1) % (8 * e) <= 7 * e for d in S)
def least_R(S):
    best = None
    for q in range(2, 9):
        for e in S:
            if e % q: continue
            M = e // q
            for r in range(M if best is None else min(M, best)):
                if any(lonely(S, e, i * M + r) for i in range(q)):
                    best = r; break
    return best
def hard(S): return eight_residual(S) and not any(rule(S, q, free_exact) for q in range(2, 9))
def family(args):
    small, lo, hi, k = args
    return [small + big for big in itertools.combinations(range(lo, hi + 1), k) if hard(small + big)]

if __name__ == '__main__':
    t0 = time.time()
    R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
    H40 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 9))]
    c = Counter(least_R(S) for S in H40)
    print(f"[1,40] hard sets {len(H40)}: least push lap {sorted((k if k is not None else -1, v) for k, v in c.items())}  ({time.time()-t0:.0f}s)", flush=True)
    jobs = [(s, 17, 150, 2) for s in itertools.combinations(range(1, 17), 5)] + \
           [(s, 13, 100, 3) for s in itertools.combinations(range(1, 13), 4)]
    with Pool(4) as pool:
        H2 = sorted({S for out in pool.imap_unordered(family, jobs, chunksize=8) for S in out if max(S) > 60})
    c = Counter(least_R(S) for S in H2); none = [S for S in H2 if least_R(S) is None]
    print(f"family hard sets with largest 61..150: {len(H2)}; least push lap {sorted((k if k is not None else -1, v) for k, v in c.items())}; "
          f"none {len(none)} {none[:6]}  ({time.time()-t0:.0f}s)", flush=True)
    worst = sorted(H2, key=lambda S: -(least_R(S) or 0))[:6]
    print("   the sets needing the deepest push:", [(S, least_R(S)) for S in worst])
