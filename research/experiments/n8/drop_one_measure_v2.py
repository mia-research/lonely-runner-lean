#!/usr/bin/env python3
"""Sharpen the drop-one reduction from MEASURE to COMPONENT LENGTH.

The dropped speed v has bad set  B(v) = {t : ||tv|| < 1/8}  =  v disjoint intervals of
length 1/(4v), at period 1/v, separated by gaps of length 3/(4v) > 0.

So if C is a CONNECTED COMPONENT of L6 and C is covered by v, then C lies inside a SINGLE
bad interval, hence |C| <= 1/(4v).  Taking lambda = max component length of L6:

        LEMMA.  If T = T6 u {v} is a counterexample-candidate for LRC(8), then
                v <= 1/(4*lambda(T6)).                                    [PROVED]

The measure test |L6| > 1/4 is the weak shadow of this: it ignores where the mass sits.
Same frame as v1: all C(24,6) six-subsets of [1,24], level 1/8, exact rationals.
Reports the distribution of the bound B = floor(1/(4*lambda)) over the frame, and its max.
"""
import sys, os, io, contextlib
from fractions import Fraction as F
from itertools import combinations
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
with contextlib.redirect_stdout(io.StringIO()):
    from exact_phi_n_ap_v1 import lonely_set

M, K, LEVEL = 24, 6, 8

def merged_components(T):
    """Exact components of L6, adjacent BSM cells merged (BSM emits cell-by-cell)."""
    pts, ivs = lonely_set(list(T), LEVEL)
    out = []
    for a, c in sorted(ivs):
        if out and a <= out[-1][1]:
            out[-1][1] = max(out[-1][1], c)
        else:
            out.append([a, c])
    return out

def job(first):
    rows = []
    for rest in combinations(range(first + 1, M + 1), K - 1):
        T = (first,) + rest
        comp = merged_components(T)
        if not comp:
            rows.append((T, None, None)); continue        # L6 has no interval at all
        lam = max(c - a for a, c in comp)
        rows.append((T, lam, (1 // (4 * lam)) if lam else None))
    best = max((r for r in rows if r[1] is not None), key=lambda r: r[2], default=None)
    worst_lam = min((r[1] for r in rows if r[1] is not None), default=None)
    empty = sum(1 for r in rows if r[1] is None)
    bs = [r[2] for r in rows if r[2] is not None]
    return best, worst_lam, empty, len(rows), bs

if __name__ == "__main__":
    with Pool(6) as pool:
        res = pool.map(job, range(1, M - K + 2))
    tot = sum(r[3] for r in res)
    empty = sum(r[2] for r in res)
    allb = [b for r in res for b in r[4]]
    best = max((r[0] for r in res if r[0]), key=lambda r: r[2])
    print(f"frame: all C({M},{K}) = {tot} six-subsets of [1,{M}], level 1/8, exact")
    print(f"six-subsets whose L6 has NO positive-length component: {empty}")
    print()
    print(f"LEMMA bound on the 7th speed:  v <= 1/(4*lambda)")
    print(f"  worst (largest) bound over the frame: v <= {best[2]}   attained by T6 = {list(best[0])}")
    print(f"     its largest component lambda = {best[1]} = {float(best[1]):.6e}")
    print()
    import collections
    h = collections.Counter(allb)
    print("distribution of the bound B = floor(1/(4*lambda)):")
    for b in sorted(h)[:14]:
        print(f"    v <= {b:>5} : {h[b]:>7} six-subsets")
    print(f"    ... max B = {max(h)}")
    print()
    print(f"six-subsets forcing the 7th speed <= 24 (i.e. inside the frame): "
          f"{sum(c for b,c in h.items() if b <= 24)} of {tot}")
