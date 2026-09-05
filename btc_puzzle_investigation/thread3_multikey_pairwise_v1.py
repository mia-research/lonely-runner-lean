#!/usr/bin/env python3
"""
THREAD 3: multi-key joint-set structure via PAIRWISE point differences.
Idea: for a set of pubkeys {P_i}, P_i (-) P_j = [d_i - d_j]G is computable from the
POINTS ALONE (no d). If the scalars d_i are RELATED (e.g. arithmetic progression
d_i=d0+i*delta), the pairwise differences collapse onto few points -> detectable
joint-set signature; independent d_i -> all distinct. This is the ONE curve-side
channel the closure theorem does not cover (a property of the SET).

Power test (secp): AP set d_i=d0+i*delta (should concentrate) vs random set (should
not). Statistic = distinct x-coords of pairwise diffs / #pairs.
Then apply to the REAL 82 pubkeys (pairwise diffs from published X,Y).
HONEST SCOPE: the 82 puzzles are 1-per-bitlength (no within-band multi-key set), so
a within-generator SET test is not possible on real data; the cross-band 82-set has
no expected joint structure. The power test validates the method for IF such a set existed.
"""
import csv
from ecc_secp256k1 import scalar_mul, P as p, N_ORDER


def add_a(P1, P2):
    if P1 is None: return P2
    if P2 is None: return P1
    x1, y1 = P1; x2, y2 = P2
    if x1 == x2:
        if (y1 + y2) % p == 0: return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def neg(Pt): return (Pt[0], (-Pt[1]) % p)


def pairwise_distinct_ratio(points):
    xs = set(); npair = 0
    m = len(points)
    for i in range(m):
        for j in range(i + 1, m):
            D = add_a(points[i], neg(points[j]))
            if D is not None:
                xs.add(D[0]); npair += 1
    return len(xs) / npair if npair else 0, npair  # noqa: float


def main():
    import random
    rng = random.Random(3)
    print("THREAD 3: multi-key pairwise-difference joint-set test\n")
    print("(power test, secp, m=60 keys) distinct-diff ratio (AP -> ~4/m=0.067, random -> ~1):")
    m = 60
    # AP set
    d0 = rng.randrange(1, N_ORDER); delta = rng.randrange(1, 1 << 40)
    ap = [scalar_mul((d0 + i * delta) % N_ORDER) for i in range(m)]
    rr, _ = pairwise_distinct_ratio(ap)
    # geometric/GLV set d_i = d0 * r^i (multiplicative) -- another structure
    rr2base = rng.randrange(2, N_ORDER)
    geo = [scalar_mul((d0 * pow(rr2base, i, N_ORDER)) % N_ORDER) for i in range(m)]
    rg, _ = pairwise_distinct_ratio(geo)
    # random set
    rand = [scalar_mul(rng.randrange(1, N_ORDER)) for _ in range(m)]
    rrand, _ = pairwise_distinct_ratio(rand)
    print(f"    AP (d0+i*delta):        ratio = {rr:.4f}   ({'CONCENTRATED=structure' if rr<0.5 else 'flat'})")  # noqa: float
    print(f"    geometric (d0*r^i):     ratio = {rg:.4f}   ({'CONCENTRATED' if rg<0.5 else 'flat -- mult structure not seen by additive diff'})")  # noqa: float
    print(f"    random independent:     ratio = {rrand:.4f}   (predict ~1.0)")

    # real 82
    pts = []
    for r in csv.DictReader(open("puzzles_verified.csv")):
        pts.append((int(r["X"], 16), int(r["Y"], 16)))
    rr82, np82 = pairwise_distinct_ratio(pts)
    print(f"\n  REAL 82 pubkeys: pairwise-diff distinct ratio = {rr82:.4f} "
          f"(of {np82} pairs)")
    print("    ratio~1 => no AP/additive joint structure across the 82 (expected: they")
    print("    are 1-per-bitlength, unrelated). Scope: cross-band set; within-generator")
    print("    multi-key set not available in the puzzle (1 key per band).")


if __name__ == "__main__":
    main()
