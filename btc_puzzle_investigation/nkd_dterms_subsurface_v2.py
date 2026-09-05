#!/usr/bin/env python3
"""
nkd_dterms_subsurface_v2.py -- test fiber fragmentation on GENUINELY WIDE fibers.

v1 showed N<=18 fibers are too narrow (width<=257, T in {0,1}) to fragment. Wide fibers
need large N; can't enumerate a whole 2^N band, but a single fiber is a CONTIGUOUS d-interval
(proven), so we find its boundaries by exponential+binary search and enumerate just that fiber.

For a chosen (N,n,k): compute T(D)=d_terms over the whole fiber, then ask whether the
complexity-bounded sublevel set A_t={D: T(D)<=t} fragments into disconnected runs
(#components>1 => holes), REAL vs a within-fiber permutation control (same T-multiset,
random arrangement).  Exact integers; control is a count statistic.
"""
import sys, random
from collections import Counter
from exact_core import best_nk, residual, d_terms, lo_of


def fiber_bounds(N, n, k):
    lo = lo_of(N)
    base = lo + (lo * k) // n
    if not (lo <= base < 2 * lo) or best_nk(base, N, 256) != (n, k):
        return None
    def ok(d):
        return lo <= d < 2 * lo and best_nk(d, N, 256) == (n, k)
    # right boundary
    hi = base; s = 1
    while ok(hi + s):
        hi += s; s *= 2
    lb, ub = hi, hi + s
    while lb < ub:
        mid = (lb + ub + 1) // 2
        lb, ub = (mid, ub) if ok(mid) else (lb, mid - 1)
    d_hi = lb
    # left boundary
    lo_ = base; s = 1
    while ok(lo_ - s):
        lo_ -= s; s *= 2
    lb, ub = lo_ - s, lo_
    while lb < ub:
        mid = (lb + ub) // 2
        lb, ub = (lb, mid) if ok(mid) else (mid + 1, ub)
    d_lo = lb
    return d_lo, d_hi


def components(present_sorted):
    if not present_sorted:
        return 0
    comp = 1
    for i in range(1, len(present_sorted)):
        if present_sorted[i] != present_sorted[i - 1] + 1:
            comp += 1
    return comp


def analyze(Tvals, tmax=5, ctrl_seeds=20):
    W = len(Tvals)
    print(f"  width={W}  T-hist={dict(sorted(Counter(Tvals).items()))}")
    print(f"  {'t':>2} {'realComp':>9} {'ctrlComp(mean)':>15} {'real/ctrl':>10} {'|A_t|':>8}")
    for t in range(tmax + 1):
        present = [i for i in range(W) if Tvals[i] <= t]
        real_c = components(present)
        csum = 0
        for s in range(ctrl_seeds):
            rng = random.Random(31 * s + 5)
            perm = Tvals[:]; rng.shuffle(perm)
            csum += components([i for i in range(W) if perm[i] <= t])
        cmean = csum / ctrl_seeds                      # noqa: float (report)
        ratio = real_c / cmean if cmean else 0.0       # noqa: float (report)
        print(f"  {t:>2} {real_c:>9} {cmean:>15.1f} {ratio:>10.3f} {len(present):>8}")


def main():
    # (N, n, k) targets: push width up while keeping enumeration feasible
    targets = []
    if len(sys.argv) > 3:
        targets = [(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))]
    else:
        targets = [(26, 2, 1), (26, 3, 1), (28, 2, 1), (30, 3, 1)]
    for (N, n, k) in targets:
        b = fiber_bounds(N, n, k)
        if b is None:
            print(f"N={N} (n,k)=({n},{k}): base not canonical, skip"); continue
        d_lo, d_hi = b
        W = d_hi - d_lo + 1
        print(f"\n### N={N}  (n,k)=({n},{k})  fiber d in [{d_lo},{d_hi}]  width={W}")
        if W > 6_000_000:
            print(f"  width {W} too large to enumerate pointwise; skipping detailed pass.")
            continue
        Tvals = [d_terms(d, N, n, k) for d in range(d_lo, d_hi + 1)]
        analyze(Tvals)


if __name__ == "__main__":
    main()
