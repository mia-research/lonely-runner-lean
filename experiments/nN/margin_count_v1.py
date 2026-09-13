"""
How close does the procedure come to failing?  -- the RIGHT quantity.

A first attempt measured the LENGTH of the clear set. That is uninformative and the reason
is MANUSCRIPT section 6.1 itself: the arithmetic progression's clear set is a finite set of
points, so its length is 0. The minimum over any family containing an AP is 0, attained,
and says nothing.

The informative quantity is the COUNT of clear components. The AP has phi(n) of them. The
question this answers:

    over an exhaustive family, what is the FEWEST clear components any runner has,
    and is it ever fewer than phi(n)?

A count of 0 is a failure of the procedure. A count of 1 is the tightest case short of
failure: a single instant in the whole window at which the runner is lonely.

Counting is not measuring. Nothing here is a route to part 7, which section 6.1 closes to
size arguments at any strength; this locates where the procedure is tightest, which is a
different question and not a proof of anything.

Exact; open zones; never merged -- two touching zones leave their shared endpoint clear and
that endpoint is its own clear component.
"""
import sys, itertools
from fractions import Fraction as F
from math import gcd

def phi(n):
    r, m, p = n, n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            r -= r // p
        p += 1
    if m > 1:
        r -= r // m
    return r

def readings(v, i, n):
    d = sorted(abs(v[j] - v[i]) for j in range(n) if j != i)
    dmin = d[0]
    return [F(x, dmin) for x in d[1:]]

def clear_components(v, i, n):
    """Number of connected components of the clear set, and the first clear point."""
    lo, hi = F(1, n), F(n - 1, n)
    Z = []
    for s in readings(v, i, n):
        k = 0
        while True:
            a = F(n * k - 1, n) / s
            if a > hi:
                break
            b = F(n * k + 1, n) / s
            if b > lo:
                Z.append((a, b))
            k += 1
    Z.sort()
    # candidate left ends of clear components: lo, and each zone's right endpoint
    cands = sorted({lo} | {b for _, b in Z if lo <= b <= hi})
    comps, first = 0, None
    ptr, maxb = 0, None
    for u in cands:
        while ptr < len(Z) and Z[ptr][0] < u:
            b = Z[ptr][1]
            if maxb is None or b > maxb:
                maxb = b
            ptr += 1
        if maxb is None or not (maxb > u):
            comps += 1
            if first is None:
                first = u
    return comps, first

def sweep(n, V):
    tot = fail = 0
    best = None
    hist = {}
    for v in itertools.combinations(range(1, V + 1), n):
        g = 0
        for x in v:
            g = gcd(g, x)
        if g != 1:
            continue
        for i in range(n):
            tot += 1
            c, u = clear_components(list(v), i, n)
            hist[min(c, 12)] = hist.get(min(c, 12), 0) + 1
            if c == 0:
                fail += 1
                print(f"    FAILURE n={n} v={v} runner={i}", flush=True)
            if best is None or c < best[0]:
                best = (c, v, i, u)
    return tot, fail, best, hist

if __name__ == "__main__":
    print("fewest clear components over each exhaustive family")
    print("n distinct positive integer speeds, gcd 1, no runner pinned at 0; exact\n")
    spec = [(5, 30), (6, 24), (7, 20), (8, 18), (9, 16), (10, 15)]
    if len(sys.argv) > 1:
        spec = [(int(a.split(':')[0]), int(a.split(':')[1])) for a in sys.argv[1:]]
    print(f"{'n':>3} {'phi':>4} {'V':>4} {'instances':>11} {'fail':>5} {'min comps':>10}")
    print("-" * 52)
    for n, V in spec:
        tot, fail, best, hist = sweep(n, V)
        c, vv, ii, uu = best
        print(f"{n:>3} {phi(n):>4} {V:>4} {tot:>11} {fail:>5} {c:>10}", flush=True)
        print(f"        at v={vv} runner={ii}, its only/first clear u={uu}", flush=True)
        tail = ", ".join(f"{k}:{hist[k]}" for k in sorted(hist) if k <= 6)
        print(f"        component-count histogram (<=6): {tail}", flush=True)
