"""First-interval decision procedure, exact integer arithmetic.

Runner i has differences ds (positive ints), m = min(ds).
Window in t: [1/(8m), 7/(8m)].  Attains  <=>  exists t in window with
||d t|| >= 1/8 for every d in ds.

Good set is closed; its extreme points lie among the window endpoints and the
endpoints (8k +- 1)/(8d) of the open bad intervals.  So testing that finite
candidate set is an exact decision, not a sampling.
"""

def ok_at(ds, p, q):
    """||d*p/q|| >= 1/8 for all d?  p,q positive ints."""
    for d in ds:
        r = (d * p) % q
        if 8 * min(r, q - r) < q:
            return False
    return True


def attains(ds):
    """Exact.  Returns a witness (p,q) with t=p/q in the window, or None."""
    m = min(ds)
    # window endpoints
    for p in (1, 7):
        if ok_at(ds, p, 8 * m):
            return (p, 8 * m)
    lo_num, hi_num = 1, 7          # t in [lo_num/(8m), hi_num/(8m)]
    for d in ds:
        q = 8 * d
        # t = p/(8d) in window  <=>  p/d in [1/m, 7/m]  <=>  p in [d/m, 7d/m]
        klo = (d) // (8 * m) - 1
        khi = (7 * d) // (8 * m) + 2
        for k in range(klo, khi + 1):
            for p in (8 * k - 1, 8 * k + 1):
                if p <= 0:
                    continue
                # window test, exact:  p/(8d) >= 1/(8m)  and  <= 7/(8m)
                if p * m < d or p * m > 7 * d:
                    continue
                if ok_at(ds, p, q):
                    return (p, q)
    return None


def diffs(V, i):
    return [abs(V[j] - V[i]) for j in range(len(V)) if j != i]


def config_ok(V):
    """Every runner attains in its own first window?  Returns list of failures."""
    bad = []
    for i in range(len(V)):
        ds = diffs(V, i)
        if attains(ds) is None:
            bad.append(i)
    return bad
