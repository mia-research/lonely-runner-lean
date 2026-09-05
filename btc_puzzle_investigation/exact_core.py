#!/usr/bin/env python3
"""
exact_core.py  —  float-free decomposition primitives (CLAUDE.md rule).

Everything here is exact int / Fraction. No `/`, no float(), no round(ratio).
Best rational approximation minimizes the INTEGER quantity |(d-lo)*n - k*lo|;
errors are compared by integer cross-multiplication (u=num/lo, err_n = a_n/(lo*n),
so a1/n1 < a2/n2  <=>  a1*n2 < a2*n1).

Self-test (`python exact_core.py`) checks the integer path against a Fraction
reference on random keys and asserts the guard passes.
"""
from fractions import Fraction

def lo_of(N):            # band floor 2^{N-1}
    return 1 << (N - 1)

def best_nk(d, N, nmax=256):
    """Exact best k/n approx of u=(d-lo)/lo with 1<=n<=nmax. Integer-only."""
    if N <= 1:
        return (1, 0)
    lo = lo_of(N); num = d - lo                      # u = num/lo, 0 <= num < lo
    a_best = None; n_best = 1; k_best = 0
    for n in range(1, nmax + 1):
        k = (2 * num * n + lo) // (2 * lo)           # round(u*n), half-up, exact
        a = abs(num * n - k * lo)                     # err_n = a/(lo*n)
        if a_best is None or a * n_best < a_best * n:  # a/n < a_best/n_best
            a_best, n_best, k_best = a, n, k
    return (n_best, k_best)

def base_of(d, N, n, k):
    lo = lo_of(N); return lo + (lo * k) // n

def residual(d, N, n, k):
    return d - base_of(d, N, n, k)

def d_terms(d, N, n, k, cap=200):
    """Greedy reciprocal (Sylvester/GECT) term count, integer-only."""
    lo = lo_of(N); cur = base_of(d, N, n, k); err = d - cur; t = 0
    while err != 0 and t < cap:
        Di = lo // abs(err)
        if Di == 0:
            t += 1; break
        corr = lo // Di
        cur += corr if err > 0 else -corr
        err = d - cur; t += 1
    return t

def cf_denoms(d, N, cap=6):
    """Exact continued-fraction convergent denominators q1,q2,... of u=(d-lo)/lo.
    CF(num/lo)=[a0=0; a1,a2,...]; k_i=a_i k_{i-1}+k_{i-2}, (k_-1,k_0)=(0,1)."""
    if N <= 1:
        return [1]
    lo = lo_of(N); num = d - lo
    if num == 0:
        return [1]
    a = []; x, y = num, lo
    while y and len(a) < cap + 2:
        a.append(x // y); x, y = y, x % y            # a = [a0=0, a1, a2, ...]
    qs = []; km2, km1 = 0, 1
    for ai in a[1:]:
        k = ai * km1 + km2; qs.append(k); km2, km1 = km1, k
    return qs or [1]

def position_bin(d, N, bins):
    """Exact bin of u=(d-lo)/lo in {0..bins-1}."""
    lo = lo_of(N); num = d - lo
    b = (bins * num) // lo
    return b if b < bins else bins - 1

def nk_curve(d, N, nmax=512):
    """Parity of best-approx denominator n(m) for m=1..nmax (exact running best)."""
    out = [0] * (nmax + 1)
    if N <= 1:
        return out
    lo = lo_of(N); num = d - lo
    a_best = None; n_best = 1
    for n in range(1, nmax + 1):
        k = (2 * num * n + lo) // (2 * lo)
        a = abs(num * n - k * lo)
        if a_best is None or a * n_best < a_best * n:
            a_best, n_best = a, n
        out[n] = n_best & 1
    return out

# ---------- self-test ----------
def _best_nk_ref(d, N, nmax):
    """Independent Fraction reference for the min-selection logic."""
    lo = lo_of(N); num = d - lo; best = None
    for n in range(1, nmax + 1):
        k = (2 * num * n + lo) // (2 * lo)
        e = abs(Fraction(num, lo) - Fraction(k, n))
        if best is None or e < best[0]:
            best = (e, n, k)
    return (best[1], best[2])

if __name__ == "__main__":
    import random, subprocess, sys, os
    rng = random.Random(20260707)
    for _ in range(4000):
        N = rng.randint(8, 160); d = (1 << (N - 1)) + rng.randrange(1 << (N - 1))
        for nmax in (128, 256, 512):
            assert best_nk(d, N, nmax) == _best_nk_ref(d, N, nmax), (d, N, nmax)
        n, k = best_nk(d, N, 256)
        assert residual(d, N, n, k) == d - (lo_of(N) + (lo_of(N) * k) // n)
        qs = cf_denoms(d, N)
        assert all(isinstance(q, int) for q in qs) and qs[0] >= 1
    # convergent sanity
    assert cf_denoms((1 << 7) + (16 * (1 << 7)) // 113, 8)  # smoke
    print("exact_core self-test: PASS (4000 random keys, 3 nmax each)")
    here = os.path.dirname(os.path.abspath(__file__))
    r = subprocess.run([sys.executable, os.path.join(here, "check_no_float.py"), __file__],
                       capture_output=True, text=True)
    print(r.stdout.strip())
    sys.exit(r.returncode)
