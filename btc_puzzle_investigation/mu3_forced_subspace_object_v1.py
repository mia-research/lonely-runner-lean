#!/usr/bin/env python3
"""mu3_forced_subspace_object_v1.py -- item 2: BUILD the object I buried this morning.

THE OBJECT (CORRECTION_deflation_overreach_v1.md section 4.2, restored):
  h1[d] = chi2(y_{[d]G}) is FORCED into the mu3-invariant subspace: h1[m*d] = h1[d], m of order 3
  in (Z/n)*, together with h1[-d] = eps*h1[d].  So the n-1 signs carry only (n-1)/6 free values.
  j=0-specific, hence present on secp256k1.  No statistic in the record projects onto it.

WHAT THIS SCRIPT DOES -- and does NOT:
  It CONSTRUCTS the reduced object and CHARACTERIZES it.  It is NOT a leakage verdict: promoting
  any reading here to a leakage claim requires experiment-designer pre-registration (CLAUDE.md s2).
  Labelled descriptive throughout.

CONSTRUCTION.  (Z/n)* is cyclic of order n-1; pick a generator gamma.  Writing d = gamma^i,
  * mu3 invariance  => s[i] := h1[gamma^i] has period M := (n-1)/3
  * negation (-1 = gamma^{(n-1)/2}) => r[j + M/2] = eps * r[j] on the reduced index
so the free content is u : Q6 -> {+-1} with |Q6| = (n-1)/6, matching mu6_reps' cell count exactly.
Both forced symmetries are VERIFIED here, not assumed.

STATISTIC.  Fourier concentration of u over the cyclic group Q6: max over nontrivial characters of
|u^(chi)|.  Per CLAUDE.md a float transform is permitted ONLY as a monotone statistic ranked against
a MATCHED null -- so the value is never thresholded; it is ranked against R random +-1 sequences of
the SAME length.  The reported number is an integer rank.
"""
import cmath, random, sys                                             # noqa: float
import audit_n1_vsign_v2_core as core
from jclass_e2_relation_probe_v1 import curve_order_p, dlog_table_p, points_p

R_NULL = 2000

def primitive_root(n):
    fac, m = [], n - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, n):
        if all(pow(g, (n - 1) // q, n) != 1 for q in fac): return g
    raise RuntimeError

def maxfourier(v):
    N = len(v)
    best = 0.0                                                        # noqa: float
    for k in range(1, N):
        s = sum(v[j] * cmath.exp(-2j * cmath.pi * k * j / N) for j in range(N))   # noqa: float
        a = abs(s)                                                    # noqa: float
        if a > best: best = a
    return best

def build(p, B=7):
    n = curve_order_p(p, 0, B)
    if not core.is_prime(n) or (n - 1) % 6: return None
    dl, cyc = dlog_table_p(p, 0, B, n)
    if not cyc: return None
    half = (p - 1) // 2
    y = {}
    for (x, yy) in points_p(p, 0, B): y[dl[(x, yy)]] = yy
    h1 = [0] * n
    for d in range(1, n): h1[d] = 1 if pow(y[d], half, p) == 1 else -1
    # the order-3 multiplier m from Aut(E)
    z3 = core.tonelli((-3) % p, p); c1 = (-1 + z3) * pow(2, p - 2, p) % p
    z3 = c1 if (c1 * c1 + c1 + 1) % p == 0 else (-1 - core.tonelli((-3) % p, p)) * pow(2, p - 2, p) % p
    m = None
    for (x, yy), d in dl.items():
        if d: m = dl[(z3 * x % p, yy)] * pow(d, -1, n) % n; break
    eps = core.legendre(-1, p)
    sym3 = all(h1[m * d % n] == h1[d] for d in range(1, n))
    symn = all(h1[(-d) % n] == eps * h1[d] for d in range(1, n))
    g = primitive_root(n)
    M = (n - 1) // 3
    s = [h1[pow(g, i, n)] for i in range(n - 1)]
    per3 = all(s[(i + M) % (n - 1)] == s[i] for i in range(n - 1))
    r = s[:M]
    per2 = all(r[(j + M // 2) % M] == eps * r[j] for j in range(M))
    u = r[:M // 2]
    return dict(n=n, m=m, eps=eps, sym3=sym3, symn=symn, per3=per3, per2=per2, u=u)

if __name__ == "__main__":
    rng = random.Random(20260801)
    print("p      n   eps | forced h1[md]=h1[d] | forced h1[-d]=eps.h1[d] | period M | half-per | "
          "|Q6| | maxFourier rank vs %d random" % R_NULL)
    for p in (43, 67, 79, 127, 163, 211, 547, 823):
        b = build(p)
        if b is None: continue
        u = b["u"]; N = len(u)
        if N < 4: continue
        obs = maxfourier(u)
        null = [maxfourier([rng.choice((-1, 1)) for _ in range(N)]) for _ in range(R_NULL)]
        rank = sum(1 for z in null if z < obs)
        print("%5d %5d %+3d | %-19s | %-23s | %-8s | %-8s | %4d | rank %4d/%d"
              % (p, b["n"], b["eps"], b["sym3"], b["symn"], b["per3"], b["per2"], N, rank, R_NULL))
