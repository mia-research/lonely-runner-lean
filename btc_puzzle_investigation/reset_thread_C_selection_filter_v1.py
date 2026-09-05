#!/usr/bin/env python3
"""
Reset thread C: the selection-filter reframe.

The two established key-side facts are in tension: the generator tests high-quality
(BM ~ n/2, KS-uniform) AND positions carry a base-10 bias (omega(n), p=0.002).
Reconciliation hypothesis: generator + a HUMAN selection filter ("pick a round
position"). If so, the object to characterize is the selection criterion, and the
doc tested only ONE proxy (omega of the decomposition denominator n).

This probes decimal-roundness DIRECTLY and decomposition-independently on:
    d, (d-A), and (for completeness) the fixed-decomposition denominator n.
Statistics (exact integers): factors of 2 and 5, trailing decimal zeros.
Null: uniform random d' in the SAME range [2^(N-1), 2^N) per key, matched.
p-value: fraction of B null keysets whose aggregate >= observed (integer ratio).
Positive control: a decimally-rounded keyset must fire.
"""
import random
from fractions import Fraction
from reset_common import load_solved

solved = load_solved()
KEYS = sorted(solved)                                   # all 82
BITS = {N: solved[N]["bits"] for N in KEYS}
D    = {N: solved[N]["d"] for N in KEYS}
B    = 20000
rng  = random.Random(0xC0FFEE)

def v(m, q):
    """q-adic valuation of |m| (0 for m==0)."""
    m = abs(m)
    if m == 0: return 0
    c = 0
    while m % q == 0:
        m //= q; c += 1
    return c

def trailing_dec_zeros(m):
    return min(v(m, 2), v(m, 5))

def omega(m):
    """number of distinct prime factors of m>0 by trial division (m small: <=NMAX)."""
    m = abs(m); cnt = 0; d = 2
    while d * d <= m:
        if m % d == 0:
            cnt += 1
            while m % d == 0: m //= d
        d += 1 if d == 2 else 2
    if m > 1: cnt += 1
    return cnt

def denom_fixed(d, N, NMAX):
    A = 1 << (N - 1)
    return Fraction(d - A, A).limit_denominator(NMAX).denominator

# ---- statistics over a keyset {N: d} ----
def stat_v2_dm(ks):   return sum(v(ks[N] - (1 << (N-1)), 2) for N in ks)   # 2-adic of d-A
def stat_v5_dm(ks):   return sum(v(ks[N] - (1 << (N-1)), 5) for N in ks)   # 5-adic of d-A
def stat_tz_dm(ks):   return sum(trailing_dec_zeros(ks[N] - (1 << (N-1))) for N in ks)
def stat_v2_d(ks):    return sum(v(ks[N], 2) for N in ks)
def stat_v5_d(ks):    return sum(v(ks[N], 5) for N in ks)
def stat_tz_d(ks):    return sum(trailing_dec_zeros(ks[N]) for N in ks)
def make_stat_omega(NMAX):
    def s(ks): return sum(omega(denom_fixed(ks[N], N, NMAX)) for N in ks)
    return s

STATS = {
    "v2(d-A) sum":  stat_v2_dm,
    "v5(d-A) sum":  stat_v5_dm,
    "tz10(d-A) sum": stat_tz_dm,
    "v2(d) sum":    stat_v2_d,
    "v5(d) sum":    stat_v5_d,
    "tz10(d) sum":  stat_tz_d,
    "omega(n) sum @NMAX=256":  make_stat_omega(256),
    "omega(n) sum @NMAX=1024": make_stat_omega(1024),
}

def null_keyset():
    return {N: rng.randrange(1 << (N-1), 1 << N) for N in KEYS}

def pvalue(stat_fn, observed):
    """right-tail p: fraction of null keysets with stat >= observed, as m/B."""
    ge = 0
    for _ in range(B):
        if stat_fn(null_keyset()) >= observed:
            ge += 1
    return ge, B

print("=== Thread C: decimal-roundness / selection filter (82 solved keys) ===")
print(f"null draws B = {B}, matched per-key ranges\n")
print(f"{'statistic':<26} {'observed':>10} {'null-mean':>10} {'p(>=obs)':>12}")
# precompute null means cheaply (reuse a sample)
null_samples = [null_keyset() for _ in range(2000)]
for name, fn in STATS.items():
    obs = fn(D)
    nm = sum(fn(ks) for ks in null_samples) / len(null_samples)
    ge, tot = pvalue(fn, obs)
    print(f"{name:<26} {obs:>10} {nm:>10.2f} {ge:>7}/{tot} = {ge/tot:.4f}")

# ---- positive control: force decimal roundness on d-A, must fire ----
print("\n[CTRL] planted decimally-round keyset (d-A rounded to nearest 10^k):")
def rounded_keyset():
    out = {}
    for N in KEYS:
        A = 1 << (N-1)
        raw = rng.randrange(0, A)
        k = max(1, (N // 4))               # round to ~10^(N/4)
        step = 10 ** k
        r = (raw // step) * step
        out[N] = A + (r if r < A else raw)
    return out
ctrl = rounded_keyset()
for name in ("tz10(d-A) sum", "v5(d-A) sum"):
    fn = STATS[name]; obs = fn(ctrl); ge, tot = pvalue(fn, obs)
    print(f"   {name:<20} observed {obs:>6}  p(>=obs) {ge}/{tot} = {ge/tot:.4f}  -> {'FIRES' if ge/tot < 0.01 else 'no'}")
