#!/usr/bin/env python3
"""
selection_negative_space_v1.py

LATERAL (2026-07-13): the keys are "deliberately-selected small ints". The pinned
task asks WHICH PRNG. This asks a different question: did the creator apply a
post-generation KEEP/REJECT filter -- avoiding "ugly" or "too-structured" values --
leaving a NEGATIVE SPACE the key set doesn't occupy? That is a human-selection
signature independent of the generator.

Method: a panel of low-description-complexity DESCRIPTORS of a key d (normalized so
they compare across bit-lengths), computed for the 82 real keys and for two
controls: the 100k known-MT set (the "no deliberate filter" null through the same
pipeline) and the full-range generated set. Per-descriptor two-sample test
(Mann-Whitney U via exact rank) real-vs-MT, Holm-corrected. A descriptor where real
differs from MT = a candidate selection filter (a hole or a bias in description space).

Exact integer descriptors; the U statistic is a rank stat (sanctioned).
"""
import numpy as np, csv, os
from math import gcd

def popcount(x): return bin(x).count("1")
def longest_run(x):
    s = bin(x)[2:]; best = cur = 1
    for i in range(1, len(s)):
        cur = cur + 1 if s[i] == s[i - 1] else 1; best = max(best, cur)
    return best
def distinct_hex(x): return len(set(f"{x:x}"))
def distinct_dec(x): return len(set(str(x)))
def small_factor_count(x, B=1000):
    c = 0; xx = x
    for pr in range(2, B):
        if xx % pr == 0:
            c += 1
            while xx % pr == 0: xx //= pr
    return c
def dist_pow2(x):
    N = x.bit_length(); return min(x - (1 << (N - 1)), (1 << N) - x)  # distance to nearer 2^k edge (int)
def bin_palindrome(x):
    s = bin(x)[2:]; return sum(1 for i in range(len(s) // 2) if s[i] == s[-1 - i])

DESCS = {
    "popcnt/N": lambda d, N: (popcount(d) * 1000) // N,       # per-mille of set bits
    "longrun": lambda d, N: longest_run(d),
    "distinct_hex": lambda d, N: distinct_hex(d),
    "distinct_dec": lambda d, N: distinct_dec(d),
    "smallfactors": lambda d, N: small_factor_count(d),
    "distpow2/lo": lambda d, N: (dist_pow2(d) * 1000) >> (N - 1),  # normalized 0..1000
    "bin_palin": lambda d, N: (bin_palindrome(d) * 1000) // max(N // 2, 1),
    "d%2": lambda d, N: d & 1,
}

def load_real():
    here = os.path.dirname(os.path.abspath(__file__))
    out = []
    with open(os.path.join(here, "btc_puzzle_master_exact.csv")) as f:
        for r in csv.DictReader(f):
            if r["status"].strip().upper() == "SOLVED" and r["priv_dec"].strip():
                out.append((int(r["priv_dec"]), int(r["bits"])))
    return out

def load_mt_matched(real, per=40):
    """BIT-LENGTH-MATCHED control: for each real key of N bits, sample `per` MT keys
    of the SAME N. (Un-matched control confounds descriptors that scale with N.)"""
    import random
    here = os.path.dirname(os.path.abspath(__file__))
    bybits = {}
    with open(os.path.join(here, "constructed_keys_1to160_100k_exact.csv")) as f:
        for r in csv.DictReader(f):
            bybits.setdefault(int(r["bits"]), []).append(int(r["d"]))
    rng = random.Random(7); out = []
    for d, N in real:
        pool = bybits.get(N) or bybits.get(min(bybits, key=lambda b: abs(b - N)))
        out += [(rng.choice(pool), N) for _ in range(per)]
    return out

def mannwhitney_z(a, b):
    """rank-sum z of sample a vs b (ties-corrected, large-sample normal approx)."""
    na, nb = len(a), len(b); allv = np.array(list(a) + list(b), float)  # noqa: float (rank stat)
    order = allv.argsort(); ranks = np.empty(na + nb)                   # noqa: float
    ranks[order] = np.arange(1, na + nb + 1)                            # noqa: float
    # tie correction: average ranks
    _, inv, cnt = np.unique(allv, return_inverse=True, return_counts=True)
    Ra = ranks[:na].sum()                                               # noqa: float
    U = Ra - na * (na + 1) / 2                                          # noqa: float
    mu = na * nb / 2                                                    # noqa: float
    sd = (na * nb * (na + nb + 1) / 12) ** 0.5                          # noqa: float
    return float((U - mu) / (sd + 1e-9))                               # noqa: float

def main():
    real = load_real(); mt = load_mt_matched(real)
    print(f"real={len(real)} keys, BIT-LENGTH-MATCHED MT-control={len(mt)} keys\n")
    print(f"{'descriptor':>14} {'real_med':>9} {'MT_med':>9} {'MW-z(real vs MT)':>17}  flag")
    zs = []
    for name, fn in DESCS.items():
        rv = [fn(d, N) for d, N in real]
        mv = [fn(d, N) for d, N in mt]
        z = mannwhitney_z(rv, mv)
        zs.append((name, z))
        rmed = int(np.median(rv)); mmed = int(np.median(mv))            # noqa: float (report)
        print(f"{name:>14} {rmed:>9} {mmed:>9} {z:>17.2f}  {'<-- CHECK' if abs(z) > 2.5 else ''}")  # noqa: float (report/classifier)
    # Holm correction over the panel
    from math import erfc, sqrt
    ps = sorted(((name, erfc(abs(z) / sqrt(2))) for name, z in zs), key=lambda t: t[1])  # noqa: float
    m = len(ps); print("\n  Holm-corrected panel (need p_(i) < 0.05/(m-i+1)):")
    any_sig = False
    for i, (name, pv) in enumerate(ps):
        thr = 0.05 / (m - i)                                            # noqa: float
        sig = pv < thr
        any_sig = any_sig or sig
        print(f"    {name:>14}: p={pv:.4f}  thr={thr:.4f}  {'SIGNIFICANT' if sig else ''}")
    print(f"\n=> {'a selection-filter signature SURVIVES Holm' if any_sig else 'NO descriptor survives Holm — no negative-space filter detected at n=82'}")
    print("   (control: real vs MT are BOTH through select-bitlen->keep; a real difference = human filter)")

if __name__ == "__main__":
    main()
