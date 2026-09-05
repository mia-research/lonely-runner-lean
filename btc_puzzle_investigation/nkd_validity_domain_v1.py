#!/usr/bin/env python3
"""
nkd_validity_domain_v1.py

The (n,k,D) coordinate is invertible: d = 2^(N-1) + (2^(N-1)*k)//n + D. But NOT every
(n,k,D) triple is a valid/canonical key -- and "which combos cannot produce a valid
curve integer" is itself a data point (user 2026-07-13). This maps the domain:

  Q1 REACHABLE LABELS: which (n,k) actually arise as best_nk(d)? A non-coprime (n,k)
     reduces to k'/n' with n'<n, which is a better-or-equal approx, so gcd(n,k)>1 is
     NEVER canonical -> a FORBIDDEN label set (coprimality forbids labels, not d-regions).
  Q2 D-RANGE per n: for a fixed canonical (n,k) the residual D that keeps (n,k) the best
     approx lives in a Farey-gap interval whose width shrinks with n (~ lo/n^2). Measured.
  Q3 CURVE-SCALAR OVERFLOW: at N=256, d can exceed the group order N_ORDER (< 2^256).
     Those d are NOT distinct scalars (reduce mod n) -> a real "certain 256-bit integers
     cannot be a fresh curve key" data point. Fraction measured.

Exact integers (CLAUDE.md). Self-contained (does not need the dataset).
"""
import math, random, numpy as np
from collections import Counter, defaultdict
from exact_core import best_nk, residual, lo_of

_PY = random.Random(20260713)  # for big-int ranges numpy int64 can't hold

N_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
NMAX = 256

def gcd(a, b):
    while b: a, b = b, a % b
    return a

# ---- Q1: are non-coprime (n,k) ever canonical? (forward census) ----
def forward_census(N, samples, rng):
    supp = Counter(); gcds = Counter(); Dabs_by_n = defaultdict(list)
    lo = lo_of(N)
    for _ in range(samples):
        d = lo + int(rng.integers(0, lo)) if N <= 63 else lo + int.from_bytes(rng.bytes((N+7)//8), "big") % lo
        n, k = best_nk(d, N, NMAX)
        supp[(n, k)] += 1
        g = gcd(n, k) if k > 0 else n  # k=0 -> label (n,0); canonical only n=1
        gcds[g] += 1
        D = residual(d, N, n, k)
        Dabs_by_n[n].append(abs(D))
    return supp, gcds, Dabs_by_n

# ---- Q1b: explicit forbidden-label check ----
def label_reachable(N, n, k, tries, rng):
    """Does ANY d have best_nk == (n,k)? Sample d whose u is near k/n and test."""
    lo = lo_of(N)
    base = lo + (lo * k) // n
    W = lo // (n * n) + 2
    for _ in range(tries):
        D = _PY.randrange(-W, W)
        d = base + D
        if not (lo <= d < 2 * lo):
            continue
        if best_nk(d, N, NMAX) == (n, k):
            return True
    return False

def main():
    rng = np.random.default_rng(20260713)
    print("=== Q1  REACHABLE LABELS: is any best_nk (n,k) non-coprime? ===")
    for N in (64, 128, 256):
        supp, gcds, Dabs = forward_census(N, 30000, rng)
        noncop = sum(c for (n, k), c in supp.items() if k > 0 and gcd(n, k) > 1)
        distinct = len(supp)
        print(f"  N={N:3d}: {distinct} distinct (n,k) labels seen in 30000 draws; "
              f"non-coprime canonical labels (k>0, gcd>1): {noncop}  "
              f"(gcd histogram top: {gcds.most_common(3)})")
    print("  -> gcd(n,k)=1 is necessary for a canonical label (non-coprime = FORBIDDEN).")

    print("\n=== Q1b  explicit: planted non-coprime labels are unreachable ===")
    N = 128
    for (n, k) in [(4, 2), (6, 3), (9, 6), (10, 5)]:
        r = label_reachable(N, n, k, 4000, rng)
        g = gcd(n, k)
        print(f"  N=128 label (n={n},k={k}) gcd={g}: reachable as best_nk = {r}  "
              f"(expect False for gcd>1)")
    # positive control: a coprime label IS reachable
    for (n, k) in [(5, 2), (7, 3)]:
        print(f"  [ctrl] coprime (n={n},k={k}) gcd=1: reachable = "
              f"{label_reachable(N, n, k, 4000, rng)}  (expect True)")

    print("\n=== Q2  D-RANGE per n (Farey-gap width; should shrink ~ lo/n^2) ===")
    N = 256; lo = lo_of(N)
    _, _, Dabs = forward_census(N, 40000, rng)
    print(f"  N=256, lo=2^255. max|D| observed per small n vs lo/n^2 prediction:")
    for n in (1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233):
        vals = Dabs.get(n, [])
        if not vals:
            continue
        mx = max(vals)
        pred_bits = 255 - 2 * (n.bit_length() - 1)  # ~ log2(lo/n^2)
        print(f"    n={n:3d}: max|D|~2^{mx.bit_length()-1:3d}  (lo/n^2 ~ 2^{max(pred_bits,0):3d}), "
              f"count={len(vals)}")

    print("\n=== Q3  CURVE-SCALAR OVERFLOW at N=256 (d >= group order) ===")
    lo = 1 << 255
    trials = 200000
    over = sum(1 for _ in range(trials)
               if (lo + int.from_bytes(rng.bytes(32), "big") % lo) >= N_ORDER)
    frac = over / trials  # noqa: float (report)
    gap = (1 << 256) - N_ORDER
    print(f"  P(uniform 256-bit d >= N_ORDER) = {frac:.6f}  (~gap/2^255 = "
          f"{gap} / 2^255 ~ 2^{gap.bit_length()-1-255})")
    print("  -> a small but nonzero fraction of 256-bit integers are NOT fresh curve")
    print("     scalars (they reduce mod n). Below N=256 every in-range d is a valid scalar.")

if __name__ == "__main__":
    main()
