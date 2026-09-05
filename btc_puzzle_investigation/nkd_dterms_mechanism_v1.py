#!/usr/bin/env python3
"""
nkd_dterms_mechanism_v1.py -- turn the empirical T=1 fragmentation (real/ctrl~0.5) into an
EXACT structural law, and locate the low-complexity islands. Exact integers.

Claim to test (from the d_terms recursion):
  T(D)=1  <=>  D>0 and D == lo//(lo//D)   (one greedy reciprocal step hits err=0)
The fixed points of f(D)=lo//(lo//D) are EXACTLY the reciprocal-floor lattice {lo//q : q>=1}
(Dirichlet hyperbola). Consequences to verify:
  (I)  A1 := {D in [1,Dmax]: T(D)=1}  ==  {D in [1,Dmax]: D == lo//(lo//D)}  (identity vs d_terms)
  (II) that set == the distinct values {lo//q} <= Dmax
  (III) island structure: values > sqrt(lo) are ISOLATED (spacing ~ lo/q^2 > 1);
        values <= sqrt(lo) fill a CONTIGUOUS block => #components ~ (#reciprocal-floors above sqrt).
  (IV) 2-adic vs Dirichlet-generic: is lo=2^(N-1) special? Recompute with a matched NON-power-of-2
       L of the same size. If island counts match, the law is DIRICHLET (generic in L), and the
       earlier '2-adic' guess is WRONG -> correct it.
"""
import sys
from math import isqrt
from exact_core import best_nk, residual, d_terms, lo_of


def fiber_bounds(N, n, k):
    lo = lo_of(N); base = lo + (lo * k) // n
    if not (lo <= base < 2 * lo) or best_nk(base, N, 256) != (n, k):
        return None
    def ok(d): return lo <= d < 2 * lo and best_nk(d, N, 256) == (n, k)
    hi = base; s = 1
    while ok(hi + s): hi += s; s *= 2
    lb, ub = hi, hi + s
    while lb < ub:
        mid = (lb + ub + 1) // 2
        lb, ub = (mid, ub) if ok(mid) else (lb, mid - 1)
    return base, lb            # (base, d_hi) -> Dmax = d_hi - base


def components_of(sorted_vals):
    if not sorted_vals: return 0
    c = 1
    for i in range(1, len(sorted_vals)):
        if sorted_vals[i] != sorted_vals[i - 1] + 1: c += 1
    return c


def recip_fixed(L, Dmax):
    """{ v in [1,Dmax] : v == L//(L//v) } == distinct {L//q} <= Dmax. O(Dmax)."""
    return [v for v in range(1, Dmax + 1) if v == L // (L // v)]


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 28
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    k = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    lo = lo_of(N)
    b = fiber_bounds(N, n, k)
    base, d_hi = b
    Dmax = d_hi - base
    print(f"### N={N} (n,k)=({n},{k})  lo=2^{N-1}  Dmax={Dmax}  sqrt(lo)={isqrt(lo)}")

    # (I) identity: T=1 set (via d_terms) == reciprocal-floor fixed points
    A1_enum = [D for D in range(1, Dmax + 1) if d_terms(base + D, N, n, k) == 1]
    A1_pred = recip_fixed(lo, Dmax)
    print(f"(I)  |A1 via d_terms|={len(A1_enum)}   |A1 via lo//(lo//D)|={len(A1_pred)}   "
          f"IDENTICAL={A1_enum == A1_pred}")

    # (II)/(III) island structure vs sqrt(lo)
    s = isqrt(lo)
    comps = components_of(A1_pred)
    above = [v for v in A1_pred if v > s]
    below = [v for v in A1_pred if v <= s]
    # how many of the 'above sqrt' points are isolated singletons?
    aset = set(A1_pred)
    singletons_above = sum(1 for v in above if (v - 1) not in aset and (v + 1) not in aset)
    below_contig = components_of(below)
    print(f"(III) #components(A1)={comps};  points >sqrt(lo): {len(above)} "
          f"({singletons_above} isolated singletons);  points <=sqrt(lo): {len(below)} "
          f"in {below_contig} run(s)")
    print(f"      => islands above sqrt(lo), (near-)contiguous block below.  "
          f"comps ~ singletons_above + below_runs = {singletons_above}+{below_contig}")

    # (IV) 2-adic vs Dirichlet: matched non-power-of-2 L of same magnitude
    from sympy import nextprime
    L2 = lo                      # 2^(N-1)
    Lp = nextprime(lo + (lo // 3))   # an odd, non-2-adic L of the same bit-size
    for label, L in [("L=2^(N-1)", L2), ("L=odd prime ~1.33*lo", Lp)]:
        vals = recip_fixed(L, Dmax)
        s2 = isqrt(L)
        ab = sum(1 for v in vals if v > s2)
        print(f"(IV) {label:24s}: |A1|={len(vals):6d}  #components={components_of(vals):6d}  "
              f"#above_sqrt(islands)={ab:6d}")
    print("     -> if the two rows match in shape, the law is DIRICHLET (generic in L), NOT 2-adic.")


if __name__ == "__main__":
    main()
