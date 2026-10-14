#!/usr/bin/env python3
"""PRIMARY SLOT MISS (Lemma 5.2 of lrc_n11_ap_paper_v30.md) instantiated at n = 8.

The n=11 engine, verbatim structure, with 11 -> n:
  chain      B_{j,k}(a_j) = [ (n k + n-1)/(n a_j), (n k + n+1)/(n a_j) ]
  slots      I_s = [ (n s + 1)/(n(n-1)), (n s + n-1)/(n(n-1)) ],  s = 1..n-2
  window     W_ref = [1/(n a_1), (n-1)/(n a_1)]
  sign range a_j in (j-1, j+1)                              (Lemma 5.1)
PSM asks: if runner j covers the far endpoint g of the UNCLAIMED slot, which k are feasible
given a_j in (j-1,j+1); the feasible k pins a_j to a narrow range; over that range B_{j,0}
lies entirely outside some OTHER slot, forcing GF > 0 there.

Nothing here uses primality of n.  Exact Fraction arithmetic; no float anywhere.
Reference check: run with n=11 and it must reproduce the paper's Lemma 5.2 --
runner 3 -> a_3 <= 230/109 and misses I_3; runner 4 -> I_2; runner 5 -> I_1.
"""
import sys
from fractions import Fraction as F

def slots(n):  return {s: (F(n*s+1, n*(n-1)), F(n*s+n-1, n*(n-1))) for s in range(1, n-1)}
def Bk(k, a, n): return (F(n*k+n-1, n)/a, F(n*k+n+1, n)/a)

def psm(n, verbose=True):
    S = slots(n)
    g = S[n-2][1]                      # far (right) endpoint of the last slot = unclaimed one
    out = []
    for j in range(2, n-1):            # free runners
        lo, hi = F(j-1), F(j+1)
        for k in range(0, 3*n):
            # B_{j,k} covers g  <=>  (nk+n-1)/(n a) <= g <= (nk+n+1)/(n a)
            amin, amax = F(n*k+n-1, n)/g, F(n*k+n+1, n)/g
            l, h = max(lo, amin), min(hi, amax)
            if l >= h: continue
            # over a in [l,h], B_{j,0} = [(n-1)/(n a), (n+1)/(n a)] is widest at a=l
            b0l_max, b0r_min = F(n-1, n)/l, F(n+1, n)/h      # extreme positions
            b0l_min, b0r_max = F(n-1, n)/h, F(n+1, n)/l
            for s, (sl, sr) in S.items():
                if b0l_min > sr:   out.append((j, k, l, h, s, "right of", b0l_min, sr))
                elif b0r_max < sl: out.append((j, k, l, h, s, "left of",  b0r_max, sl))
    if verbose:
        print(f"n = {n}.  unclaimed-slot far endpoint g = {g}")
        print(f"free runners 2..{n-2}, sign range a_j in (j-1, j+1), slots I_1..I_{n-2}")
        seen = set()
        for j, k, l, h, s, side, val, bnd in out:
            key = (j, s)
            tag = "" if key in seen else "  <== FORCED MISS"
            seen.add(key)
            print(f"  runner {j}: B_(j,{k}) covers g  =>  a_{j} in [{l}, {h}]"
                  f"   then B_(j,0) lies {side} I_{s}  ({val} vs {bnd}){tag}")
    return out

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    psm(n)
